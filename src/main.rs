// Author: Alexander M. Pellegrino
// Date: November 2, 2024
// License: CC BY-NC 4.0

use rand::rngs::OsRng;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc};
use std::thread;
use std::time::Duration;
use dashmap::DashMap;
use fips203::ml_kem_1024;
use fips203::traits::SerDes as SerDesKyber;
use fips204::ml_dsa_87;
use fips204::traits::Verifier;
use fips204::traits::SerDes as SerDesDilithium;
use rand::RngCore;
use zeroize::Zeroize;

// Fixed port for server.
const PORT: &str = "57813";

// The number of bytes involved in challenge nonces.
const NONCE_SIZE: usize = 256;

// Standard delimiters.
const TRANSMISSION_DELIMITER: &str = ":::";

// The signature context. All signatures from this application should have it.
const SIGNATURE_CONTEXT: &[u8] = b"\xCE\xB1";

// The messages peers and the server should transmit.
const AUTHENTICATION_REQUEST: &str = "Friend requesting access.";
const SESSION_REQUEST: &str = "もうすぐ私に会えますよ";
const ISSUED_CHALLENGE: &str = "Welcome Anon. Here's your challenge:";
const VERIFIED_PEER: &str = "You're in.";
const MALICIOUS_PEER: &str = "You are not authorized to be here, your connection will be terminated.\nEND OF LINE";
const PEER_KEYS_RECEIVED: &str = "I see you have constructed a new lightsaber.";
const PEER_CONNECTION_REQUEST: &str = "We Shall Sail Together.";

// The HTTP response for browser clients.
const BROWSER_RESPONSE: &str =
    "HTTP/1.1 200 OK\r\n\
    Content-Type: text/html\r\n\
    \r\n\
    <html><body>Hello. It appears you're trying to connect via \
    a browser. However, this server is an endpoint for P2P messaging, \
    and will not work with normal browsers.</body></html>\r\n";

fn main() {

    // Since the server spawns new threads to handle each incoming client,
    // we need thread-safe references to our global peer pool. To do this,
    // we'll make use of Mutex to prevent data races and Arc to allow
    // thread-safe references to the mutex while preserving lifetimes.

    // Keys - Kyber Public Keys
    // Values - Tuple (Dilithium Public Key, Stream)
    let global_peer_pool: Arc<DashMap<String, (String, TcpStream)>> = Arc::new(DashMap::new());

    let cleanup_pool = Arc::clone(&global_peer_pool);

    // Spawn cleanup thread
    thread::spawn(move || {
        loop {
            thread::sleep(Duration::from_secs(60));  // Adjust interval as needed
            cleanup_peer_pool(&cleanup_pool);
        }
    });

    // Listen for incoming connections on fixed port. Allow any IP to connect.
    let listener = TcpListener::bind(format!("0.0.0.0:{}", PORT)).expect("Unable to bind to port.");

    println!("Server listening on port {}", PORT);

    // Handle all incoming connections.
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => handle_client(stream, &global_peer_pool),
            Err(e) => eprintln!("Connection failed: {}", e),
        }
    }

}

// Function to check for common HTTP headers added by browsers to detect
// users attempting to connect via a browser rather than the peer client.
fn is_browser_connection(request: &str) -> bool {
    request.contains("HTTP/1.1") || request.contains("Host:") || request.contains("User-Agent:")
}

// Function to handle all incoming connections and filter out peers.
fn handle_client(mut stream: TcpStream, global_peer_pool: &Arc<DashMap<String, (String, TcpStream)>>) {

    let peer_pool = Arc::clone(global_peer_pool);

    // Each client lives in its own thread - they shouldn't be talking to one another yet.
    thread::spawn(move || {

        // Read incoming transmissions from clients.
        let mut request = read_from_stream(&mut stream);

        // Client is a web browser.
        if is_browser_connection(&request) {
            if let Err(e) = write_message(&mut stream, BROWSER_RESPONSE.as_bytes()) {
                eprintln!("Failed to write to stream: {}", e);
            }
        }

        else if request.contains(AUTHENTICATION_REQUEST) {
            handle_peer(stream, &peer_pool);
        }

        else if request.contains(SESSION_REQUEST) {
            handle_session(stream, &request, &peer_pool);
        }

        // Securely Zero request from memory in case it contains any sensitive data.
        request.zeroize();
    });
}

// Function to handle incoming peers.
fn handle_peer(mut stream: TcpStream, peer_pool: &Arc<DashMap<String, (String, TcpStream)>>) {

    // Generate a hex-encoded challenge for the peer to sign.
    let challenge_nonce = hex::encode(generate_nonce(NONCE_SIZE));

    // Send the challenge to the peer.
    let challenge = format!("{}\n{}", ISSUED_CHALLENGE, challenge_nonce);
    println!("{}", challenge);

    if let Err(e) = write_message(&mut stream, challenge.as_bytes()) {
        eprintln!("Error welcoming peer: {}", e);
    };

    // Read the peer's response.
    let request = read_from_stream(&mut stream);

    let fragments: Vec<&str> = request.split(TRANSMISSION_DELIMITER).collect();

    // Check if the peer signed the nonce successfully. Format:

    /*
     *   The peer's public key.
     *   Our nonce. (Should be returned unmodified.)
     *   The nonce signature. (Should be verifiable with the public key.)
     */
    if fragments.len() != 3 {
        println!("Invalid header from peer.");
        return;
    }

    let serial_peer_public_key = fragments[0];
    let serial_nonce = fragments[1];
    let serial_signature = fragments[2];

    // Confirm that after splitting both fragments exist and the hex-encoded
    // nonce that the peer sent back matches the nonce that we sent to them.
    if serial_nonce == challenge_nonce {

        // Attempt to reconstruct a public key from received hexcode.
        let peer_public_key = deserialize_dilithium_key(serial_peer_public_key);

        // Attempt to verify peer using nonce, pubkey, and signature.
        if verify_dilithium_signature(&peer_public_key,
                                      hex::decode(challenge_nonce).expect("Invalid nonce received."),
                                      deserialize_dilithium_signature(serial_signature)
        ) {

            // Peer has verified ownership of the Dilithium key. Reply.
            if let Err(e) = write_message(&mut stream, VERIFIED_PEER.as_bytes()) {
                eprintln!("Error sending peer verification: {}", e);
            };

            println!("Peer Authenticated.");

            // A compliant peer should now attempt to link their Dilithium and Kyber keys.
            // This should be done by sending us:

            /*
             *   The same Dilithium key.
             *   Their public Kyber key.
             *   Their Kyber key signed using the Dilithium key.
             */

            // We will compare the Dilithium keys to attempt to flag interference,
            // then use the original key, not the new one, to verify the signature.
            let mut peer_keys = read_from_stream(&mut stream);

            let peer_key_set: Vec<&str> = peer_keys.split(TRANSMISSION_DELIMITER).collect();

            if peer_key_set.len() != 3 {
                println!("Invalid data from peer.");
                return;
            }

            let public_key_confirmation = peer_key_set[0];
            let serial_kyber_public_key = peer_key_set[1];
            let serial_kyber_key_signature = peer_key_set[2];

            // Attempt to match Dilithium keys.
            if public_key_confirmation == serial_peer_public_key {

                // Attempt to verify the kyber key was signed with the correct Dilithium key.
                if verify_dilithium_signature(&peer_public_key,
                                              Vec::from(deserialize_kyber_key(serial_kyber_public_key).into_bytes()),
                                              deserialize_dilithium_signature(serial_kyber_key_signature)
                ) {

                    // Success. Inform the peer that we received their keys and will
                    // add them to the pool. They are cleared to proceed to exchange.
                    if let Err(e) = write_message(&mut stream, PEER_KEYS_RECEIVED.as_bytes()) {
                        eprintln!("Error sending information to peer: {}", e);
                    };

                    // Add the peer to the pool in a thread-safe manner.
                    peer_pool
                        .insert(serial_kyber_public_key.to_string(),
                                (
                                    serial_peer_public_key.to_string(),

                                    stream,
                                )
                        );

                    println!("Peer verified.");
                }

                else {
                    println!("Peer failed verification.");
                }
            }

            // The Dilithium key on this connection has changed.
            else {
                if write_message(&mut stream, MALICIOUS_PEER.as_bytes()).is_err() {
                    eprintln!("Corrupted or intercepted feed detected. Terminating.");
                }

                println!("Peer rejected.");
            }

            // Securely Zero sensitive values in memory before drop.
            peer_keys.zeroize();
        }

        // The nonce was signed incorrectly.
        else {
            if let Err(e) = write_message(&mut stream, MALICIOUS_PEER.as_bytes()) {
                eprintln!("Error warning unwelcome peer: {}", e);
            };

            println!("Peer rejected.");
        }
    }

    // The nonce was modified or damaged in transit.
    else {
        if let Err(e) = write_message(&mut stream, b"Invalid signature returned.") {
            eprintln!("Error responding to peer: {}", e);
        };

        println!("Invalid signature.");
    }
    
}

// Function to handle session initiation.
fn handle_session(mut stream: TcpStream, session_data: &str, peer_pool: &Arc<DashMap<String, (String, TcpStream)>>) {

    // Read connection request from peer. Should be:

    /*
     *   Session Request Header
     *   Public Kyber Key
     *   Peer ID to Connect With
     *   Peer ID to Connect With, Signed with the Requester's Dilithium Key
     *   The Requester's listening port, encrypted with the Peer's Public Kyber Key
     *   The ciphertext to establish the shared secret.
     */
    let data_fragments: Vec<&str> = session_data.split(TRANSMISSION_DELIMITER).collect();

    if data_fragments.len() != 6 {
        if write_message(&mut stream, b"Missing connection request fragments.").is_err() {
            eprintln!("Peer missing connection request pieces.");
        }
        return;
    }

    let kyber_key = data_fragments[1];
    let target_peer = data_fragments[2];
    let target_signature = data_fragments[3];
    let encrypted_port = data_fragments[4];
    let ciphertext = data_fragments[5];

    // No else clauses to return failure state here - the below
    // operations are intentionally invisible for user privacy.
    let pool_search = peer_pool.get(kyber_key);

    let (serial_dilithium_public_key, _) = match pool_search {
        Some(ref v) => v.value(),
        None => { return; }
    };
    

    // Confirm that this is an authentic connection request.
    if verify_dilithium_signature(&deserialize_dilithium_key(serial_dilithium_public_key),
                                  Vec::from(deserialize_kyber_key(target_peer).into_bytes()),
                                  deserialize_dilithium_signature(target_signature)
    ) {
        // It is. If the listening peer exists, send them the signal. Our job is done.
        if peer_pool.contains_key(target_peer) {
            
            // Search the pool for our target peer. They should be listening.
            let mut target_search = peer_pool.get_mut(target_peer);
            
            let (_, target_socket) = match target_search {
                Some(ref mut v) => v.value_mut(),
                None => { return; }
            };

            // Send the connection request to the target peer. Format:
            
            /*
             *   Connection request header.
             *   The sender's public Kyber key.
             *   The sender's listening port, encrypted using the target's public key.
             */
            if let Err(e) = write_message(target_socket,
                                                            format!("{}{}{}{}{}{}{}{}{}",
                                                            PEER_CONNECTION_REQUEST,
                                                            TRANSMISSION_DELIMITER,
                                                            kyber_key,
                                                            TRANSMISSION_DELIMITER,
                                                            stream.peer_addr().unwrap().ip(),
                                                            TRANSMISSION_DELIMITER,
                                                            encrypted_port,
                                                            TRANSMISSION_DELIMITER,
                                                            ciphertext
            ).as_bytes()) {
                eprintln!("Transmission failed: {}", e);
            }
        }

        // No else - the server will not inform the sender if the target does not exist.
    }
    
    else {
        println!("Signature verification failed - Bad connection request.");
    }

    
}

// Generates a secure nonce for peer authentication.
fn generate_nonce(size: usize) -> Vec<u8> {
    let mut nonce = vec![0; size];
    OsRng.try_fill_bytes(&mut nonce).expect("Unable to generate secure nonce.");
    nonce
}

// Function to transmit data with length prefixed.
fn write_message(stream: &mut TcpStream, data: &[u8]) -> std::io::Result<()> {
    let len = data.len() as u32;
    stream.write_all(&len.to_be_bytes())?;
    stream.write_all(data)?;
    Ok(())
}

// Function to safely read from streams - BLOCKING!
fn read_from_stream(stream: &mut TcpStream) -> String {
    let mut len_bytes = [0u8; 4];

    match stream.read_exact(&mut len_bytes) {
        Ok(_) => {
            let len = u32::from_be_bytes(len_bytes) as usize;
            let mut buffer = vec![0; len];

            match stream.read_exact(&mut buffer) {
                Ok(_) => {
                    let result = String::from_utf8(buffer);

                    if let Ok(safe_result) = result {
                        safe_result
                    } else {
                        String::from("Invalid Data in the Stream.")
                    }
                },
                Err(e) => {
                    if let Err(e2) = write_message(stream, format!("Unknown server error: {}", e).as_bytes()) {
                        eprintln!("Unknown server error: {}", e2);
                    };
                    format!("Failed to read from stream: {}", e)
                }
            }
        },
        Err(e) => {
            if let Err(e2) = write_message(stream, format!("Unknown server error: {}", e).as_bytes()) {
                eprintln!("Unknown server error: {}", e2);
            };
            format!("Failed to read from stream: {}", e)
        }
    }
}

// Function to check if a stream is still alive - used to clean up disconnected peers
fn is_stream_alive(stream: &TcpStream) -> bool {
    let mut buf = [0; 1];
    match stream.peek(&mut buf) {
        Ok(0) | Err(_) => false,  // Connection closed or error
        Ok(_) => true,  // Data available or would block
    }
}

// Function to clean up dead connections from the peer pool
fn cleanup_peer_pool(peer_pool: &Arc<DashMap<String, (String, TcpStream)>>) {
    let mut to_remove = Vec::new();

    // First pass - collect keys to remove
    for entry in peer_pool.iter() {
        let (_, stream) = entry.value();
        if !is_stream_alive(stream) {
            to_remove.push(entry.key().clone());
        }
    }

    // Second pass - remove dead connections
    for key in to_remove {
        peer_pool.remove(&key);
    }
}

// Reads a hex-encoded Dilithium public key. Will not
// and should not work for private keys - these should
// never be going out over the network, or we have issues.
fn deserialize_dilithium_key(serial_key: &str) -> ml_dsa_87::PublicKey {
    ml_dsa_87::PublicKey::try_from_bytes(
        <[u8; 2592]>::try_from(
            hex::decode(serial_key).
                expect("Unable to decode public key.")
        ).expect("Unable to extract public key bytes.")
    ).expect("Invalid public key.")
}

// Deserializes a signature generated with a Dilithium Private Key for transmission.
fn deserialize_dilithium_signature(signature: &str) -> Vec<u8> {
    hex::decode(signature)
        .expect("Invalid signature hex.")
}

// Verifies a message using a Dilithium Public Key.
fn verify_dilithium_signature(key: &ml_dsa_87::PublicKey, mut message: Vec<u8>, mut signature: Vec<u8>) -> bool {
    let result = key.verify(message.as_slice(),
               signature.as_slice().try_into().expect("Invalid Signature Format"),
               SIGNATURE_CONTEXT);

    message.zeroize();
    signature.zeroize();
    
    result
}

// Reads a hex-encoded Kyber public key. Will not
// and should not work for private keys - these should
// never be going out over the network, or we have issues.
fn deserialize_kyber_key(serial_key: &str) -> ml_kem_1024::EncapsKey {
    ml_kem_1024::EncapsKey::try_from_bytes(
        <[u8; 1568]>::try_from(
            hex::decode(serial_key).
                expect("Unable to decode public key.")
        ).expect("Unable to extract public key bytes.")
    ).expect("Invalid public key.")
}