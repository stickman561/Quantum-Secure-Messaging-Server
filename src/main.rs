// Author: Alexander M. Pellegrino
// Date: November 2, 2024
// License: CC BY-NC 4.0

use rand::rngs::StdRng;
use std::io::{stdin, stdout, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};
use dashmap::DashMap;
use fips203::ml_kem_1024;
use fips203::traits::SerDes as SerDesKyber;
use fips204::ml_dsa_87;
use fips204::traits::Verifier;
use fips204::traits::SerDes as SerDesDilithium;
use rand::{RngCore, SeedableRng};
use secrecy::{ExposeSecret, SecretSlice, SecretString};
use subtle_encoding::hex;

// Fixed port for server.
const DEFAULT_PORT: &str = "57813";

// The number of bytes involved in challenge nonces.
const NONCE_SIZE: usize = 256;

// Standard delimiters.
const TRANSMISSION_DELIMITER: &str = ":::";

// The signature context. All signatures from this application should have it.
const SIGNATURE_CONTEXT: &[u8] = b"\xCE\xB1";

// The messages peers and the server should transmit.
const AUTHENTICATION_REQUEST: &str = "Friend requesting access.";
const SESSION_REQUEST: &str = "もうすぐ私に会えますよ"; // 山村貞子、『リング』 - Sadako Yamamura/Samara Morgan, The Ring (Remake, 2002)
const ISSUED_CHALLENGE: &str = "Welcome, Anon. Here's your challenge:";
const VERIFIED_PEER: &str = "You're in.";
const MALICIOUS_PEER: &str = "You are not authorized to be here, your connection will be terminated.\nEND OF LINE";
const PEER_KEYS_RECEIVED: &str = "I see you have constructed a new lightsaber."; // Darth Vader, Star Wars (Return of the Jedi, 1983)
const PEER_CONNECTION_REQUEST: &str = "We Shall Sail Together."; // Sea of Thieves (Rare Games, 2018)
const HEARTBEAT_PROMPT: &str = "Are you still there?"; // Turret, Portal (Valve, 2007)
const HEARTBEAT_RESPONSE: &str = "There you are."; // Turret, Portal (Valve, 2007)

type PeerKyberKey = String;
type PeerDilithiumKey = String;
type PeerConnection = TcpStream;
type PeerData = (PeerDilithiumKey, PeerConnection, Instant);
type PeerMap = Arc<DashMap<PeerKyberKey, PeerData>>;

fn main() {

    // Since the server spawns new threads to handle each incoming client,
    // we need thread-safe references to our global peer pool. To do this,
    // we'll make use of Mutex to prevent data races and Arc to allow
    // thread-safe references to the mutex while preserving lifetimes.

    // Keys - Kyber Public Keys
    // Values - Tuple (Dilithium Public Key, Stream, Last Connection Request Time)

    let global_peer_pool: PeerMap = Arc::new(DashMap::new());

    let cleanup_pool = Arc::clone(&global_peer_pool);

    // Spawn cleanup thread
    thread::spawn(move || {
        loop {
            thread::sleep(Duration::from_secs(300));  // Adjust interval as needed
            cleanup_peer_pool(&cleanup_pool);
        }
    });

    // Prompt host to enter a port.
    let mut port = String::new();
    println!("Enter listening port. (Hit Enter to use default port.)");
    stdout().flush().unwrap();

    stdin().read_line(&mut port).unwrap();

    if port.trim().is_empty() {
        port = String::from(DEFAULT_PORT);
    }

    else {
        port = port.trim().to_string();
    }

    // Listen for incoming connections on fixed port. Allow any IP to connect.
    let listener = TcpListener::bind(format!("0.0.0.0:{port}")).expect("Unable to bind to port.");

    println!("Server listening on port {port}");

    // Handle all incoming connections.
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => handle_client(stream, &global_peer_pool),
            Err(e) => eprintln!("Connection failed: {e}"),
        }
    }

}

// Function to handle all incoming connections and filter out peers.
fn handle_client(mut stream: TcpStream, global_peer_pool: &PeerMap) {

    let peer_pool = Arc::clone(global_peer_pool);

    // Each client lives in its own thread - they shouldn't be talking to one another yet.
    thread::spawn(move || {

        // Read incoming transmissions from clients.
        let request = read_from_stream(&mut stream);

        if request.expose_secret().contains(AUTHENTICATION_REQUEST) {
            handle_peer(stream, &peer_pool);
        }

        else if request.expose_secret().contains(SESSION_REQUEST) {
            handle_session(stream, &request, &peer_pool);
        }
    });
}

// Function to handle incoming peers.
fn handle_peer(mut stream: TcpStream, peer_pool: &PeerMap) {

    // Generate a hex-encoded challenge for the peer to sign.
    let challenge_nonce = String::from_utf8(hex::encode(generate_nonce(NONCE_SIZE).expose_secret())).unwrap();

    // Send the challenge to the peer.
    let challenge = format!("{ISSUED_CHALLENGE}\n{challenge_nonce}");
    println!("{challenge}");

    if let Err(e) = write_message(&mut stream, challenge.as_bytes()) {
        eprintln!("Error welcoming peer: {e}");
    }

    // Read the peer's response.
    let request = read_from_stream(&mut stream);

    let fragments: Vec<&str> = request.expose_secret().split(TRANSMISSION_DELIMITER).collect();

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
                                      &SecretSlice::from(hex::decode(challenge_nonce).expect("Invalid nonce received.")),
                                      &deserialize_dilithium_signature(serial_signature)
        ) {

            // Peer has verified ownership of the Dilithium key. Reply.
            if let Err(e) = write_message(&mut stream, VERIFIED_PEER.as_bytes()) {
                eprintln!("Error sending peer verification: {e}");
            }

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
            let peer_keys = read_from_stream(&mut stream);

            let peer_key_set: Vec<&str> = peer_keys.expose_secret().split(TRANSMISSION_DELIMITER).collect();

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
                                              &SecretSlice::from(Vec::from(deserialize_kyber_key(serial_kyber_public_key).into_bytes())),
                                              &deserialize_dilithium_signature(serial_kyber_key_signature)
                ) {

                    // Success. Inform the peer that we received their keys and will
                    // add them to the pool. They are cleared to proceed to exchange.
                    if let Err(e) = write_message(&mut stream, PEER_KEYS_RECEIVED.as_bytes()) {
                        eprintln!("Error sending information to peer: {e}");
                    }

                    // Add the peer to the pool in a thread-safe manner.
                    peer_pool
                        .insert(serial_kyber_public_key.to_string(),
                                (
                                    serial_peer_public_key.to_string(),
                                    stream,
                                    Instant::now()
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
        }

        // The nonce was signed incorrectly.
        else {
            if let Err(e) = write_message(&mut stream, MALICIOUS_PEER.as_bytes()) {
                eprintln!("Error warning unwelcome peer: {e}");
            }

            println!("Peer rejected.");
        }
    }

    // The nonce was modified or damaged in transit.
    else {
        if let Err(e) = write_message(&mut stream, b"Invalid signature returned.") {
            eprintln!("Error responding to peer: {e}");
        }

        println!("Invalid signature.");
    }

}

// Function to handle session initiation.
fn handle_session(mut stream: TcpStream, session_data: &SecretString, peer_pool: &PeerMap) {

    // Read connection request from peer. Should be:

    /*
     *   Session Request Header
     *   Public Kyber Key
     *   Peer ID to Connect With
     *   Peer ID to Connect With, Signed with the Requester's Dilithium Key
     *   The Requester's listening port, encrypted with the Peer's Public Kyber Key
     *   The ciphertext to establish the shared secret.
     */
    let data_fragments: Vec<&str> = session_data.expose_secret().split(TRANSMISSION_DELIMITER).collect();

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

    let (serial_dilithium_public_key, _, _) = match pool_search {
        Some(ref v) => v.value(),
        None => { return; }
    };


    // Confirm that this is an authentic connection request.
    if verify_dilithium_signature(&deserialize_dilithium_key(serial_dilithium_public_key),
                                  &SecretSlice::from(Vec::from(deserialize_kyber_key(target_peer).into_bytes())),
                                  &deserialize_dilithium_signature(target_signature)
    ) {
        // It is. If the listening peer exists, send them the signal. Our job is done.
        if peer_pool.contains_key(target_peer) {

            // Search the pool for our target peer. They should be listening.
            let mut target_search = peer_pool.get_mut(target_peer);

            let (_, target_socket, last_request) = match target_search {
                Some(ref mut v) => v.value_mut(),
                None => { return; }
            };

            // Avoid requests from last 60 seconds.
            if last_request.elapsed() < Duration::from_secs(60) {
                return;
            }

            *last_request = Instant::now();

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
                eprintln!("Transmission failed: {e}");
            }
        }

        // No else - the server will not inform the sender if the target does not exist.
    }

    else {
        println!("Signature verification failed - Bad connection request.");
    }


}

// Generates a secure nonce for peer authentication.
fn generate_nonce(size: usize) -> SecretSlice<u8> {
    let mut nonce = vec![0; size];
    StdRng::from_os_rng().fill_bytes(&mut nonce);
    SecretSlice::from(nonce)
}

// Function to transmit data with length prefixed.
fn write_message(stream: &mut TcpStream, data: &[u8]) -> std::io::Result<()> {
    if data.is_empty() {
        return Ok(());
    }

    let len = u32::try_from(data.len())
        .map_err(|_| std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "Invalid data packet."
        ))?;

    stream.write_all(&len.to_be_bytes())?;
    stream.write_all(data)?;
    Ok(())
}

// Function to safely read from streams - BLOCKING!
fn read_from_stream(stream: &mut TcpStream) -> SecretString {

    let mut len_bytes = [0u8; 4];

    match stream.read_exact(&mut len_bytes) {
        Ok(()) => {
            let len = u32::from_be_bytes(len_bytes) as usize;
            let mut buffer = vec![0; len];

            match stream.read_exact(&mut buffer) {
                Ok(()) => {
                    let result = String::from_utf8(buffer);

                    if let Ok(safe_result) = result {
                        SecretString::from(safe_result)
                    }

                    else {
                        SecretString::from("Invalid Data in the Stream.")
                    }
                },
                Err(e) => {
                    if let Err(e2) = write_message(stream, format!("Unknown server error: {e}").as_bytes()) {
                        eprintln!("Unknown server error: {e2}");
                    }
                    SecretString::from(format!("Failed to read from stream: {e}"))
                }
            }
        },

        Err(e) => {
            if let Err(e2) = write_message(stream, format!("Unknown server error: {e}").as_bytes()) {
                eprintln!("Unknown server error: {e2}");
            }
            SecretString::from(format!("Failed to read from stream: {e}"))
        }
    }
}

// Function to check if a stream is still alive - used to clean up disconnected peers
fn is_stream_alive(stream: &mut TcpStream) -> bool {

    // Send heartbeat prompt
    if write_message(stream, HEARTBEAT_PROMPT.as_bytes()).is_err() {
        return false;
    }

    // Wait for response with a timeout
    stream.set_read_timeout(Some(Duration::from_secs(5))).unwrap_or(());

    read_from_stream(stream).expose_secret() == HEARTBEAT_RESPONSE
}

// Function to clean up dead connections from the peer pool
fn cleanup_peer_pool(peer_pool: &PeerMap) {
    println!("Cleaning up peer pool. Sending heartbeat signals...");

    let to_remove = Arc::new(Mutex::new(Vec::new()));

    peer_pool.iter()
        .map(|entry| {
            let key = entry.key().clone();
            let test_stream = entry.value().1.try_clone();

            let local_handle = Arc::clone(&to_remove);

            thread::spawn(move || {
                if test_stream.is_err() || !is_stream_alive(&mut test_stream.unwrap()) {
                    local_handle.lock().unwrap().push(key);
                }
            })
        })
        .for_each(|task| task.join().unwrap());

    let dead_peer_count = to_remove.lock().unwrap().len();

    // Second pass - remove dead connections
    to_remove.lock().unwrap().iter().for_each(|key| {
        if let Some(peer) = peer_pool.get(key) {
            if peer.value().2.elapsed() > Duration::from_secs(300) {
                peer_pool.remove(key);
            }
        }

        else {
            peer_pool.remove(key);
        }
    });

    if dead_peer_count > 0 {
        if dead_peer_count == 1 {
            println!("Cleaned up 1 disconnected peer. さむらいがひとりたつ");
        }

        else {
            println!("Cleaned up {dead_peer_count} disconnected peers. さよなら、友達");
        }
    }

    else {
        println!("No inactive peers found.");
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
fn deserialize_dilithium_signature(signature: &str) -> SecretSlice<u8> {
    SecretSlice::from(hex::decode(signature).expect("Invalid signature hex."))
}

// Verifies a message using a Dilithium Public Key.
fn verify_dilithium_signature(key: &ml_dsa_87::PublicKey, message: &SecretSlice<u8>, signature: &SecretSlice<u8>) -> bool {
    key.verify(message.expose_secret(),
               signature.expose_secret().try_into().expect("Invalid Signature Format"),
               SIGNATURE_CONTEXT
    )
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