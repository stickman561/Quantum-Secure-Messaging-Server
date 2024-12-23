# Server Application

Just throwing together a quick README for now, will likely improve later. This repository contains the source code for a peer-to-peer relay server, 
designed to relay connections for a specific client application (which can be found at https://github.com/stickman561/Quantum-Secure-Messaging-Client).
It's built entirely in safe Rust and uses Quantum-Secure signing, key encapsulation, and encryption in order to provide a hopefully future-safe messaging
experience. This server requires an open port on the firewall in order to bind to, currently hardcoded as port 57813. It can handle connections and
exchanges from multiple clients simultaneously.
