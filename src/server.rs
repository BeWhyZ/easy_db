use crate::raft;

use crossbeam::channel::{Receiver, Sender};
use std::collections::HashMap;
use std::net::{TcpListener, TcpStream, ToSocketAddrs};
use log::{debug, error, info};


pub struct Server {
    node: raft::Node,

    node_rx: Receiver<raft::Envelope>,

    peers: HashMap<raft::NodeID, String>,
}

impl Server {
    pub fn new(
        id: raft::NodeID, 
        peers: HashMap<raft::NodeID, String>,
        raft_log: raft::Log,
        raft_state: Box<dyn raft::State>,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let (node_tx, node_rx) = crossbeam::channel::unbounded();
        let node = raft::Node::new(
            id, peers.keys().copied().collect(), raft_log, 
            raft_state, node_tx,
            raft::Options::default(),
        )?;

        Ok(Self {
            node,
            node_rx,
            peers,
        })
        
    }

    /// Serves Raft and SQL requests indefinitely. Consumes the server.
    pub fn serve(self, raft_addr: impl ToSocketAddrs, sql_addr: impl ToSocketAddrs) -> Result<()>{
        let raft_listener = TcpListener::bind(raft_addr)?;
        let sql_listener = TcpListener::bind(sql_addr)?;
        info!(
            "Listening on {} (SQL) and {} (Raft)",
            sql_listener.local_addr()?,
            raft_listener.local_addr()?
        );

        std::thread::scope(move |s| {
            let id = self.node.id();
            let (raft_request_tx, raft_request_rx) = crossbeam::channel::unbounded();
            let (raft_step_tx, raft_step_rx) = crossbeam::channel::unbounded();

            // Serve inbound Raft connections.
            // Establish outbound Raft connections to peers.
            // Route Raft messages between the local node, peers, and clients.
            // Serve inbound SQL connections.
        });

        Ok(())

    }

    fn raft_accept(listener: TcpListener, raft_step_tx: Sender<raft::Envelope>) {
        todo!();
    }



}

