use crate::raft;
use crate::error::Result;
use crate::sql;

use crossbeam::channel::{Receiver, Sender};
use std::collections::HashMap;
use std::net::{TcpListener, TcpStream, ToSocketAddrs};
use log::{debug, error, info};


const RAFT_PEER_CHANNEL_CAPACITY: u16 = 1000;


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
    ) -> Result<Self> {
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
            s.spawn(move || Self::raft_accept(raft_listener, raft_step_tx));
            // Establish outbound Raft connections to peers.
            let mut raft_peers_tx = HashMap::new();
            for (id, addr) in self.peers.into_iter() {
                let (raft_peer_tx, raft_peer_rx) = crossbeam::channel::bounded(RAFT_PEER_CHANNEL_CAPACITY);
                raft_peers_tx.insert(id, raft_peer_tx);
                s.spawn(move || Self::raft_send_peer(addr, raft_peer_rx));
            }
            // Route Raft messages between the local node, peers, and clients.
            s.spawn(move || Self::raft_route(
                self.node,
                self.node_rx,
                raft_step_rx,
                raft_peers_tx,
                raft_request_rx,
            ));
            // Serve inbound SQL connections.
            let sql_engine = sql::engine::Raft::new(raft_request_tx);
            s.spawn(move || Self::sql_accept(self.node.id(), sql_listener, sql_engine));
        });

        Ok(())

    }

    /// Accepts new inbound Raft connections from peers and spawns threads
    /// routing inbound messages to the local Raft node.
    fn raft_accept(listener: TcpListener, raft_step_tx: Sender<raft::Envelope>) {
        todo!();
    }

    /// Sends outbound messages to a peer via TCP. Retries indefinitely if the
    /// connection fails.
    fn raft_send_peer(addr: String, raft_peer_rx: Receiver<raft::Envelope>) {
        todo!();
    }

    /// Routes Raft messages:
    ///
    /// * node_rx: outbound messages from the local Raft node. Routed to peers
    ///   via TCP, or to local clients via a response channel.
    ///
    /// * request_rx: inbound requests from local SQL clients. Stepped into
    ///   the local Raft node as ClientRequest messages. Responses are returned
    ///   via the provided response channel.
    ///
    /// * peers_rx: inbound messages from remote Raft peers. Stepped into the
    ///   local Raft node.
    ///
    /// * peers_tx: outbound per-peer channels sent via TCP connections.
    ///   Messages from the local node's node_rx are sent here.
    ///
    /// Panics on any errors, since the Raft node can't recover from failed
    /// state transitions.
    fn raft_route(
        mut node: raft::Node,
        node_rx: Receiver<raft::Envelope>,
        peers_rx: Receiver<raft::Envelope>,
        mut peers_tx: HashMap<raft::NodeID, Sender<raft::Envelope>>,
        request_tx: Receiver<(raft::Request, Sender<Result<raft::Response>>)>,
    ) {
        todo!();
    }

    /// Accepts new SQL client connections and spawns session threads for them.
    fn sql_accept(id: raft::NodeID, listener: TcpListener, sql_engine: sql::engine::Raft) {
        todo!();
    }


}

