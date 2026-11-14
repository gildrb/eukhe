//! Whom a client accepts as the listener of an abstract endpoint
//! (`bend/server_peer.bend`, entry `bend/ffi_server_peer.bend`;
//! `laws/server_peer.bend`): the listener runs as the client's uid and is
//! the process recorded for the endpoint. [`server_verdict`] encodes the
//! facts the transport read, calls [`Entry::ServerPeer`] and decodes the
//! verdict; [`PEER_RULES`] hands both ends' rules to the transport.

use eukhe_types::platform::access::{PeerRules, ServerVerdict};

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

/// The rules of both ends of eukhe's sockets: the listener's peer rule
/// (`fsmode`) and the client's server rule.
pub const PEER_RULES: PeerRules = PeerRules {
    peer: crate::rules::fsmode::peer_verdict,
    server: server_verdict,
};

/// The verdict on the listener of an abstract endpoint of uid `uid` and
/// pid `pid`, for a client of `own_uid`, when `recorded` is the pid
/// recorded for the endpoint (0: none).
#[must_use]
pub fn server_verdict(uid: u32, own_uid: u32, pid: u32, recorded: u32) -> ServerVerdict {
    expect_core(Entry::ServerPeer, server_call(uid, own_uid, pid, recorded))
}

fn server_call(uid: u32, own_uid: u32, pid: u32, recorded: u32) -> Result<ServerVerdict, Error> {
    let mut request = Writer::new();
    request.u32(uid).u32(own_uid).u32(pid).u32(recorded);
    let reply = call(Entry::ServerPeer, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let verdict = match reader.tag_of(4, "a server verdict")? {
        0 => ServerVerdict::Served,
        1 => ServerVerdict::OtherUid,
        2 => ServerVerdict::NoRecord,
        // `tag_of` answers a tag below 4: this is 3.
        _ => ServerVerdict::OtherPid,
    };
    reader.end()?;
    Ok(verdict)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each verdict comes from the compiled core, in its order: another
    /// uid first, then no record, then another pid.
    #[test]
    fn the_server_rule_comes_from_the_compiled_core() {
        assert_eq!(
            [
                server_verdict(1000, 1000, 4242, 4242),
                server_verdict(1001, 1000, 4242, 4242),
                server_verdict(1001, 1000, 4242, 0),
                server_verdict(1000, 1000, 4242, 0),
                server_verdict(1000, 1000, 0, 0),
                server_verdict(1000, 1000, 4243, 4242),
            ],
            [
                ServerVerdict::Served,
                ServerVerdict::OtherUid,
                ServerVerdict::OtherUid,
                ServerVerdict::NoRecord,
                ServerVerdict::NoRecord,
                ServerVerdict::OtherPid,
            ]
        );
    }
}
