//! Whether a URL host is a literal loopback, private, link-local or
//! unspecified address, or a `localhost` name (`bend/mcp_url.bend`, entry
//! `bend/ffi_mcp_url.bend`; `laws/mcp_url.bend`): a structural check of
//! the host text, no DNS. Rust sends the host as the url crate gives it
//! and reads the verdict.

use crate::wire::{Reader, Writer};
use crate::{call, Entry, Error};

/// Whether `host` is refused as an endpoint: `localhost` or a name ending
/// `.localhost`; an IPv4 quad in `0/8`, `10/8`, `127/8`, `169.254/16`,
/// `172.16/12` or `192.168/16`, or with a part past 255; an IPv6 address
/// that is malformed, `::`, `::1`, IPv4-mapped to a refused quad, in
/// `fe80::/10` or `fc00::/7`.
///
/// # Errors
///
/// A host past the wire's string bound, or a compiled-core failure.
pub fn literal_private_or_loopback(host: &str) -> Result<bool, Error> {
    let reply = call(Entry::McpUrl, &Writer::new().str(host).finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let refused = reader.bool()?;
    reader.end()?;
    Ok(refused)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The verdict comes from the compiled core: a loopback quad and the
    /// url crate's spelling of an IPv4-mapped loopback are refused, a
    /// public name passes.
    #[test]
    fn the_core_refuses_literal_private_hosts() {
        let verdicts = ["127.0.0.1", "[::ffff:7f00:1]", "mcp.linear.app"]
            .map(|host| literal_private_or_loopback(host).expect("the core answers"));
        assert_eq!(verdicts, [true, true, false]);
    }
}
