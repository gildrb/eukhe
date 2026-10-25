//! Who may reach the dashboard: the compiled Bend core decides
//! (`bend/dash_access.bend`, entry `bend/ffi_dash_access.bend`, laws
//! `laws/dash_access.bend`). Every request must name a loopback host
//! (`127.0.0.1`, `localhost`, `[::1]`, any port) or a host the user
//! allowed (`eukhe dashboard --allow-host <name>`) in its `Host`; that
//! defeats DNS rebinding, where a foreign name resolves to 127.0.0.1 but
//! the browser still sends that name. A WebSocket upgrade must also carry
//! the page's own `Origin`: the origin of the `Host` it was served under,
//! or of the public authority that a forwarder in front of the dashboard
//! names in `X-Forwarded-Host` (poros rewrites `Host` to the local address
//! and keeps the browser's `Origin`). That defeats cross-site WebSocket
//! hijacking, where another site's page opens the socket with its own
//! origin: a page cannot add `X-Forwarded-Host` to a WebSocket handshake,
//! so the header comes only from a forwarder or a local program, and a
//! local program can send any `Origin` anyway.
//!
//! Every text here is an HTTP header value or a host name from the command
//! line: hyper bounds a request's headers far below the wire's `STR_MAX`.

use eukhe_bend::wire::{Reader, Writer};
use eukhe_bend::{call, expect_core, Entry, Error};

/// The core's verdict on the request in `writer`.
fn ask(writer: &mut Writer) -> bool {
    let mut answer = || -> Result<bool, Error> {
        let reply = call(Entry::DashAccess, &writer.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let verdict = reader.bool()?;
        reader.end()?;
        Ok(verdict)
    };
    expect_core(Entry::DashAccess, answer())
}

/// Whether a request's `Host` names a host the dashboard serves.
pub(crate) fn host_allowed(host: &str, allowed_hosts: &[String]) -> bool {
    let mut writer = Writer::new();
    writer.tag(0).str(host).count(allowed_hosts.len());
    for allowed in allowed_hosts {
        writer.str(allowed);
    }
    ask(&mut writer)
}

/// Whether `origin` (the `Origin` header) is the origin of a page served
/// under `host` (the request's `Host`): same host, and the same port once
/// the scheme's default port fills in a missing one.
pub(crate) fn same_origin(origin: &str, host: &str) -> bool {
    ask(Writer::new().tag(1).str(origin).str(host))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_core_decides_hosts_and_origins() {
        let allowed = vec!["box.ts.net".to_string()];
        assert_eq!(
            [
                host_allowed("127.0.0.1:8377", &[]),
                host_allowed("Box.ts.net", &allowed),
                host_allowed("evil.example", &allowed),
                same_origin("http://localhost", "localhost:80"),
                same_origin("https://evil.example", "127.0.0.1:8377"),
            ],
            [true, true, false, true, false]
        );
    }
}
