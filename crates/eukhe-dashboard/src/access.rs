//! Who may reach the dashboard. Every request must name a loopback host
//! (`127.0.0.1`, `localhost`, `[::1]`, any port) or a host the user
//! allowed (`eukhe dashboard --allow-host <name>`) in its `Host`; that
//! defeats DNS rebinding, where a foreign name resolves to 127.0.0.1 but
//! the browser still sends that name. A WebSocket upgrade must also carry
//! the page's own `Origin`: the origin of the `Host` it was served under,
//! or of the public authority that a forwarder in front of the dashboard
//! names in `X-Forwarded-Host` (porthmeus rewrites `Host` to the local address
//! and keeps the browser's `Origin`). That defeats cross-site WebSocket
//! hijacking, where another site's page opens the socket with its own
//! origin: a page cannot add `X-Forwarded-Host` to a WebSocket handshake,
//! so the header comes only from a forwarder or a local program, and a
//! local program can send any `Origin` anyway.

/// The host names that are always allowed.
const LOOPBACK: [&str; 3] = ["127.0.0.1", "localhost", "[::1]"];

/// One `host[:port]` split in two; IPv6 literals keep their brackets.
/// `None` when the text is not an authority (empty, a bad port, userinfo,
/// a path).
fn split_authority(authority: &str) -> Option<(&str, Option<u16>)> {
    if authority.is_empty() || authority.contains(['@', '/', '?', '#', ' ']) {
        return None;
    }
    let (host, port) = if authority.starts_with('[') {
        let end = authority.find(']')?;
        let (host, rest) = authority.split_at(end + 1);
        match rest {
            "" => (host, None),
            rest => (host, Some(rest.strip_prefix(':')?)),
        }
    } else {
        match authority.rsplit_once(':') {
            Some((host, port)) => (host, Some(port)),
            None => (authority, None),
        }
    };
    if host.is_empty() || (host.contains(':') && !host.starts_with('[')) {
        return None;
    }
    let port = match port {
        Some(port) => Some(port.parse::<u16>().ok()?),
        None => None,
    };
    Some((host, port))
}

/// Whether a request's `Host` names a host the dashboard serves.
pub(crate) fn host_allowed(host: &str, allowed_hosts: &[String]) -> bool {
    split_authority(host).is_some_and(|(name, _)| {
        LOOPBACK
            .iter()
            .copied()
            .chain(allowed_hosts.iter().map(String::as_str))
            .any(|allowed| allowed.eq_ignore_ascii_case(name))
    })
}

/// Whether `origin` (the `Origin` header) is the origin of a page served
/// under `host` (the request's `Host`): same host, and the same port once
/// the scheme's default port fills in a missing one.
pub(crate) fn same_origin(origin: &str, host: &str) -> bool {
    let Some((scheme, authority)) = origin.split_once("://") else {
        return false;
    };
    let default_port = match scheme.to_ascii_lowercase().as_str() {
        "http" => 80,
        "https" => 443,
        _ => return false,
    };
    match (split_authority(authority), split_authority(host)) {
        (Some((origin_name, origin_port)), Some((host_name, host_port))) => {
            origin_name.eq_ignore_ascii_case(host_name)
                && origin_port.unwrap_or(default_port) == host_port.unwrap_or(default_port)
        }
        (None, _) | (_, None) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hosts_are_loopback_or_allowed() {
        let allowed = vec!["box.tail1234.ts.net".to_string()];
        let verdicts: Vec<bool> = [
            "127.0.0.1:8377",
            "127.0.0.1",
            "LOCALHOST:1",
            "[::1]:8377",
            "[::1]",
            "box.tail1234.ts.net",
            "Box.Tail1234.ts.net:443",
            "evil.example:8377",
            "127.0.0.1.evil.example",
            "localhost.",
            "",
            "127.0.0.1:http",
            "user@127.0.0.1",
            "::1",
        ]
        .iter()
        .map(|host| host_allowed(host, &allowed))
        .collect();
        assert_eq!(
            verdicts,
            [
                true, true, true, true, true, true, true, false, false, false, false, false, false,
                false
            ]
        );
    }

    #[test]
    fn an_origin_matches_only_its_own_host_and_port() {
        let verdicts: Vec<bool> = [
            ("http://127.0.0.1:8377", "127.0.0.1:8377"),
            ("https://box.ts.net", "box.ts.net"),
            ("https://box.ts.net", "box.ts.net:443"),
            ("http://localhost", "localhost:80"),
            ("http://[::1]:9", "[::1]:9"),
            ("http://127.0.0.1:8377", "localhost:8377"),
            ("http://127.0.0.1:9999", "127.0.0.1:8377"),
            ("https://evil.example", "127.0.0.1:8377"),
            ("http://box.ts.net", "box.ts.net:443"),
            ("null", "127.0.0.1:8377"),
            ("file://", "127.0.0.1:8377"),
            ("http://127.0.0.1:8377/path", "127.0.0.1:8377"),
        ]
        .iter()
        .map(|(origin, host)| same_origin(origin, host))
        .collect();
        assert_eq!(
            verdicts,
            [true, true, true, true, true, false, false, false, false, false, false, false]
        );
    }
}
