//! HTTP(S) proxy resolution from `*_proxy` / `no_proxy` environment values
//! (the `proxy-from-env` rules), and the matching `reqwest` proxy config.

use url::Url;

use eukhe_types::pi_ai::ProviderEnv;

use super::provider_env::get_provider_env_value;

/// Default ports of the schemes `proxy-from-env` knows.
fn default_proxy_port(protocol: &str) -> Option<u16> {
    match protocol {
        "ftp" => Some(21),
        "gopher" => Some(70),
        "http" | "ws" => Some(80),
        "https" | "wss" => Some(443),
        _ => None,
    }
}

/// Error message for SOCKS/PAC proxy URLs.
pub const UNSUPPORTED_PROXY_PROTOCOL_MESSAGE: &str =
    "Unsupported proxy protocol. SOCKS and PAC proxy URLs are not supported; use an HTTP or HTTPS proxy URL.";

/// Proxy resolution failures.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ProxyError {
    /// `Invalid proxy URL "<proxy>": <reason>`.
    #[error("Invalid proxy URL {proxy}: {reason}", proxy = serde_json::Value::String(.proxy.clone()))]
    InvalidUrl { proxy: String, reason: String },
    /// A proxy URL whose protocol is not `http:` or `https:`.
    #[error("{UNSUPPORTED_PROXY_PROTOCOL_MESSAGE} Got {protocol}")]
    UnsupportedProtocol { protocol: String },
    /// `reqwest` rejected the proxy URL.
    #[error("{0}")]
    Client(String),
}

/// Process-environment lookup (injectable for tests).
type ProcessEnv<'a> = &'a dyn Fn(&str) -> Option<String>;

fn process_env(name: &str) -> Option<String> {
    get_provider_env_value(name, None)
}

fn get_proxy_env(key: &str, env: Option<&ProviderEnv>, process: ProcessEnv<'_>) -> String {
    let lowercase_key = key.to_lowercase();
    let uppercase_key = key.to_uppercase();
    let scoped = |name: &str| {
        env.and_then(|env| env.get(name))
            .filter(|value| !value.is_empty())
            .cloned()
    };
    scoped(&lowercase_key)
        .or_else(|| scoped(&uppercase_key))
        .or_else(|| process(&lowercase_key))
        .or_else(|| process(&uppercase_key))
        .unwrap_or_default()
}

fn strip_brackets(host: &str) -> &str {
    if host.starts_with('[') && host.ends_with(']') && host.len() >= 2 {
        &host[1..host.len() - 1]
    } else {
        host
    }
}

/// JS `Number.parseInt(text, 10)`: leading decimal digits (after an optional
/// sign and whitespace), `None` for `NaN`.
fn parse_int(text: &str) -> Option<i64> {
    let text = text.trim_start_matches(super::js::is_js_whitespace);
    let (negative, digits) = match text.as_bytes().first() {
        Some(b'-') => (true, &text[1..]),
        Some(b'+') => (false, &text[1..]),
        _ => (false, text),
    };
    let end = digits.bytes().take_while(u8::is_ascii_digit).count();
    let value: i64 = digits[..end].parse().ok()?;
    Some(if negative { -value } else { value })
}

fn parse_no_proxy_entry(entry: &str) -> Option<(String, i64)> {
    let trimmed = entry
        .trim_matches(super::js::is_js_whitespace)
        .to_lowercase();
    if trimmed.is_empty() {
        return None;
    }
    if trimmed.starts_with('[') {
        if let Some(closing_bracket) = trimmed.find(']') {
            let host = trimmed[1..closing_bracket].to_owned();
            let rest = &trimmed[closing_bracket + 1..];
            if let Some(port) = rest.strip_prefix(':') {
                return Some((host, parse_int(port).unwrap_or(0)));
            }
            return Some((host, 0));
        }
    }
    if trimmed.contains(':') && trimmed.split(':').count() > 2 {
        return Some((trimmed, 0));
    }
    if let Some(colon_index) = trimmed.rfind(':') {
        if Some(colon_index) == trimmed.find(':') {
            if let Some(port) = parse_int(&trimmed[colon_index + 1..]) {
                return Some((trimmed[..colon_index].to_owned(), port));
            }
        }
    }
    Some((trimmed, 0))
}

fn should_proxy_hostname(
    hostname: &str,
    port: i64,
    env: Option<&ProviderEnv>,
    process: ProcessEnv<'_>,
) -> bool {
    let no_proxy = get_proxy_env("no_proxy", env, process).to_lowercase();
    if no_proxy.is_empty() {
        return true;
    }
    if no_proxy == "*" {
        return false;
    }
    let lowered = hostname.to_lowercase();
    let normalized_target_host = strip_brackets(&lowered);
    no_proxy
        .split(|c: char| c == ',' || is_regexp_whitespace(c))
        .all(|entry| {
            let Some((host, entry_port)) = parse_no_proxy_entry(entry) else {
                return true;
            };
            if entry_port != 0 && entry_port != port {
                return true;
            }
            let mut domain = strip_brackets(&host);
            if let Some(rest) = domain.strip_prefix("*.") {
                domain = rest;
            } else if let Some(rest) = domain
                .strip_prefix('.')
                .or_else(|| domain.strip_prefix('*'))
            {
                domain = rest;
            }
            if domain.is_empty() {
                return true;
            }
            normalized_target_host != domain
                && !normalized_target_host.ends_with(&format!(".{domain}"))
        })
}

/// JS `RegExp` `\s`: `WhiteSpace` and `LineTerminator` code points.
fn is_regexp_whitespace(c: char) -> bool {
    super::js::is_js_whitespace(c)
}

fn get_proxy_for_url(
    target_url: &str,
    env: Option<&ProviderEnv>,
    process: ProcessEnv<'_>,
) -> String {
    let Ok(parsed_url) = Url::parse(target_url) else {
        return String::new();
    };
    let Some(host) = parsed_url.host_str().filter(|host| !host.is_empty()) else {
        return String::new();
    };
    let protocol = parsed_url.scheme();
    let hostname = strip_brackets(host);
    let port = parsed_url
        .port()
        .map(i64::from)
        .filter(|port| *port != 0)
        .or_else(|| default_proxy_port(protocol).map(i64::from))
        .unwrap_or(0);
    if !should_proxy_hostname(hostname, port, env, process) {
        return String::new();
    }
    let mut proxy = get_proxy_env(&format!("{protocol}_proxy"), env, process);
    if proxy.is_empty() {
        proxy = get_proxy_env("all_proxy", env, process);
    }
    if !proxy.is_empty() && !proxy.contains("://") {
        proxy = format!("{protocol}://{proxy}");
    }
    proxy
}

fn resolve_with(
    target_url: &str,
    env: Option<&ProviderEnv>,
    process: ProcessEnv<'_>,
) -> Result<Option<Url>, ProxyError> {
    let proxy = get_proxy_for_url(target_url, env, process);
    if proxy.is_empty() {
        return Ok(None);
    }
    let proxy_url = Url::parse(&proxy).map_err(|_| ProxyError::InvalidUrl {
        proxy: proxy.clone(),
        reason: "Invalid URL".to_owned(),
    })?;
    match proxy_url.scheme() {
        "http" | "https" => Ok(Some(proxy_url)),
        other => Err(ProxyError::UnsupportedProtocol {
            protocol: format!("{other}:"),
        }),
    }
}

/// The HTTP(S) proxy for requests to `target_url`, from `env` overrides then
/// the process environment (`<scheme>_proxy`, `all_proxy`, `no_proxy`, either case).
///
/// # Errors
///
/// [`ProxyError::InvalidUrl`] for an unparsable proxy value and
/// [`ProxyError::UnsupportedProtocol`] for SOCKS/PAC/other schemes.
pub fn resolve_http_proxy_url_for_target(
    target_url: &str,
    env: Option<&ProviderEnv>,
) -> Result<Option<Url>, ProxyError> {
    resolve_with(target_url, env, &process_env)
}

/// The `reqwest` proxy config for requests to `target_url` (the Node HTTP
/// agent the TS module configures).
///
/// # Errors
///
/// See [`resolve_http_proxy_url_for_target`]; [`ProxyError::Client`] when
/// `reqwest` rejects the URL.
pub fn reqwest_proxy_for_target(
    target_url: &str,
    env: Option<&ProviderEnv>,
) -> Result<Option<reqwest::Proxy>, ProxyError> {
    resolve_http_proxy_url_for_target(target_url, env)?
        .map(|url| reqwest::Proxy::all(url).map_err(|error| ProxyError::Client(error.to_string())))
        .transpose()
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    fn resolve(
        target: &str,
        process: &[(&str, &str)],
        env: Option<&ProviderEnv>,
    ) -> Result<Option<String>, ProxyError> {
        let process: HashMap<String, String> = process
            .iter()
            .map(|(key, value)| ((*key).to_owned(), (*value).to_owned()))
            .collect();
        let lookup = move |name: &str| process.get(name).filter(|value| !value.is_empty()).cloned();
        resolve_with(target, env, &lookup).map(|url| url.map(|url| url.to_string()))
    }

    #[test]
    fn respects_no_proxy_exclusions() {
        let process = [
            ("HTTPS_PROXY", "http://proxy.example:8080"),
            ("NO_PROXY", "bedrock-runtime.us-east-1.amazonaws.com"),
        ];
        assert_eq!(
            resolve(
                "https://bedrock-runtime.us-east-1.amazonaws.com",
                &process,
                None
            ),
            Ok(None)
        );
    }

    #[test]
    fn resolves_http_and_https_proxy_urls() {
        let process = [("HTTPS_PROXY", "http://proxy.example:8080")];
        assert_eq!(
            resolve(
                "https://bedrock-runtime.us-east-1.amazonaws.com",
                &process,
                None
            ),
            Ok(Some("http://proxy.example:8080/".to_owned()))
        );
    }

    #[test]
    fn prefers_scoped_proxy_env_aliases_before_process_env_aliases() {
        let process = [("https_proxy", "http://process-proxy.example:8080")];
        let env: ProviderEnv = [(
            "HTTPS_PROXY".to_owned(),
            "http://scoped-proxy.example:8080".to_owned(),
        )]
        .into_iter()
        .collect();
        assert_eq!(
            resolve(
                "https://bedrock-runtime.us-east-1.amazonaws.com",
                &process,
                Some(&env)
            ),
            Ok(Some("http://scoped-proxy.example:8080/".to_owned()))
        );
    }

    #[test]
    fn rejects_socks_and_pac_proxy_urls_explicitly() {
        let process = [("HTTPS_PROXY", "socks5://proxy.example:1080")];
        let error = resolve(
            "https://bedrock-runtime.us-east-1.amazonaws.com",
            &process,
            None,
        )
        .unwrap_err();
        assert!(error
            .to_string()
            .contains(UNSUPPORTED_PROXY_PROTOCOL_MESSAGE));
        assert_eq!(
            error.to_string(),
            format!("{UNSUPPORTED_PROXY_PROTOCOL_MESSAGE} Got socks5:")
        );
    }

    #[test]
    fn handles_subdomain_wildcards_ipv6_and_ports_in_no_proxy() {
        let process = [
            ("HTTPS_PROXY", "http://proxy.example:8080"),
            (
                "NO_PROXY",
                "example.com, .wildcard.org, *.star.net, ::1, [2001:db8::1], 127.0.0.1:8080",
            ),
        ];
        let proxied = Ok(Some("http://proxy.example:8080/".to_owned()));
        for target in [
            "https://example.com",
            "https://api.example.com",
            "https://wildcard.org",
            "https://api.wildcard.org",
            "https://star.net",
            "https://api.star.net",
            "https://[::1]:80",
            "https://[2001:db8::1]",
            "https://127.0.0.1:8080",
        ] {
            assert_eq!(resolve(target, &process, None), Ok(None), "{target}");
        }
        assert_eq!(resolve("https://notexample.com", &process, None), proxied);
        assert_eq!(resolve("https://127.0.0.1:3000", &process, None), proxied);
    }

    #[test]
    fn reports_invalid_proxy_urls_like_the_ts_message() {
        let process = [("HTTPS_PROXY", "http://")];
        assert_eq!(
            resolve("https://example.com", &process, None)
                .unwrap_err()
                .to_string(),
            "Invalid proxy URL \"http://\": Invalid URL"
        );
    }
}
