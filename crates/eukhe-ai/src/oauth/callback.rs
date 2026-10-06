//! The Codex login's localhost callback server (TS
//! `openai-codex.ts`'s `startLocalOAuthServer` + `oauth-page.ts`): one
//! listener on the app registration's redirect port serving the
//! callback route with the product's success/error pages. Only a
//! matching redirect settles the login -- a state mismatch, a missing
//! code, or an unknown route answers its error page and keeps waiting
//! (TS calls `settleWait` on success only). A bind failure is the
//! caller's to handle: the login continues on the manual paste.

use std::sync::Arc;

use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;

/// `EUKHE_OAUTH_CALLBACK_HOST` (TS `CALLBACK_HOST`, default `127.0.0.1`).
pub(crate) const CALLBACK_HOST_ENV: &str = "EUKHE_OAUTH_CALLBACK_HOST";

/// The app registration's redirect: `http://localhost:1455/auth/callback`
/// (TS `REDIRECT_URI`; the port is the registration's, not a scan range).
pub(crate) const CALLBACK_PORT: u16 = 1455;
const CALLBACK_PATH: &str = "/auth/callback";

/// The authorization code the browser redirect carries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallbackCode {
    pub code: String,
}

/// Settled once per login; the first settle wins.
// Two states: outer None = unsettled, inner None = settled-empty (cancelled).
#[allow(clippy::option_option)]
#[derive(Default)]
struct CallbackShared {
    result: tokio::sync::Mutex<Option<Option<CallbackCode>>>,
    notify: tokio::sync::Notify,
}

impl CallbackShared {
    async fn settle(&self, result: Option<CallbackCode>) {
        let mut slot = self.result.lock().await;
        if slot.is_none() {
            *slot = Some(result);
            drop(slot);
            // `notify_one` stores a permit when no waiter is registered
            // yet, so a wait that checked the empty slot just before the
            // settle still wakes on its first poll — `notify_waiters`
            // would miss that window and hang the wait forever.
            self.notify.notify_one();
        }
    }
}

/// A running callback server.
///
/// The server owns the only strong handle on its listener (the accept
/// loop upgrades a weak one per poll), so dropping the server closes
/// the socket synchronously: a settled or cancelled login never wedges
/// the registered redirect port for the next one.
pub struct CodexCallbackServer {
    shared: Arc<CallbackShared>,
    port: u16,
    /// Held, never read: the one strong handle (see above).
    _listener: Arc<TcpListener>,
    task: tokio::task::JoinHandle<()>,
}

impl Drop for CodexCallbackServer {
    fn drop(&mut self) {
        self.task.abort();
    }
}

impl CodexCallbackServer {
    /// Bind the registered redirect port on the callback host (TS
    /// `server.listen(1455, CALLBACK_HOST)`).
    ///
    /// # Errors
    ///
    /// Returns an error when the listener cannot be bound (the login
    /// continues on the manual paste).
    pub async fn start(state: &str) -> Result<Self, String> {
        let host = std::env::var(CALLBACK_HOST_ENV).unwrap_or_else(|_| "127.0.0.1".to_string());
        Self::bind(&host, CALLBACK_PORT, state).await
    }

    /// Bind one exact host and port; the caller owns the failure (tests
    /// and embedded hosts pick free ports).
    ///
    /// # Errors
    ///
    /// Returns an error when the listener cannot be bound.
    pub async fn bind(host: &str, port: u16, state: &str) -> Result<Self, String> {
        let listener = TcpListener::bind((host, port))
            .await
            .map_err(|error| format!("port {port}: {error}"))?;
        let bound_port = listener.local_addr().map_or(port, |addr| addr.port());
        let listener = Arc::new(listener);
        let weak_listener = Arc::downgrade(&listener);
        let shared = Arc::new(CallbackShared::default());
        let task_shared = Arc::clone(&shared);
        let state = state.to_string();
        let task = tokio::spawn(async move {
            loop {
                // The strong handle lives only inside one poll: a dropped
                // server closes the listener even while this loop waits.
                let accepted = std::future::poll_fn(|context| match weak_listener.upgrade() {
                    Some(listener) => listener.poll_accept(context).map(Some),
                    None => std::task::Poll::Ready(None),
                })
                .await;
                let Some(Ok((stream, _))) = accepted else {
                    break;
                };
                let shared = Arc::clone(&task_shared);
                let state = state.clone();
                tokio::spawn(async move {
                    serve_callback(stream, &shared, &state).await;
                });
            }
        });
        Ok(CodexCallbackServer {
            shared,
            port: bound_port,
            _listener: listener,
            task,
        })
    }

    /// The bound port.
    #[must_use]
    pub fn port(&self) -> u16 {
        self.port
    }

    /// Wait for the browser redirect to settle: the code, or `None`
    /// when the wait was cancelled. A taken code re-arms the slot for
    /// the next redirect.
    pub async fn wait_for_code(&self) -> Option<CallbackCode> {
        loop {
            if let Some(result) = self.shared.result.lock().await.take() {
                return result;
            }
            self.shared.notify.notified().await;
        }
    }

    /// Cancel: settle the waiter with `None` (TS `cancelWait`).
    pub async fn cancel(&self) {
        self.shared.settle(None).await;
    }
}

/// One browser request: read it, answer it, settle the login only on a
/// matching redirect (TS the callback handler's validation order —
/// route, state, code).
async fn serve_callback(mut stream: tokio::net::TcpStream, shared: &CallbackShared, state: &str) {
    let Some(request) = read_request_head(&mut stream).await else {
        let _ = write_response(
            &mut stream,
            "400 Bad Request",
            error_page("Callback route not found."),
        )
        .await;
        return;
    };
    let target = request
        .lines()
        .next()
        .unwrap_or_default()
        .split_whitespace()
        .nth(1)
        .unwrap_or_default();
    let path = target.split('?').next().unwrap_or_default();
    if path != CALLBACK_PATH {
        let _ = write_response(
            &mut stream,
            "404 Not Found",
            error_page("Callback route not found."),
        )
        .await;
        return;
    }
    let query = target.split_once('?').map_or("", |(_, query)| query);
    let code = query_param(query, "code");
    if query_param(query, "state").as_deref() != Some(state) {
        let _ = write_response(
            &mut stream,
            "400 Bad Request",
            error_page("State mismatch."),
        )
        .await;
        return;
    }
    match code {
        Some(code) if !code.is_empty() => {
            shared.settle(Some(CallbackCode { code })).await;
            let _ = write_response(
                &mut stream,
                "200 OK",
                success_page("OpenAI authentication completed. You can close this window."),
            )
            .await;
        }
        _ => {
            let _ = write_response(
                &mut stream,
                "400 Bad Request",
                error_page("Missing authorization code."),
            )
            .await;
        }
    }
}

/// Read one request head: accumulate until the head's closing blank
/// line (a request split across TCP reads stays complete; the callback
/// browser request carries no body worth parsing).
async fn read_request_head(stream: &mut tokio::net::TcpStream) -> Option<String> {
    let mut head = Vec::with_capacity(1024);
    let mut buffer = [0u8; 8192];
    loop {
        if head.windows(4).any(|window| window == b"\r\n\r\n") {
            return Some(String::from_utf8_lossy(&head).to_string());
        }
        if head.len() >= buffer.len() {
            // An oversized head: parse what arrived (the handler's route
            // checks reject it).
            return Some(String::from_utf8_lossy(&head).to_string());
        }
        let read = stream.read(&mut buffer).await.ok()?;
        if read == 0 {
            return None;
        }
        head.extend_from_slice(&buffer[..read]);
    }
}

async fn write_response(
    stream: &mut tokio::net::TcpStream,
    status: &str,
    body: String,
) -> std::io::Result<()> {
    let head = format!(
        "HTTP/1.1 {status}\r\nContent-Type: text/html; charset=utf-8\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(head.as_bytes()).await?;
    stream.write_all(body.as_bytes()).await?;
    stream.flush().await
}

/// One decoded query parameter (`+` as space, percent-decoded).
fn query_param(query: &str, name: &str) -> Option<String> {
    for pair in query.split('&') {
        if pair.is_empty() {
            continue;
        }
        let (key, value) = pair.split_once('=').unwrap_or((pair, ""));
        if percent_decode(&key.replace('+', " ")) == name {
            return Some(percent_decode(&value.replace('+', " ")));
        }
    }
    None
}

fn percent_decode(value: &str) -> String {
    let bytes = value.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] == b'%' && index + 2 < bytes.len() {
            // The two bytes after `%` are decoded as bytes — a slice of
            // the UTF-8 string there could split a multi-byte character
            // and panic, so malformed escapes fall through to the
            // literal byte instead.
            if let Ok(hex) = std::str::from_utf8(&bytes[index + 1..index + 3]) {
                if let Ok(byte) = u8::from_str_radix(hex, 16) {
                    out.push(byte);
                    index += 3;
                    continue;
                }
            }
        }
        out.push(bytes[index]);
        index += 1;
    }
    String::from_utf8_lossy(&out).to_string()
}

fn escape_html(value: &str) -> String {
    let mut out = String::with_capacity(value.len());
    for character in value.chars() {
        match character {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            other => out.push(other),
        }
    }
    out
}

/// The callback pages: a dark minimal page carrying the login's outcome
/// (the port's page shape; the TS flow's own wording rides the
/// messages).
fn render_page(title: &str, message: &str) -> String {
    format!(
        r#"<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>{}</title>
  <style>
    body {{ margin: 0; min-height: 100vh; display: flex; align-items: center;
           justify-content: center; padding: 24px; background: #000; color: #fff;
           font-family: ui-sans-serif, system-ui, sans-serif; text-align: center; }}
    main {{ width: 100%; max-width: 560px; }}
    h1 {{ margin: 0 0 10px; font-size: 28px; line-height: 1.15; font-weight: 650; }}
    p {{ margin: 0; line-height: 1.7; color: #a1a1aa; font-size: 15px; }}
  </style>
</head>
<body>
  <main>
    <h1>Authentication</h1>
    <p>{}</p>
  </main>
</body>
</html>"#,
        escape_html(title),
        escape_html(message)
    )
}

fn success_page(message: &str) -> String {
    render_page("Eukhe authentication completed", message)
}

fn error_page(message: &str) -> String {
    render_page("Eukhe authentication failed", message)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    /// One live server on a free loopback port, with its port.
    async fn live(state: &str) -> (CodexCallbackServer, u16) {
        let server = CodexCallbackServer::bind("127.0.0.1", 0, state)
            .await
            .expect("a free loopback port binds");
        let port = server.port();
        (server, port)
    }

    /// One raw browser request and its whole response.
    async fn request(port: u16, target: &str) -> String {
        use tokio::io::AsyncReadExt as _;
        let mut stream = tokio::net::TcpStream::connect(("127.0.0.1", port))
            .await
            .expect("the callback server accepts the connection");
        stream
            .write_all(format!("GET {target} HTTP/1.1\r\nHost: localhost\r\n\r\n").as_bytes())
            .await
            .expect("the request writes");
        let mut response = String::new();
        let mut buffer = [0u8; 4096];
        loop {
            let read = stream.read(&mut buffer).await.unwrap_or(0);
            if read == 0 {
                break;
            }
            response.push_str(&String::from_utf8_lossy(&buffer[..read]));
            if response.contains("</html>") {
                break;
            }
        }
        response
    }

    /// The missed-notification regression: a settle landing between the
    /// wait's empty-slot check and its `notified` registration still
    /// wakes — the settle's stored permit (`notify_one`) completes the
    /// future's first poll. With a `notify_waiters` settle this wait
    /// would hang and the bound fails the test.
    #[tokio::test]
    async fn a_settle_in_the_registration_window_still_wakes() {
        let server = CodexCallbackServer::bind("127.0.0.1", 0, "the-state")
            .await
            .expect("a free loopback port binds");
        let shared = &server.shared;
        // The wait's shape, with the race window staged exactly: the
        // slot check ran (empty), the `notified` future exists but has
        // not registered yet, and the settle lands in that window.
        let notified = shared.notify.notified();
        assert!(
            shared.result.lock().await.is_none(),
            "the slot starts empty"
        );
        shared.settle(None).await;
        tokio::time::timeout(Duration::from_secs(2), notified)
            .await
            .expect("the wait wakes on the stored permit");
        let settled = shared.result.lock().await.take();
        assert_eq!(settled, Some(None));
    }

    /// The fragmentation regression: a request split across reads stays
    /// complete (the head accumulates until the closing blank line).
    #[tokio::test]
    async fn a_request_split_across_reads_parses() {
        let (server, port) = live("the-state").await;
        let mut stream = tokio::net::TcpStream::connect(("127.0.0.1", port))
            .await
            .expect("the callback server accepts the connection");
        stream
            .write_all(b"GET /auth/call")
            .await
            .expect("the first fragment writes");
        stream.flush().await.expect("the fragment flushes");
        tokio::time::sleep(Duration::from_millis(20)).await;
        stream
            .write_all(b"back?code=split-code&state=the-state HTTP/1.1\r\nHost: localhost\r\n\r\n")
            .await
            .expect("the rest of the request writes");
        // The settle is the observable readiness: the split request
        // still settles its code.
        let code = tokio::time::timeout(Duration::from_secs(2), server.wait_for_code())
            .await
            .expect("the split request settles")
            .expect("the code settles");
        assert_eq!(code.code, "split-code");
    }

    #[tokio::test]
    async fn a_matching_redirect_settles_the_code() {
        let (server, port) = live("the-state").await;
        let response = request(port, "/auth/callback?code=the-code&state=the-state").await;
        assert!(response.starts_with("HTTP/1.1 200 OK"), "{response}");
        assert!(
            response.contains("OpenAI authentication completed. You can close this window."),
            "{response}"
        );
        assert_eq!(
            server.wait_for_code().await,
            Some(CallbackCode {
                code: "the-code".to_string()
            })
        );
    }

    #[tokio::test]
    async fn a_state_mismatch_answers_and_keeps_waiting() {
        let (server, port) = live("the-state").await;
        let response = request(port, "/auth/callback?code=c&state=other").await;
        assert!(
            response.starts_with("HTTP/1.1 400 Bad Request"),
            "{response}"
        );
        assert!(response.contains("State mismatch."), "{response}");
        // A mismatch never settles the login; cancellation does.
        server.cancel().await;
        assert_eq!(server.wait_for_code().await, None);
    }

    #[tokio::test]
    async fn a_missing_code_answers_and_keeps_waiting() {
        let (server, port) = live("the-state").await;
        let response = request(port, "/auth/callback?state=the-state").await;
        assert!(
            response.starts_with("HTTP/1.1 400 Bad Request"),
            "{response}"
        );
        assert!(
            response.contains("Missing authorization code."),
            "{response}"
        );
        server.cancel().await;
        assert_eq!(server.wait_for_code().await, None);
    }

    #[tokio::test]
    async fn an_unknown_route_answers_404_without_settling() {
        let (server, port) = live("the-state").await;
        let response = request(port, "/other?code=c&state=the-state").await;
        assert!(response.starts_with("HTTP/1.1 404 Not Found"), "{response}");
        assert!(response.contains("Callback route not found."), "{response}");
        server.cancel().await;
        assert_eq!(server.wait_for_code().await, None);
    }

    /// The port-release regression: a dropped server frees its port
    /// before the next statement (an aborted accept task holding the
    /// listener kept it bound until the runtime polled it).
    #[tokio::test]
    async fn a_dropped_server_releases_its_port_at_once() {
        let (server, port) = live("the-state").await;
        drop(server);
        std::net::TcpListener::bind(("127.0.0.1", port))
            .expect("the dropped server's port binds again immediately");
    }

    #[tokio::test]
    async fn an_unbindable_port_yields_the_error() {
        let held = std::net::TcpListener::bind(("127.0.0.1", 0)).expect("a probe port");
        let port = held.local_addr().unwrap().port();
        assert!(CodexCallbackServer::bind("127.0.0.1", port, "s")
            .await
            .is_err());
    }

    #[test]
    fn query_and_percent_decoding() {
        assert_eq!(percent_decode("a%20b"), "a b");
        assert_eq!(percent_decode("bad%2"), "bad%2");
        // A `%` escape that would split a multi-byte character decodes
        // as the literal bytes (the regression for the panicking
        // string slice).
        assert_eq!(percent_decode("%9\u{e9}"), "%9\u{e9}");
        assert_eq!(
            query_param("code=1&state=2", "state"),
            Some("2".to_string())
        );
        assert_eq!(query_param("code=a+b", "code"), Some("a b".to_string()));
        assert_eq!(query_param("code", "state"), None);
    }

    #[test]
    fn the_pages_escape_their_text() {
        let page = error_page("<script>&\"'</script>");
        // The angle brackets escape too: the payload renders fully
        // entity-encoded, never as raw markup.
        assert!(
            page.contains("&lt;script&gt;&amp;&quot;&#39;&lt;/script&gt;"),
            "{page}"
        );
        assert!(!page.contains("<script>"), "{page}");
    }
}
