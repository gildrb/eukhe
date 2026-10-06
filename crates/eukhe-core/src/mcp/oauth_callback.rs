//! The local OAuth callback server.
//!
//! One fresh listener per candidate port (a failed bind cannot reuse a
//! socket), on the registered redirect ports; the login flow races the
//! browser callback against a manual paste. Every callback-route hit
//! settles one outcome (the code, or why it cannot complete the login)
//! for the flow to take; the slot re-arms once taken. The served pages
//! keep the TS product's success/error wording.

use std::sync::Arc;

use anyhow::{anyhow, Result};
use eukhe_ai::oauth::{parse_redirect_input, RedirectInputError, VerifiedAuthorization};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;

/// `EUKHE_OAUTH_CALLBACK_HOST` (default `127.0.0.1`).
fn callback_host() -> String {
    std::env::var("EUKHE_OAUTH_CALLBACK_HOST").unwrap_or_else(|_| "127.0.0.1".to_string())
}

/// A range (not one port) so a leaked or concurrent login cannot wedge all
/// logins with one occupied socket. Distinct from the Anthropic callback
/// port (53692); every candidate is a registered redirect URI.
pub(crate) const CALLBACK_PORT_BASE: u16 = 53_700;
pub(crate) const CALLBACK_PORT_COUNT: u16 = 10;
const CALLBACK_PATH: &str = "/callback";

pub(crate) fn redirect_uri_for(port: u16) -> String {
    format!("http://localhost:{port}{CALLBACK_PATH}")
}

/// Every redirect URI a login registers (dynamic client registration
/// offers them all).
pub fn all_redirect_uris() -> Vec<String> {
    (0..CALLBACK_PORT_COUNT)
        .map(|offset| redirect_uri_for(CALLBACK_PORT_BASE + offset))
        .collect()
}

/// Serializes this crate's tests that bind the callback range: one holding
/// every candidate would otherwise starve another's start.
#[cfg(test)]
pub(crate) static CALLBACK_PORT_LOCK: tokio::sync::Mutex<()> = tokio::sync::Mutex::const_new(());

/// The range's staging probe: `true` when this run can bind every
/// candidate (another process holding one makes the fallback layout
/// unpredictable). Call it under the lock above.
#[cfg(test)]
pub(crate) fn callback_range_stages() -> bool {
    (0..CALLBACK_PORT_COUNT).all(|offset| {
        std::net::TcpListener::bind(("127.0.0.1", CALLBACK_PORT_BASE + offset)).is_ok()
    })
}

/// One callback-route hit: the code with this login's state, or why it
/// cannot complete the login (an OAuth error, no code, another state).
pub type CallbackResult = Result<VerifiedAuthorization, RedirectInputError>;

/// One settled outcome per take; the first settle into an empty slot wins.
#[derive(Default, Debug)]
struct CallbackShared {
    result: tokio::sync::Mutex<Option<CallbackResult>>,
    notify: tokio::sync::Notify,
}

impl CallbackShared {
    async fn settle(&self, result: CallbackResult) {
        let mut slot = self.result.lock().await;
        if slot.is_none() {
            *slot = Some(result);
            drop(slot);
            // `notify_one` stores a permit when no waiter is registered
            // yet: a wait between its empty-slot check and its `notified`
            // registration still wakes (`notify_waiters` would hang it).
            self.notify.notify_one();
        }
    }
}

/// A running callback server: its redirect URI plus the settled result.
///
/// The server owns the only strong handle on its listener (the accept
/// loop upgrades a weak one per poll), so dropping the server closes the
/// socket synchronously: a finished login never holds its port.
#[derive(Debug)]
pub struct CallbackServer {
    shared: Arc<CallbackShared>,
    port: u16,
    /// Held, never read: the one strong handle (see above).
    _listener: Arc<TcpListener>,
    task: tokio::task::JoinHandle<()>,
}

impl Drop for CallbackServer {
    fn drop(&mut self) {
        self.task.abort();
    }
}

impl CallbackServer {
    /// Bind the first free candidate port; a hit must echo
    /// `expected_state`.
    ///
    /// # Errors
    ///
    /// Returns an error when every candidate port is busy (the login goes
    /// on with the paste when it has one).
    pub async fn start(label: &str, expected_state: &str) -> Result<Self> {
        let host = callback_host();
        let mut last_error: Option<String> = None;
        for offset in 0..CALLBACK_PORT_COUNT {
            let port = CALLBACK_PORT_BASE + offset;
            let listener = match TcpListener::bind((host.as_str(), port)).await {
                Ok(listener) => Arc::new(listener),
                Err(error) => {
                    last_error = Some(format!("port {port}: {error}"));
                    continue;
                }
            };
            let weak_listener = Arc::downgrade(&listener);
            let shared = Arc::new(CallbackShared::default());
            let task_shared = Arc::clone(&shared);
            let expected_state = expected_state.to_string();
            let task = tokio::spawn(async move {
                loop {
                    // The strong handle lives only inside one poll: a
                    // dropped server closes the listener even while this
                    // loop waits.
                    let accepted = std::future::poll_fn(|context| match weak_listener.upgrade() {
                        Some(listener) => listener.poll_accept(context).map(Some),
                        None => std::task::Poll::Ready(None),
                    })
                    .await;
                    let Some(Ok((stream, _))) = accepted else {
                        break;
                    };
                    let shared = Arc::clone(&task_shared);
                    let expected_state = expected_state.clone();
                    tokio::spawn(async move {
                        serve_callback(stream, &shared, &expected_state).await;
                    });
                }
            });
            return Ok(CallbackServer {
                shared,
                port,
                _listener: listener,
                task,
            });
        }
        Err(anyhow!(
            "Could not start the OAuth callback server: ports {CALLBACK_PORT_BASE}-{} are all in use. \
             Close other login attempts and retry. ({label}; {})",
            CALLBACK_PORT_BASE + CALLBACK_PORT_COUNT - 1,
            last_error.unwrap_or_else(|| "no candidate port bound".to_string()),
        ))
    }

    /// The local URL the authorization redirect must land on.
    pub fn redirect_uri(&self) -> String {
        redirect_uri_for(self.port)
    }

    /// Wait for the next callback-route hit; taking it re-arms the slot.
    pub async fn wait_for_code(&self) -> CallbackResult {
        loop {
            if let Some(result) = self.shared.result.lock().await.take() {
                return result;
            }
            self.shared.notify.notified().await;
        }
    }

    /// Whether a hit is waiting to be taken (tests observe the
    /// non-settling routes).
    #[cfg(test)]
    async fn is_settled(&self) -> bool {
        self.shared.result.lock().await.is_some()
    }
}

/// One browser request: read it, answer it, settle the login's waiter
/// (unknown routes answer 404 and settle nothing).
async fn serve_callback(mut stream: tokio::net::TcpStream, shared: &CallbackShared, state: &str) {
    let Some(request) = read_request_head(&mut stream).await else {
        let _ = write_response(
            &mut stream,
            "400 Bad Request",
            oauth_error_page("Eukhe", "Callback route not found."),
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
        .unwrap_or_default()
        .to_string();
    let path = target.split('?').next().unwrap_or_default();
    if path != CALLBACK_PATH {
        let _ = write_response(
            &mut stream,
            "404 Not Found",
            oauth_error_page("Eukhe", "Callback route not found."),
        )
        .await;
        return;
    }
    let query = target.split_once('?').map_or("", |(_, query)| query);
    // The browser hit must echo the state: a missing one fails the CSRF
    // check like a foreign one (a paste may omit it, a redirect never).
    let outcome = parse_redirect_input(&format!("?{query}")).and_then(|pasted| {
        if pasted.state.is_none() {
            Err(RedirectInputError::StateMismatch)
        } else {
            pasted.verify_state(state)
        }
    });
    let (status, page) = match &outcome {
        Ok(_) => (
            "200 OK",
            oauth_success_page("Eukhe authentication completed. You can close this window."),
        ),
        Err(RedirectInputError::Provider { error, description }) => (
            "400 Bad Request",
            oauth_error_page(
                "Eukhe",
                &match description {
                    Some(description) => {
                        format!("Eukhe authentication failed. Error: {error} ({description})")
                    }
                    None => format!("Eukhe authentication failed. Error: {error}"),
                },
            ),
        ),
        Err(RedirectInputError::MissingCode) => (
            "400 Bad Request",
            oauth_error_page("Eukhe", "Missing code or state parameter."),
        ),
        Err(RedirectInputError::StateMismatch) => (
            "400 Bad Request",
            oauth_error_page("Eukhe", "State mismatch."),
        ),
    };
    shared.settle(outcome).await;
    let _ = write_response(&mut stream, status, page).await;
}

/// Read one request head (until the connection goes quiet); the callback
/// browser request carries no body worth parsing.
async fn read_request_head(stream: &mut tokio::net::TcpStream) -> Option<String> {
    let mut buffer = [0u8; 8192];
    let read = stream.read(&mut buffer).await.ok()?;
    if read == 0 {
        return None;
    }
    Some(String::from_utf8_lossy(&buffer[..read]).to_string())
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

/// The callback pages: a dark minimal page carrying the login's outcome.
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
        escape_html(message),
    )
}

fn oauth_success_page(message: &str) -> String {
    render_page("Eukhe authentication completed", message)
}

fn oauth_error_page(label: &str, message: &str) -> String {
    render_page(&format!("{label} authentication failed"), message)
}

#[cfg(test)]
mod tests {
    use super::*;

    async fn hit(server: &CallbackServer, target: &str) -> u16 {
        reqwest::Client::new()
            .get(format!("http://127.0.0.1:{}{target}", server.port))
            .send()
            .await
            .unwrap()
            .status()
            .as_u16()
    }

    #[tokio::test]
    async fn falls_back_to_the_next_free_port() {
        let _ports = CALLBACK_PORT_LOCK.lock().await;
        if !callback_range_stages() {
            return; // the range is busy: this run cannot stage it.
        }
        // The base port is occupied, so the login lands on a later
        // candidate (a leaked login cannot wedge all of them).
        let blocker = std::net::TcpListener::bind(("127.0.0.1", CALLBACK_PORT_BASE)).unwrap();
        let server = CallbackServer::start("Linear", "st").await.unwrap();
        assert_ne!(server.redirect_uri(), redirect_uri_for(CALLBACK_PORT_BASE));
        assert!(server.redirect_uri().starts_with("http://localhost:5370"));
        drop(blocker);
    }

    #[tokio::test]
    async fn all_candidates_bound_fails_clearly() {
        let _ports = CALLBACK_PORT_LOCK.lock().await;
        // Whatever this run cannot bind is held elsewhere: busy either way.
        let _blockers: Vec<std::net::TcpListener> = (0..CALLBACK_PORT_COUNT)
            .filter_map(|offset| {
                std::net::TcpListener::bind(("127.0.0.1", CALLBACK_PORT_BASE + offset)).ok()
            })
            .collect();
        let error = CallbackServer::start("Linear", "st")
            .await
            .unwrap_err()
            .to_string();
        assert!(error.contains("Could not start the OAuth callback server"));
    }

    /// Every callback-route hit settles its outcome, and taking one
    /// re-arms the slot for the next hit (a retried browser login).
    #[tokio::test]
    async fn callback_hits_settle_their_outcomes_in_turn() {
        let _ports = CALLBACK_PORT_LOCK.lock().await;
        if !callback_range_stages() {
            return; // the range is busy: this run cannot stage it.
        }
        let server = CallbackServer::start("Linear", "the-state").await.unwrap();
        assert_eq!(hit(&server, "/callback?code=x&state=other").await, 400);
        assert_eq!(
            server.wait_for_code().await,
            Err(RedirectInputError::StateMismatch)
        );
        assert_eq!(
            hit(
                &server,
                "/callback?error=access_denied&error_description=no+way"
            )
            .await,
            400
        );
        assert_eq!(
            server.wait_for_code().await,
            Err(RedirectInputError::Provider {
                error: "access_denied".to_string(),
                description: Some("no way".to_string()),
            })
        );
        assert_eq!(hit(&server, "/callback?code=x").await, 400);
        assert_eq!(
            server.wait_for_code().await,
            Err(RedirectInputError::StateMismatch)
        );
        assert_eq!(
            hit(&server, "/callback?code=the-code&state=the-state").await,
            200
        );
        assert_eq!(
            server.wait_for_code().await,
            Ok(VerifiedAuthorization {
                code: "the-code".to_string(),
                state: "the-state".to_string()
            })
        );
    }

    #[tokio::test]
    async fn unknown_route_is_404_without_settling() {
        let _ports = CALLBACK_PORT_LOCK.lock().await;
        if !callback_range_stages() {
            return; // the range is busy: this run cannot stage it.
        }
        let server = CallbackServer::start("Linear", "st").await.unwrap();
        assert_eq!(hit(&server, "/other").await, 404);
        assert!(!server.is_settled().await);
    }

    /// Dropping the server frees its port at once, even while the accept
    /// loop waits: the next login rebinds the same candidate.
    #[tokio::test]
    async fn a_dropped_server_releases_its_port() {
        let _ports = CALLBACK_PORT_LOCK.lock().await;
        if !callback_range_stages() {
            return; // the range is busy: this run cannot stage it.
        }
        let server = CallbackServer::start("Linear", "st").await.unwrap();
        let port = server.port;
        drop(server);
        assert!(
            std::net::TcpListener::bind(("127.0.0.1", port)).is_ok(),
            "port {port} is still held after the drop"
        );
    }
}
