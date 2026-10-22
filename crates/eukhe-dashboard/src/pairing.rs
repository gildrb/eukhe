//! Pairing: the token a tab must present before the bridge runs anything
//! for it. The token is 32 random bytes, kept as 64 hex digits in a file
//! of the agent dir (mode 0600), so a link that holds it keeps working
//! across restarts until a rotation replaces it. `eukhe dashboard` puts
//! the token in the URL's fragment, which the browser never sends to a
//! server; the app sends it in the first frame of each socket.
//!
//! Every check reads the file again, so a rotation by another
//! `eukhe dashboard` process takes effect at the next check of this one.
//! The comparison is constant-time. The token never goes into a log line
//! or an error text.

use std::fmt;
use std::io::Write;
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::Path;

use anyhow::Context;
use subtle::ConstantTimeEq;

/// The bytes of a token.
const TOKEN_BYTES: usize = 32;

/// A pairing token. Its `Debug` hides the value; only
/// [`PairingToken::secret_hex`] shows it.
#[derive(Clone, PartialEq, Eq)]
pub struct PairingToken([u8; TOKEN_BYTES]);

impl fmt::Debug for PairingToken {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("PairingToken(..)")
    }
}

impl PairingToken {
    /// A new random token.
    fn fresh() -> anyhow::Result<Self> {
        let mut bytes = [0; TOKEN_BYTES];
        getrandom::fill(&mut bytes)
            .map_err(|error| anyhow::anyhow!("get random bytes for the pairing token: {error}"))?;
        Ok(Self(bytes))
    }

    /// The token as 64 lowercase hex digits: the text of the file and of
    /// the URL fragment. Never log it.
    #[must_use]
    pub fn secret_hex(&self) -> String {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";
        let mut hex = String::with_capacity(TOKEN_BYTES * 2);
        for byte in self.0 {
            hex.push(char::from(DIGITS[usize::from(byte >> 4)]));
            hex.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
        }
        hex
    }

    /// The token that `text` spells (64 hex digits, either case); `None`
    /// for any other text. Only the length and the digit set decide, so
    /// the time depends on the presented text, never on the secret.
    pub(crate) fn parse(text: &str) -> Option<Self> {
        let digits = text.as_bytes();
        if digits.len() != TOKEN_BYTES * 2 {
            return None;
        }
        let mut bytes = [0; TOKEN_BYTES];
        for (byte, &[high, low]) in bytes.iter_mut().zip(digits.as_chunks::<2>().0) {
            // One hex digit per character: `u8::from_str_radix` on a pair
            // also takes a sign ("+a" read as 0x0a).
            let digit = |c: u8| char::from(c).to_digit(16);
            *byte = u8::try_from(digit(high)? * 16 + digit(low)?).ok()?;
        }
        Some(Self(bytes))
    }

    /// Whether `other` is this token, in constant time.
    fn same(&self, other: &Self) -> bool {
        bool::from(self.0.ct_eq(&other.0))
    }
}

/// Whether `eukhe dashboard` keeps the stored token or replaces it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rotation {
    /// Use the stored token; make one when there is none.
    Keep,
    /// Replace the stored token with a new one: every earlier token stops
    /// working.
    Rotate,
}

/// The pairing token stored at `path`: the stored one, or a new one when
/// there is none or `rotation` asks for one. A new token replaces the
/// file atomically (mode 0600); a kept file with a wider mode is set to
/// 0600.
///
/// # Errors
///
/// The file cannot be read or written, or it holds no token (rotate to
/// replace it).
pub fn pairing_token(path: &Path, rotation: Rotation) -> anyhow::Result<PairingToken> {
    match rotation {
        Rotation::Keep => match std::fs::read_to_string(path) {
            Ok(text) => {
                let token = PairingToken::parse(text.trim()).with_context(|| {
                    format!(
                        "{} holds no pairing token: run `eukhe dashboard --rotate-token` to make a new one",
                        path.display()
                    )
                })?;
                let mode = std::fs::metadata(path)
                    .with_context(|| format!("read the mode of {}", path.display()))?
                    .permissions()
                    .mode();
                if mode & 0o077 != 0 {
                    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o600))
                        .with_context(|| format!("make {} private", path.display()))?;
                }
                Ok(token)
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => store_fresh(path),
            Err(error) => Err(error).with_context(|| format!("read {}", path.display())),
        },
        Rotation::Rotate => store_fresh(path),
    }
}

/// Make a new token and store it at `path`.
fn store_fresh(path: &Path) -> anyhow::Result<PairingToken> {
    let token = PairingToken::fresh()?;
    write_private(path, format!("{}\n", token.secret_hex()).as_bytes())?;
    Ok(token)
}

/// Write `contents` to `path` with mode 0600: a new file in the same
/// folder, synced, then renamed over `path`, so a reader sees the old
/// file or the new one, never a part.
///
/// # Errors
///
/// The folder cannot be made, or the file cannot be written or renamed.
pub(crate) fn write_private(path: &Path, contents: &[u8]) -> anyhow::Result<()> {
    let folder = path
        .parent()
        .with_context(|| format!("{} has no folder", path.display()))?;
    std::fs::create_dir_all(folder).with_context(|| format!("create {}", folder.display()))?;
    let name = path
        .file_name()
        .with_context(|| format!("{} has no file name", path.display()))?
        .to_string_lossy();
    let staging = folder.join(format!(".{name}.{}.tmp", uuid::Uuid::new_v4()));
    let written = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&staging)
        .and_then(|mut file| {
            file.write_all(contents)?;
            file.sync_all()
        })
        .and_then(|()| std::fs::rename(&staging, path));
    if let Err(error) = written {
        if let Err(cleanup) = std::fs::remove_file(&staging) {
            if cleanup.kind() != std::io::ErrorKind::NotFound {
                tracing::warn!(path = %staging.display(), error = %cleanup, "could not remove a staging file");
            }
        }
        return Err(error).with_context(|| format!("write {}", path.display()));
    }
    Ok(())
}

/// Write the page that opens `url` (which holds the token) in the
/// browser to `path`, mode 0600: the browser gets the page's path, so the
/// token never goes into a process's arguments, which other users of the
/// machine can read.
///
/// # Errors
///
/// The page cannot be written.
pub fn opener_page(path: &Path, url: &str) -> anyhow::Result<()> {
    let url = url
        .replace('&', "&amp;")
        .replace('"', "&quot;")
        .replace('<', "&lt;");
    let page = format!(
        "<!doctype html>\n<meta charset=\"utf-8\">\n<meta name=\"referrer\" content=\"no-referrer\">\n<meta http-equiv=\"refresh\" content=\"0;url={url}\">\n<title>eukhe dashboard</title>\n<a href=\"{url}\">Open the eukhe dashboard</a>\n"
    );
    write_private(path, page.as_bytes())
}

/// Why a socket's pairing failed: the text of its `unpaired` frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Refusal {
    /// The first frame was not a pairing, or it named no token.
    Missing,
    /// The token is not the current one (rotated, or never issued).
    Wrong,
    /// The server has no current token to compare with.
    Unset,
}

impl Refusal {
    /// The error the tab shows. It never holds a token.
    pub(crate) fn error(self) -> &'static str {
        match self {
            Refusal::Missing => {
                "pairing needed: open the link that `eukhe dashboard` prints"
            }
            Refusal::Wrong => {
                "this pairing link is not valid any more: open the link that `eukhe dashboard` prints"
            }
            Refusal::Unset => {
                "the dashboard has no pairing token: restart `eukhe dashboard`"
            }
        }
    }
}

/// Whether `presented` is the current token stored at `path`. A missing
/// or damaged file admits nothing.
pub(crate) async fn admits(path: &Path, presented: &PairingToken) -> Result<(), Refusal> {
    let stored = match tokio::fs::read_to_string(path).await {
        Ok(text) => PairingToken::parse(text.trim()),
        Err(error) => {
            tracing::warn!(path = %path.display(), %error, "could not read the pairing token");
            None
        }
    };
    let Some(current) = stored else {
        tracing::warn!(path = %path.display(), "the pairing token file holds no token");
        return Err(Refusal::Unset);
    };
    if current.same(presented) {
        Ok(())
    } else {
        Err(Refusal::Wrong)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testing::{compare, Rng, Scenario};
    use crate::{DashboardConfig, Port};
    use eukhe_tui::saved_sessions::DaemonLauncher;
    use futures::{SinkExt, StreamExt};
    use serde_json::{json, Value};
    use std::collections::HashMap;
    use std::fmt::Write as _;
    use std::future::Future;
    use std::io::{BufRead, BufReader};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    use std::time::Duration;
    use tokio_tungstenite::tungstenite::client::IntoClientRequest;
    use tokio_tungstenite::tungstenite::Message;

    type Socket = tokio_tungstenite::WebSocketStream<tokio::net::TcpStream>;

    const DEADLINE: Duration = Duration::from_secs(20);

    /// The daemon is up (the counting socket).
    struct Up;

    impl DaemonLauncher for Up {
        fn ensure(&self) -> impl Future<Output = anyhow::Result<()>> + Send {
            std::future::ready(Ok(()))
        }
    }

    /// A daemon that greets each connection, answers every command with
    /// no sessions, and counts the `list_saved_sessions` commands (what a
    /// tab's `sessions` frame runs).
    fn counting_daemon(socket_path: &Path) -> Arc<AtomicUsize> {
        let listener = std::os::unix::net::UnixListener::bind(socket_path).expect("bind");
        let listed = Arc::new(AtomicUsize::new(0));
        let counter = Arc::clone(&listed);
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(stream) = stream else { break };
                let counter = Arc::clone(&counter);
                std::thread::spawn(move || {
                    let mut writer = stream.try_clone().expect("clone");
                    let hello = json!({
                        "type": "daemon_hello",
                        "protocol": { "name": "eukhe.daemon", "version": 7 },
                        "serverCapabilities": [],
                        "clientId": "bridge",
                    });
                    writeln!(writer, "{hello}").expect("greet");
                    for line in BufReader::new(stream).lines() {
                        let Ok(line) = line else { break };
                        let Ok(envelope) = serde_json::from_str::<Value>(&line) else {
                            continue;
                        };
                        let kind = envelope["command"]["type"].clone();
                        if kind == "list_saved_sessions" {
                            counter.fetch_add(1, Ordering::SeqCst);
                        }
                        let response = json!({
                            "type": "response", "id": envelope["id"], "command": kind,
                            "success": true, "data": { "sessions": [] },
                        });
                        if writeln!(writer, "{response}").is_err() {
                            break;
                        }
                    }
                });
            }
        });
        listed
    }

    /// The next text frame of the server; `None` once it closed the
    /// socket.
    async fn next_text(socket: &mut Socket) -> Option<Value> {
        loop {
            match tokio::time::timeout(DEADLINE, socket.next())
                .await
                .expect("a frame in time")
            {
                Some(Ok(Message::Text(text))) => {
                    return Some(serde_json::from_str(text.as_str()).expect("JSON frame"))
                }
                Some(Ok(Message::Close(_)) | Err(_)) | None => return None,
                Some(Ok(
                    Message::Binary(_) | Message::Ping(_) | Message::Pong(_) | Message::Frame(_),
                )) => {}
            }
        }
    }

    /// A tab's socket from the served page; `first` is its first frame.
    async fn open_with(port: u16, first: &Value) -> Socket {
        let stream = tokio::net::TcpStream::connect(("127.0.0.1", port))
            .await
            .expect("connect");
        let mut request = format!("ws://127.0.0.1:{port}/api/ws")
            .into_client_request()
            .expect("request");
        request.headers_mut().append(
            "origin",
            format!("http://127.0.0.1:{port}").parse().expect("origin"),
        );
        let (mut socket, _) = tokio_tungstenite::client_async(request, stream)
            .await
            .expect("the socket");
        socket
            .send(Message::text(first.to_string()))
            .await
            .expect("send");
        socket
    }

    /// The bridge to bend/dash.bend: rotations, connections that present
    /// a current, an old, a never-made or no token, and frames, through
    /// the real server and token file; what paired, ran, was refused or
    /// reached nothing. A frame counts as run only when its command
    /// reached the daemon.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    #[allow(clippy::too_many_lines)] // One scenario's whole run, event by event.
    async fn the_gate_pairs_as_its_model() {
        let mut rng = Rng(0xda5_a0f1);
        let mut scenarios = Vec::new();
        for at in 0..40 {
            let dir = tempfile::tempdir().expect("tempdir");
            let token_path = dir.path().join("dashboard-token");
            let mut made = vec![pairing_token(&token_path, Rotation::Keep).expect("made")];
            let listed = counting_daemon(&dir.path().join("daemon.sock"));
            let listener = crate::bind(Port::Free).await.expect("bind");
            let port = listener.local_addr().expect("address").port();
            let config = DashboardConfig {
                socket_path: dir.path().join("daemon.sock"),
                session_dir: dir.path().to_path_buf(),
                new_session_cwd: dir.path().to_path_buf(),
                create_config: serde_json::Map::new(),
                allowed_hosts: Vec::new(),
                token_path: token_path.clone(),
            };
            let server = tokio::spawn(crate::serve(listener, config, Up));
            let mut sockets: HashMap<u64, Socket> = HashMap::new();
            let mut events = String::new();
            let mut transcript = String::new();
            let mut id = 0_u64;
            for _ in 0..rng.range(1, 10) {
                let before = listed.load(Ordering::SeqCst);
                let c = rng.below(4);
                let line = match rng.below(8) {
                    0 => {
                        made.push(pairing_token(&token_path, Rotation::Rotate).expect("rotate"));
                        writeln!(events, "r").expect("write");
                        "rot".to_string()
                    }
                    kind @ (1..=4) => {
                        sockets.remove(&c);
                        let newest = u64::try_from(made.len()).expect("count") - 1;
                        let shown = match kind {
                            1 | 2 => Some(newest),
                            3 => Some(rng.below(newest + 1)),
                            _ => match rng.below(2) {
                                0 => Some(100 + rng.below(3)),
                                _ => None,
                            },
                        };
                        let first = if let Some(t) = shown {
                            writeln!(events, "o {c} {t}").expect("write");
                            let hex = made.get(usize::try_from(t).expect("index")).map_or_else(
                                || {
                                    PairingToken([u8::try_from(t).expect("byte"); TOKEN_BYTES])
                                        .secret_hex()
                                },
                                PairingToken::secret_hex,
                            );
                            json!({ "op": "pair", "token": hex })
                        } else {
                            writeln!(events, "m {c}").expect("write");
                            json!({ "id": 0, "op": "sessions" })
                        };
                        let mut socket = open_with(port, &first).await;
                        let heard = next_text(&mut socket).await.expect("an answer");
                        if heard["type"] == "hello" {
                            sockets.insert(c, socket);
                            format!("p {c}")
                        } else {
                            assert_eq!(
                                (heard["type"].clone(), next_text(&mut socket).await),
                                (json!("unpaired"), None)
                            );
                            format!("j {c}")
                        }
                    }
                    _ => {
                        writeln!(events, "f {c}").expect("write");
                        match sockets.get_mut(&c) {
                            None => format!("z {c}"),
                            Some(socket) => {
                                id += 1;
                                socket
                                    .send(Message::text(
                                        json!({ "id": id, "op": "sessions" }).to_string(),
                                    ))
                                    .await
                                    .expect("send");
                                let answer = loop {
                                    match next_text(socket).await {
                                        Some(frame)
                                            if frame["type"] == "reply" && frame["id"] == id =>
                                        {
                                            break format!("x {c}")
                                        }
                                        Some(frame) if frame["type"] == "unpaired" => {
                                            break format!("u {c}")
                                        }
                                        Some(_) => {}
                                        None => break format!("z {c}"),
                                    }
                                };
                                if !answer.starts_with('x') {
                                    sockets.remove(&c);
                                }
                                answer
                            }
                        }
                    }
                };
                let ran = listed.load(Ordering::SeqCst) - before;
                assert_eq!(
                    (ran, line.as_str()),
                    (usize::from(line.starts_with('x')), line.as_str()),
                    "a frame ran exactly when the daemon got its command"
                );
                writeln!(transcript, "{line}").expect("write");
            }
            server.abort();
            scenarios.push(Scenario {
                name: format!("{at}"),
                events,
                transcript,
            });
        }
        compare("bend/bridge_dash.bend", scenarios);
    }

    #[test]
    fn the_opener_page_is_private_and_redirects() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("dashboard-open.html");
        opener_page(&path, "http://127.0.0.1:8377/#token=ab").expect("written");
        assert_eq!(
            (
                std::fs::metadata(&path).expect("metadata").permissions().mode() & 0o777,
                std::fs::read_to_string(&path).expect("read"),
            ),
            (
                0o600,
                "<!doctype html>\n<meta charset=\"utf-8\">\n<meta name=\"referrer\" content=\"no-referrer\">\n<meta http-equiv=\"refresh\" content=\"0;url=http://127.0.0.1:8377/#token=ab\">\n<title>eukhe dashboard</title>\n<a href=\"http://127.0.0.1:8377/#token=ab\">Open the eukhe dashboard</a>\n".to_string()
            )
        );
    }

    #[test]
    fn a_token_is_kept_private_until_rotated() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("agent").join("dashboard-token");
        let first = pairing_token(&path, Rotation::Keep).expect("made");
        let mode = |path: &Path| {
            std::fs::metadata(path)
                .expect("metadata")
                .permissions()
                .mode()
                & 0o777
        };
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o644)).expect("chmod");
        let kept = pairing_token(&path, Rotation::Keep).expect("kept");
        let kept_mode = mode(&path);
        let rotated = pairing_token(&path, Rotation::Rotate).expect("rotated");
        let stored = std::fs::read_to_string(&path).expect("stored");
        let leftovers: Vec<_> = std::fs::read_dir(path.parent().expect("folder"))
            .expect("list")
            .map(|entry| entry.expect("entry").file_name())
            .collect();
        assert_eq!(
            (
                kept == first,
                kept_mode,
                rotated == first,
                mode(&path),
                stored,
                leftovers,
                format!("{rotated:?}"),
            ),
            (
                true,
                0o600,
                false,
                0o600,
                format!("{}\n", rotated.secret_hex()),
                vec![std::ffi::OsString::from("dashboard-token")],
                "PairingToken(..)".to_string(),
            )
        );
    }

    #[test]
    fn a_damaged_file_is_an_error_without_its_text() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("dashboard-token");
        std::fs::write(&path, "secret-but-not-a-token\n").expect("write");
        let error = format!(
            "{:#}",
            pairing_token(&path, Rotation::Keep).expect_err("damaged")
        );
        assert_eq!(
            error,
            format!(
                "{} holds no pairing token: run `eukhe dashboard --rotate-token` to make a new one",
                path.display()
            )
        );
    }

    #[test]
    fn only_64_hex_digits_spell_a_token() {
        let token = PairingToken([0xab; TOKEN_BYTES]);
        let hex = token.secret_hex();
        let parsed: Vec<Option<PairingToken>> = [
            hex.clone(),
            hex.to_uppercase(),
            hex[..62].to_string(),
            format!("{hex}0"),
            format!("{}zz", &hex[..62]),
            // Regression (laws/dashboard_policy.bend F1): a sign in a pair
            // spelled a byte ("+a" as 0x0a).
            format!("+a{}", &hex[2..]),
            format!("{}é", &hex[..62]),
            String::new(),
        ]
        .iter()
        .map(|text| PairingToken::parse(text))
        .collect();
        assert_eq!(
            parsed,
            [
                Some(token.clone()),
                Some(token),
                None,
                None,
                None,
                None,
                None,
                None
            ]
        );
    }

    #[tokio::test]
    async fn only_the_current_token_is_admitted() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("dashboard-token");
        let missing = admits(&path, &PairingToken([1; TOKEN_BYTES])).await;
        let first = pairing_token(&path, Rotation::Keep).expect("made");
        let before = admits(&path, &first).await;
        let second = pairing_token(&path, Rotation::Rotate).expect("rotated");
        assert_eq!(
            (
                missing,
                before,
                admits(&path, &first).await,
                admits(&path, &second).await
            ),
            (Err(Refusal::Unset), Ok(()), Err(Refusal::Wrong), Ok(()))
        );
    }
}
