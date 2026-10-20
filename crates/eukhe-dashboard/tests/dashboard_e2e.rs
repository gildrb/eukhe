//! The dashboard end to end against a scripted daemon socket: the server
//! answers the app's files and its WebSocket only to loopback (or allowed)
//! hosts and to its own origin (or the public origin a forwarder such as
//! poros declares); a tab's socket pairs with the current token (else it
//! hears `unpaired` and nothing runs), greets with `hello`, opens
//! the newest root session (create + attach), resumes from a cursor, sends
//! a message whose reply streams back as session events with cursors,
//! runs daemon commands for the bound session, hears approvals and
//! resyncs, reads the memory tree, and keeps events flowing while a
//! request waits.
#![cfg(unix)]

use std::future::Future;
use std::io::{BufRead, BufReader, Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{mpsc, Arc, Mutex};
use std::time::Duration;

use eukhe_dashboard::{DashboardConfig, Port};
use eukhe_tui::saved_sessions::DaemonLauncher;
use futures::{SinkExt, StreamExt};
use serde_json::{json, Value};
use tokio_tungstenite::tungstenite::client::IntoClientRequest;
use tokio_tungstenite::tungstenite::{self, Message};

/// The daemon is already up (the scripted socket).
struct Running;

impl DaemonLauncher for Running {
    fn ensure(&self) -> impl Future<Output = anyhow::Result<()>> + Send {
        std::future::ready(Ok(()))
    }
}

/// No daemon can start; counts the bridges that tried.
struct Down(Arc<AtomicUsize>);

impl DaemonLauncher for Down {
    fn ensure(&self) -> impl Future<Output = anyhow::Result<()>> + Send {
        self.0.fetch_add(1, Ordering::SeqCst);
        std::future::ready(Err(anyhow::anyhow!("no daemon here")))
    }
}

/// The daemon is already up; counts the bridges that started.
struct Counted(Arc<AtomicUsize>);

impl DaemonLauncher for Counted {
    fn ensure(&self) -> impl Future<Output = anyhow::Result<()>> + Send {
        self.0.fetch_add(1, Ordering::SeqCst);
        std::future::ready(Ok(()))
    }
}

const DEADLINE: Duration = Duration::from_secs(20);

/// The pairing token [`config`] stores.
const TOKEN: &str = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

fn write_json(writer: &mut UnixStream, value: &Value) {
    let mut line = serde_json::to_string(value).expect("serialize");
    line.push('\n');
    writer.write_all(line.as_bytes()).expect("write");
    writer.flush().expect("flush");
}

fn assistant(text: &str) -> Value {
    json!({
        "role": "assistant",
        "content": [
            { "type": "thinking", "thinking": "consider" },
            { "type": "text", "text": text },
        ],
        "api": "scripted",
        "provider": "scripted",
        "model": "faux-1",
        "usage": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": "stop",
        "timestamp": 2,
    })
}

fn tree_status() -> Value {
    json!({
        "messages": 2, "lines": 1, "viewBytes": 20, "unsummarized": 0,
        "running": 0, "model": null, "lastError": null,
    })
}

/// One `session_event` frame of the bound session `s1` at `sequence`.
fn session_event(sequence: u64, payload: &Value) -> Value {
    json!({
        "type": "session_event", "activeSessionId": "s1", "event": payload,
        "meta": { "sequence": sequence },
    })
}

/// The session's state and summary as the scripted attach answers them.
fn state() -> Value {
    json!({ "isStreaming": false, "cwd": "/", "sessionName": null })
}

fn summary() -> Value {
    json!({ "isStreaming": false, "isRunningTools": false })
}

fn transcript() -> Value {
    json!([{ "role": "user", "content": "hi", "timestamp": 1 }])
}

/// The scripted daemon: every connection is greeted and answered; every
/// command lands in `seen`. The answers of the command types in
/// `held_types` are not written but land in `held_answers`, for the test
/// to write when it wants. A prompt's reply streams as events after its
/// answer; an attach
/// with a resume cursor has two events in flight ahead of its answer (one
/// the snapshot holds, one after it).
struct ScriptedDaemon {
    seen: mpsc::Receiver<Value>,
    held_answers: mpsc::Receiver<Value>,
    /// The newest connection.
    writer: Arc<Mutex<Option<UnixStream>>>,
}

impl ScriptedDaemon {
    fn start(socket_path: &Path, held_types: &'static [&'static str]) -> Self {
        let listener = UnixListener::bind(socket_path).expect("bind daemon");
        let (seen_sender, seen) = mpsc::channel();
        let (answer_sender, held_answers) = mpsc::channel();
        let writer = Arc::new(Mutex::new(None));
        let newest = Arc::clone(&writer);
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(stream) = stream else { break };
                let mut connection_writer = stream.try_clone().expect("clone");
                *newest.lock().expect("writer") = Some(stream.try_clone().expect("clone"));
                let seen = seen_sender.clone();
                let answers = answer_sender.clone();
                std::thread::spawn(move || {
                    serve_connection(stream, &mut connection_writer, held_types, &seen, &answers);
                });
            }
        });
        Self {
            seen,
            held_answers,
            writer,
        }
    }

    /// Write one frame on the newest connection.
    fn write(&self, value: &Value) {
        let mut writer = self.writer.lock().expect("writer");
        write_json(writer.as_mut().expect("a bridge connected"), value);
    }

    fn next_command(&self) -> Value {
        self.seen
            .recv_timeout(DEADLINE)
            .expect("a command reached the daemon")
    }
}

fn serve_connection(
    stream: UnixStream,
    writer: &mut UnixStream,
    held_types: &[&str],
    seen: &mpsc::Sender<Value>,
    answers: &mpsc::Sender<Value>,
) {
    write_json(
        writer,
        &json!({
            "type": "daemon_hello",
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "serverCapabilities": ["memory", "memory_tree", "shell_approval"],
            "clientId": "mock",
        }),
    );
    for line in BufReader::new(stream).lines() {
        let Ok(line) = line else { break };
        let Ok(envelope) = serde_json::from_str::<Value>(line.trim()) else {
            continue;
        };
        let id = envelope["id"].as_str().unwrap_or_default().to_string();
        let command = envelope["command"].clone();
        let command_type = command["type"].as_str().unwrap_or_default().to_string();
        if seen.send(command.clone()).is_err() {
            break;
        }
        if command_type == "attach" && !command["resumeCursor"].is_null() {
            write_json(writer, &session_event(3, &json!({ "type": "turn_start" })));
            write_json(writer, &session_event(4, &json!({ "type": "agent_start" })));
        }
        let response = json!({
            "type": "response", "id": id, "command": command_type,
            "success": true, "data": daemon_answer(&command),
        });
        if held_types.contains(&command_type.as_str()) {
            if answers.send(response).is_err() {
                break;
            }
            continue;
        }
        write_json(writer, &response);
        if command_type == "prompt" {
            for (sequence, payload) in [
                (4, json!({ "type": "agent_start" })),
                (
                    5,
                    json!({ "type": "message_start", "message": assistant("") }),
                ),
                (
                    6,
                    json!({
                        "type": "message_update",
                        "message": assistant("hel"),
                        "assistantMessageEvent": { "type": "text_delta", "delta": "hel" },
                    }),
                ),
                (
                    7,
                    json!({ "type": "message_end", "message": assistant("hello") }),
                ),
                (8, json!({ "type": "agent_end", "messages": [] })),
            ] {
                write_json(writer, &session_event(sequence, &payload));
            }
        }
    }
}

/// The scripted daemon's answer data to one command.
fn daemon_answer(command: &Value) -> Value {
    match command["type"].as_str().unwrap_or_default() {
        "list_saved_sessions" => json!({ "sessions": [
                {
                    "path": "/s/newest.jsonl", "id": "newest", "cwd": "/",
                    "rlmDepth": 0, "parentSessionPath": null,
                    "modified": "2026-10-15T08:00:00Z", "name": null, "firstMessage": "hi",
                },
                {
                    "path": "/s/child.jsonl", "id": "child", "cwd": "/",
                    "rlmDepth": 1, "parentSessionPath": "/s/newest.jsonl",
                    "modified": "2026-10-15T09:00:00Z", "name": null, "firstMessage": "sub",
                },
            ] }),
        "create" => json!({
            "activeSessionId": "s1", "sessionId": "newest", "sessionFile": "/s/newest.jsonl",
        }),
        "attach" => {
            let cursor = json!({ "generation": "g1", "sequence": 3 });
            let replay = match command["resumeCursor"]["sequence"].as_u64() {
                Some(3) | None => "complete",
                Some(_) => "unavailable",
            };
            json!({
                "activeSessionId": "s1",
                "snapshot": {
                    "activeSessionId": "s1",
                    "summary": summary(),
                    "state": state(),
                    "messages": transcript(),
                    "lastEventSequence": 3,
                    "lastEventCursor": cursor,
                    "children": [],
                },
                "replay": { "status": replay, "toSequence": 3 },
                "lastEventSequence": 3,
                "lastEventCursor": cursor,
            })
        }
        "get_memory_tree" if command["node"].is_null() => json!({ "tree": {
                "status": tree_status(),
                "node": null,
                "level": { "kind": "lines", "nodes": [{
                    "id": 0, "count": 2,
                    "firstDate": "2026-10-15T10:00:00.000+02:00",
                    "lastDate": "2026-10-15T10:00:05.000+02:00",
                    "kinds": [{ "kind": "talk", "count": 1 }, { "kind": "user", "count": 1 }],
                    "summary": "user: hi\ntalk: hello",
                }] },
            } }),
        "get_memory_tree" => json!({ "tree": {
                "status": tree_status(),
                "node": command["node"],
                "level": { "kind": "message", "message": {
                    "id": 0, "kind": "user", "date": "2026-10-15T10:00:00.000+02:00", "text": "hi",
                } },
            } }),
        "get_session_stats" => {
            json!({ "tokens": { "total": 42 }, "for": command["activeSessionId"] })
        }
        // The worker writes the export where `outputPath` says.
        kind @ ("export_html" | "export_jsonl") => {
            let path = command["outputPath"].as_str().expect("an output path");
            let session = command["activeSessionId"].as_str().unwrap_or_default();
            std::fs::write(path, format!("{kind} of {session}")).expect("write the export");
            json!({ "path": path })
        }
        _ => json!({}),
    }
}

/// One plain HTTP/1.1 GET under `host` with extra header lines: the
/// status line, the headers (lowercase), and the body bytes.
fn get(port: u16, path: &str, host: &str, extra: &str) -> (String, String, Vec<u8>) {
    let mut stream = std::net::TcpStream::connect(("127.0.0.1", port)).expect("connect");
    stream.set_read_timeout(Some(DEADLINE)).expect("timeout");
    write!(
        stream,
        "GET {path} HTTP/1.1\r\nHost: {host}\r\n{extra}Connection: close\r\n\r\n"
    )
    .expect("request");
    let mut response = Vec::new();
    stream.read_to_end(&mut response).expect("response");
    let split = response
        .windows(4)
        .position(|window| window == b"\r\n\r\n")
        .expect("head");
    let head = String::from_utf8(response[..split].to_vec()).expect("UTF-8 head");
    let (status, headers) = head.split_once("\r\n").expect("status");
    (
        status.to_string(),
        headers.to_lowercase(),
        response[split + 4..].to_vec(),
    )
}

async fn get_async(
    port: u16,
    path: &'static str,
    host: String,
    extra: String,
) -> (String, String, Vec<u8>) {
    tokio::task::spawn_blocking(move || get(port, path, &host, &extra))
        .await
        .expect("get")
}

fn header<'a>(headers: &'a str, name: &str) -> Option<&'a str> {
    headers
        .lines()
        .find_map(|line| line.strip_prefix(name)?.strip_prefix(": "))
}

type Socket = tokio_tungstenite::WebSocketStream<tokio::net::TcpStream>;

/// Open the bridge's socket with `host` in the request (the connection
/// goes to loopback) and the extra `headers` (`origin`, forwarder headers).
async fn upgrade(
    port: u16,
    host: &str,
    headers: &[(&'static str, &str)],
) -> Result<Socket, tungstenite::Error> {
    let stream = tokio::net::TcpStream::connect(("127.0.0.1", port))
        .await
        .expect("connect");
    let mut request = format!("ws://{host}/api/ws")
        .into_client_request()
        .expect("request");
    for (name, value) in headers {
        request
            .headers_mut()
            .append(*name, value.parse().expect("header value"));
    }
    tokio_tungstenite::client_async(request, stream)
        .await
        .map(|(socket, _)| socket)
}

/// A tab of the app as a browser opens it from the served page.
async fn open_tab(port: u16) -> Socket {
    upgrade(
        port,
        &format!("127.0.0.1:{port}"),
        &[("origin", &format!("http://127.0.0.1:{port}"))],
    )
    .await
    .expect("the bridge's socket")
}

async fn next_frame(socket: &mut Socket) -> Value {
    loop {
        let message = tokio::time::timeout(DEADLINE, socket.next())
            .await
            .expect("a frame in time")
            .expect("the socket is open")
            .expect("a frame");
        if let Message::Text(text) = message {
            return serde_json::from_str(text.as_str()).expect("JSON frame");
        }
    }
}

/// Pair with [`TOKEN`], then the `hello` greeting, as the first frame the
/// server sends.
async fn pair(socket: &mut Socket) {
    send(socket, &json!({ "op": "pair", "token": TOKEN })).await;
    let hello = next_frame(socket).await;
    let build = hello["build"].as_str().unwrap_or_default().to_string();
    assert!(build.contains("+web."), "{hello}");
    assert_eq!(
        hello,
        json!({
            "type": "hello", "protocol": 3, "build": build,
            "ops": ["sessions", "open", "new", "prompt", "abort", "memory", "run", "export", "delete", "rename"],
        })
    );
}

async fn send(socket: &mut Socket, frame: &Value) {
    socket
        .send(Message::text(frame.to_string()))
        .await
        .expect("send");
}

/// Send a request and wait for its answer; the frames pushed meanwhile
/// are dropped.
async fn request(socket: &mut Socket, frame: Value) -> Value {
    send(socket, &frame).await;
    loop {
        let reply = next_frame(socket).await;
        if reply["id"] == frame["id"] && matches!(reply["type"].as_str(), Some("reply" | "failure"))
        {
            return reply;
        }
    }
}

/// Serve the dashboard on a free loopback port; answers the port.
async fn serve(config: DashboardConfig, launcher: impl DaemonLauncher) -> u16 {
    let http = eukhe_dashboard::bind(Port::Free).await.expect("bind");
    let address = http.local_addr().expect("address");
    assert!(address.ip().is_loopback(), "{address}");
    tokio::spawn(eukhe_dashboard::serve(http, config, launcher));
    address.port()
}

/// The configuration of a dashboard in `dir`, whose pairing token is
/// [`TOKEN`].
fn config(dir: &Path, allowed_hosts: Vec<String>) -> DashboardConfig {
    let token_path = dir.join("dashboard-token");
    std::fs::write(&token_path, format!("{TOKEN}\n")).expect("store the token");
    DashboardConfig {
        socket_path: dir.join("daemon.sock"),
        session_dir: dir.join("sessions"),
        new_session_cwd: dir.to_path_buf(),
        create_config: serde_json::Map::from_iter([("script".to_string(), json!("/x.json"))]),
        allowed_hosts,
        token_path,
    }
}

/// A tab bound to the newest session (`s1`); the daemon's commands so far
/// are consumed.
async fn bound_tab(port: u16, daemon: &ScriptedDaemon) -> Socket {
    let mut socket = open_tab(port).await;
    pair(&mut socket).await;
    let opened = request(&mut socket, json!({ "id": 1, "op": "open" })).await;
    assert_eq!(opened["type"], "reply", "{opened}");
    while daemon.seen.try_recv().is_ok() {}
    socket
}

#[tokio::test]
async fn the_app_files_load_on_loopback_with_their_types_and_tags() {
    let dir = tempfile::tempdir().expect("tempdir");
    let port = serve(config(dir.path(), Vec::new()), Running).await;
    let host = format!("127.0.0.1:{port}");

    let (status, headers, _) = get_async(port, "/", host.clone(), String::new()).await;
    assert_eq!(status, "HTTP/1.1 200 OK");
    assert_eq!(
        header(&headers, "content-type"),
        Some("text/html; charset=utf-8")
    );
    assert_eq!(
        header(&headers, "content-security-policy"),
        Some("default-src 'self'; script-src 'self'; style-src 'self'; img-src 'self' data: blob:; font-src 'self'; connect-src 'self'; worker-src 'self'; manifest-src 'self'; base-uri 'none'; frame-ancestors 'none'")
    );
    assert_eq!(header(&headers, "cache-control"), Some("no-cache"));

    let (status, headers, body) = get_async(
        port,
        "/eukhe/fonts/inter.woff2",
        host.clone(),
        String::new(),
    )
    .await;
    assert_eq!(status, "HTTP/1.1 200 OK");
    assert_eq!(header(&headers, "content-type"), Some("font/woff2"));
    assert_eq!(&body[..4], b"wOF2");
    let (_, headers, body) = get_async(
        port,
        "/eukhe/icons/icon-192.png",
        host.clone(),
        String::new(),
    )
    .await;
    assert_eq!(header(&headers, "content-type"), Some("image/png"));
    assert_eq!(&body[..8], b"\x89PNG\r\n\x1a\n");
    let (_, headers, _) =
        get_async(port, "/fonts/inter-OFL.txt", host.clone(), String::new()).await;
    assert_eq!(
        header(&headers, "content-type"),
        Some("text/plain; charset=utf-8")
    );

    // An unchanged file revalidates to 304.
    let etag = header(&headers, "etag").expect("an entity tag").to_string();
    let (status, _, body) = get_async(
        port,
        "/fonts/inter-OFL.txt",
        host.clone(),
        format!("If-None-Match: {etag}\r\n"),
    )
    .await;
    assert_eq!(
        (status.as_str(), body.len()),
        ("HTTP/1.1 304 Not Modified", 0)
    );

    let (status, _, _) = get_async(port, "/etc/passwd", host, String::new()).await;
    assert_eq!(status, "HTTP/1.1 404 Not Found");
}

/// The HTTP status an upgrade was refused with; panics on acceptance.
fn refused(result: Result<Socket, tungstenite::Error>) -> u16 {
    match result {
        Err(tungstenite::Error::Http(response)) => response.status().as_u16(),
        Err(error) => panic!("expected an HTTP refusal, got {error}"),
        Ok(_) => panic!("the upgrade was accepted"),
    }
}

/// An accepted socket of a dashboard without a daemon: `hello`, then why.
async fn expect_accepted(result: Result<Socket, tungstenite::Error>) {
    let mut socket = result.expect("the page's own socket");
    pair(&mut socket).await;
    assert_eq!(
        next_frame(&mut socket).await,
        json!({
            "type": "unavailable",
            "error": "start the eukhe daemon: no daemon here",
        })
    );
}

#[tokio::test]
async fn the_socket_and_files_answer_only_their_own_origin_and_hosts() {
    let dir = tempfile::tempdir().expect("tempdir");
    let bridges = Arc::new(AtomicUsize::new(0));
    let port = serve(
        config(dir.path(), vec!["box.tail1234.ts.net".to_string()]),
        Down(Arc::clone(&bridges)),
    )
    .await;
    let loopback = format!("127.0.0.1:{port}");
    let rebound = format!("evil.example:{port}");

    // DNS rebinding: a foreign name that resolves to loopback.
    let (status, _, _) = get_async(port, "/", rebound.clone(), String::new()).await;
    assert_eq!(status, "HTTP/1.1 403 Forbidden");
    let (status, _, _) =
        get_async(port, "/", "box.tail1234.ts.net".to_string(), String::new()).await;
    assert_eq!(status, "HTTP/1.1 200 OK");

    let local_origin = format!("http://localhost:{port}");
    let rebound_origin = format!("http://{rebound}");
    let statuses = [
        // Cross-site WebSocket hijacking: another site's page.
        refused(upgrade(port, &loopback, &[("origin", "http://evil.example")]).await),
        refused(upgrade(port, &loopback, &[("origin", &local_origin)]).await),
        refused(upgrade(port, &loopback, &[]).await),
        refused(upgrade(port, &rebound, &[("origin", &rebound_origin)]).await),
        refused(
            upgrade(
                port,
                "box.tail1234.ts.net",
                &[("origin", "https://evil.example")],
            )
            .await,
        ),
    ];
    assert_eq!(statuses, [403, 403, 403, 403, 403]);
    assert_eq!(
        bridges.load(Ordering::SeqCst),
        0,
        "no refused socket reached a bridge"
    );

    // The page's own origin, on loopback and under the allowed name.
    let own_origin = format!("http://{loopback}");
    expect_accepted(upgrade(port, &loopback, &[("origin", &own_origin)]).await).await;
    expect_accepted(
        upgrade(
            port,
            "box.tail1234.ts.net",
            &[("origin", "https://box.tail1234.ts.net")],
        )
        .await,
    )
    .await;
    assert_eq!(bridges.load(Ordering::SeqCst), 2);
}

/// What poros sends: `Host` rewritten to the local address, the browser's
/// `Origin` (the public HTTPS authority), and that authority in
/// `X-Forwarded-Host`. The page behind it connects with no `--allow-host`;
/// another site's page behind it does not.
#[tokio::test]
async fn a_socket_behind_poros_answers_only_the_declared_public_origin() {
    let dir = tempfile::tempdir().expect("tempdir");
    let bridges = Arc::new(AtomicUsize::new(0));
    let port = serve(config(dir.path(), Vec::new()), Down(Arc::clone(&bridges))).await;
    let loopback = format!("127.0.0.1:{port}");
    let public = "box.tail1234.ts.net:46101";
    let public_origin = format!("https://{public}");

    let statuses = [
        // Another site's page behind the forwarder.
        refused(
            upgrade(
                port,
                &loopback,
                &[
                    ("origin", "https://evil.example"),
                    ("x-forwarded-host", public),
                ],
            )
            .await,
        ),
        // The public name on another port.
        refused(
            upgrade(
                port,
                &loopback,
                &[
                    ("origin", "https://box.tail1234.ts.net:9"),
                    ("x-forwarded-host", public),
                ],
            )
            .await,
        ),
        // Only the nearest forwarder's name counts.
        refused(
            upgrade(
                port,
                &loopback,
                &[
                    ("origin", &public_origin),
                    ("x-forwarded-host", public),
                    ("x-forwarded-host", "proxy.internal"),
                ],
            )
            .await,
        ),
        // No forwarder named it.
        refused(upgrade(port, &loopback, &[("origin", &public_origin)]).await),
    ];
    assert_eq!(statuses, [403, 403, 403, 403]);
    assert_eq!(bridges.load(Ordering::SeqCst), 0);

    expect_accepted(
        upgrade(
            port,
            &loopback,
            &[
                ("origin", &public_origin),
                ("x-forwarded-host", public),
                ("x-forwarded-proto", "https"),
            ],
        )
        .await,
    )
    .await;
    assert_eq!(bridges.load(Ordering::SeqCst), 1);
}

#[tokio::test]
#[allow(clippy::too_many_lines)] // One tab's whole session, in order.
async fn a_tab_chats_and_browses_the_memory_through_the_daemon() {
    let dir = tempfile::tempdir().expect("tempdir");
    let daemon = ScriptedDaemon::start(&dir.path().join("daemon.sock"), &[]);
    let port = serve(config(dir.path(), Vec::new()), Running).await;
    let mut socket = open_tab(port).await;
    pair(&mut socket).await;

    // Open: the newest root session, created resident and attached.
    let opened = request(&mut socket, json!({ "id": 1, "op": "open", "path": null })).await;
    assert_eq!(
        opened,
        json!({ "type": "reply", "id": 1, "data": {
            "session": { "id": "newest", "path": "/s/newest.jsonl" },
            "state": state(),
            "summary": summary(),
            "messages": transcript(),
            "cursor": { "generation": "g1", "sequence": 3 },
            "replay": null,
        } })
    );
    assert_eq!(daemon.next_command()["type"], "list_saved_sessions");
    assert_eq!(
        daemon.next_command(),
        json!({
            "type": "create",
            "sessionPath": "/s/newest.jsonl",
            "config": {
                "script": "/x.json",
                "sessionDir": dir.path().join("sessions").display().to_string(),
            },
            "lifecycle": "resident",
        })
    );
    assert_eq!(
        daemon.next_command(),
        json!({
            "type": "attach",
            "activeSessionId": "s1",
            "capabilities": ["attach_snapshot", "event_sequence", "slim_attach", "elide_snapshot_images"],
        })
    );

    // A message with an image and the tab's admission id: accepted, and
    // its reply streams as events with their cursors (the answer and the
    // events travel independently, so either may come first).
    send(
        &mut socket,
        &json!({
            "id": 2, "op": "prompt", "text": "say hello", "mode": "steer",
            "admissionId": "tab-1", "images": [{ "data": "AA==", "mimeType": "image/png" }],
        }),
    )
    .await;
    let mut sent = Value::Null;
    let mut events = Vec::new();
    while sent.is_null() || events.last().map(|(kind, _)| kind) != Some(&json!("agent_end")) {
        let frame = next_frame(&mut socket).await;
        if frame["type"] == "reply" {
            sent = frame;
            continue;
        }
        assert_eq!(frame["type"], "event", "{frame}");
        if frame["event"]["type"] == "message_end" {
            assert_eq!(frame["event"]["message"]["content"][1]["text"], "hello");
        }
        events.push((frame["event"]["type"].clone(), frame["cursor"].clone()));
    }
    assert_eq!(sent, json!({ "type": "reply", "id": 2, "data": null }));
    assert_eq!(
        daemon.next_command(),
        json!({
            "type": "prompt",
            "activeSessionId": "s1",
            "message": "say hello",
            "images": [{ "type": "image", "data": "AA==", "mimeType": "image/png" }],
            "streamingBehavior": "steer",
            "queueIfBusy": true,
            "admissionId": "tab-1",
        })
    );
    let cursor = |sequence: u64| json!({ "generation": "g1", "sequence": sequence });
    assert_eq!(
        events,
        [
            (json!("agent_start"), cursor(4)),
            (json!("message_start"), cursor(5)),
            (json!("message_update"), cursor(6)),
            (json!("message_end"), cursor(7)),
            (json!("agent_end"), cursor(8)),
        ]
    );

    // The memory: the view's lines, then one opened down to its message.
    let top = request(
        &mut socket,
        json!({ "id": 3, "op": "memory", "node": null }),
    )
    .await;
    assert_eq!(
        top["data"]["tree"]["level"]["nodes"][0]["summary"],
        "user: hi\ntalk: hello"
    );
    let leaf = request(
        &mut socket,
        json!({ "id": 4, "op": "memory", "node": { "id": 0, "count": 1 } }),
    )
    .await;
    assert_eq!(
        leaf["data"]["tree"]["level"],
        json!({ "kind": "message", "message": {
            "id": 0, "kind": "user", "date": "2026-10-15T10:00:00.000+02:00", "text": "hi",
        } })
    );

    // Stop, and a malformed request answers a failure under its id.
    let stopped = request(&mut socket, json!({ "id": 5, "op": "abort" })).await;
    assert_eq!(stopped, json!({ "type": "reply", "id": 5, "data": null }));
    let bad = request(&mut socket, json!({ "id": 6, "op": "launch" })).await;
    assert_eq!(bad["type"], "failure");

    // The session closes: the tab hears it and is no longer bound.
    daemon.write(&json!({ "type": "session_closed", "activeSessionId": "s1", "reason": "killed" }));
    assert_eq!(
        next_frame(&mut socket).await,
        json!({ "type": "resync", "reason": "the session closed (killed)" })
    );
    let unbound = request(&mut socket, json!({ "id": 7, "op": "abort" })).await;
    assert_eq!(
        unbound,
        json!({ "type": "failure", "id": 7, "error": "no session is open" })
    );
}

#[tokio::test]
async fn run_reaches_the_daemon_for_the_bound_session_only_when_allowed() {
    let dir = tempfile::tempdir().expect("tempdir");
    let daemon = ScriptedDaemon::start(&dir.path().join("daemon.sock"), &[]);
    let port = serve(config(dir.path(), Vec::new()), Running).await;
    let mut socket = open_tab(port).await;
    pair(&mut socket).await;

    let early = request(
        &mut socket,
        json!({ "id": 1, "op": "run", "command": { "type": "get_session_stats" } }),
    )
    .await;
    assert_eq!(
        early,
        json!({ "type": "failure", "id": 1, "error": "no session is open" })
    );
    request(&mut socket, json!({ "id": 2, "op": "open" })).await;
    while daemon.seen.try_recv().is_ok() {}

    // Allowed: the bridge's session id replaces the tab's, and the
    // daemon's data comes back verbatim.
    let stats = request(
        &mut socket,
        json!({ "id": 3, "op": "run", "command": {
            "type": "get_session_stats", "activeSessionId": "someone-else", "id": "x",
        } }),
    )
    .await;
    assert_eq!(
        stats,
        json!({ "type": "reply", "id": 3, "data": { "tokens": { "total": 42 }, "for": "s1" } })
    );
    assert_eq!(
        daemon.next_command(),
        json!({ "type": "get_session_stats", "activeSessionId": "s1" })
    );

    // Refused: bridge-owned and daemon-wide commands never reach it.
    let mut failures = Vec::new();
    for (id, command) in [
        (4, json!({ "type": "shutdown" })),
        (5, json!({ "type": "prompt", "message": "sneak" })),
        (6, json!({ "type": "detach" })),
        (7, json!({ "type": "launch_missiles" })),
        (
            9,
            json!({ "type": "export_html", "outputPath": "/tmp/anywhere.html" }),
        ),
        (
            10,
            json!({ "type": "delete_saved_session", "sessionPath": "/s/newest.jsonl" }),
        ),
    ] {
        let reply = request(
            &mut socket,
            json!({ "id": id, "op": "run", "command": command }),
        )
        .await;
        failures.push(reply);
    }
    let unknown = failures[3]["error"]
        .as_str()
        .unwrap_or_default()
        .to_string();
    assert!(
        unknown.starts_with("read the \"launch_missiles\" command"),
        "{unknown}"
    );
    assert_eq!(
        failures,
        [
            json!({ "type": "failure", "id": 4, "error": "the dashboard does not run shutdown" }),
            json!({ "type": "failure", "id": 5, "error": "the dashboard does not run prompt" }),
            json!({ "type": "failure", "id": 6, "error": "the dashboard does not run detach" }),
            json!({ "type": "failure", "id": 7, "error": unknown }),
            json!({ "type": "failure", "id": 9, "error": "the dashboard does not run export_html" }),
            json!({ "type": "failure", "id": 10, "error": "the dashboard does not run delete_saved_session" }),
        ]
    );
    let queue = request(
        &mut socket,
        json!({ "id": 8, "op": "run", "command": { "type": "get_queue" } }),
    )
    .await;
    assert_eq!(queue, json!({ "type": "reply", "id": 8, "data": {} }));
    assert_eq!(
        daemon.next_command(),
        json!({ "type": "get_queue", "activeSessionId": "s1" }),
        "the refused commands never reached the daemon"
    );
}

/// A catalog command names its sessions itself: it reaches the daemon with
/// no session id (the supervisor answers for every session), even when
/// the tab sends one.
#[tokio::test]
async fn catalog_commands_go_without_a_session_id() {
    let dir = tempfile::tempdir().expect("tempdir");
    let daemon = ScriptedDaemon::start(&dir.path().join("daemon.sock"), &[]);
    let port = serve(config(dir.path(), Vec::new()), Running).await;
    let mut socket = bound_tab(port, &daemon).await;
    let renamed = request(
        &mut socket,
        json!({ "id": 2, "op": "run", "command": {
            "type": "rename_saved_session", "sessionPath": "/s/other.jsonl",
            "name": "Other", "activeSessionId": "spoofed",
        } }),
    )
    .await;
    assert_eq!(
        (renamed, daemon.next_command()),
        (
            json!({ "type": "reply", "id": 2, "data": {} }),
            json!({ "type": "rename_saved_session", "sessionPath": "/s/other.jsonl", "name": "Other" }),
        )
    );
}

/// Answer the held `list` with one live row for the newest session.
fn answer_list(daemon: &ScriptedDaemon, attached_clients: u32) {
    let held = daemon
        .held_answers
        .recv_timeout(DEADLINE)
        .expect("the held list");
    daemon.write(&json!({
        "type": "response", "id": held["id"], "command": "list", "success": true,
        "data": { "sessions": [
            { "sessionFile": "/s/other.jsonl", "activeSessionId": null, "attachedClients": 0 },
            {
                "sessionFile": "/s/newest.jsonl", "activeSessionId": "s1",
                "attachedClients": attached_clients,
            },
        ] },
    }));
}

/// Deleting a chat stops the worker that hosts it when no other window
/// has it open (the tab lets its own binding go first), then deletes the
/// file with no session id; a chat open in another window is refused and
/// nothing is stopped.
// The held list is answered from the test thread while the bridge runs.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn deleting_a_chat_stops_its_idle_worker_and_refuses_one_open_elsewhere() {
    let dir = tempfile::tempdir().expect("tempdir");
    let daemon = ScriptedDaemon::start(&dir.path().join("daemon.sock"), &["list"]);
    let port = serve(config(dir.path(), Vec::new()), Running).await;
    let mut socket = bound_tab(port, &daemon).await;
    let commands = |daemon: &ScriptedDaemon, count: usize| -> Vec<Value> {
        (0..count)
            .map(|_| {
                let mut command = daemon.next_command();
                command
                    .as_object_mut()
                    .expect("a command")
                    .remove("sessionDir");
                command
            })
            .collect()
    };
    let listed = json!({
        "type": "list_saved_sessions", "cwd": dir.path().display().to_string(), "scope": null,
    });
    let live = json!({ "type": "list", "all": true, "includeClientOwned": true });

    // This tab and one other window: refused, nothing stopped.
    send(
        &mut socket,
        &json!({ "id": 2, "op": "delete", "sessionId": "newest" }),
    )
    .await;
    answer_list(&daemon, 2);
    let refused = next_frame(&mut socket).await;
    assert_eq!(
        (refused, commands(&daemon, 2)),
        (
            json!({
                "type": "failure", "id": 2,
                "error": "the chat is open in another window: close it there first",
            }),
            vec![listed.clone(), live.clone()],
        )
    );

    // Only this tab: it lets go, the worker stops, the file goes.
    send(
        &mut socket,
        &json!({ "id": 3, "op": "delete", "sessionId": "newest" }),
    )
    .await;
    answer_list(&daemon, 1);
    let deleted = next_frame(&mut socket).await;
    assert_eq!(
        (deleted, commands(&daemon, 5)),
        (
            json!({ "type": "reply", "id": 3, "data": { "deleted": "newest" } }),
            vec![
                listed,
                live,
                json!({ "type": "detach", "activeSessionId": "s1" }),
                json!({ "type": "kill", "activeSessionId": "s1" }),
                json!({ "type": "delete_saved_session", "sessionPath": "/s/newest.jsonl" }),
            ],
        )
    );
}

/// A rename goes through the worker that hosts the chat (its file is the
/// worker's), and through the catalog for a saved file no worker hosts.
// The held list is answered from the test thread while the bridge runs.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_rename_goes_through_the_live_worker_else_the_catalog() {
    let dir = tempfile::tempdir().expect("tempdir");
    let daemon = ScriptedDaemon::start(&dir.path().join("daemon.sock"), &["list"]);
    let port = serve(config(dir.path(), Vec::new()), Running).await;
    let mut socket = bound_tab(port, &daemon).await;
    let mut sent = Vec::new();
    for (id, attached_clients, live) in [(2, 1, true), (3, 0, false)] {
        send(
            &mut socket,
            &json!({ "id": id, "op": "rename", "sessionId": "newest", "name": "Plans" }),
        )
        .await;
        let held = daemon
            .held_answers
            .recv_timeout(DEADLINE)
            .expect("the held list");
        let row = if live {
            json!({ "sessionFile": "/s/newest.jsonl", "activeSessionId": "s1", "attachedClients": attached_clients })
        } else {
            json!({ "sessionFile": "/s/newest.jsonl", "activeSessionId": null, "attachedClients": 0 })
        };
        daemon.write(&json!({
            "type": "response", "id": held["id"], "command": "list", "success": true,
            "data": { "sessions": [row] },
        }));
        let reply = next_frame(&mut socket).await;
        // list_saved_sessions, list, then the rename itself.
        let mut commands: Vec<Value> = (0..3).map(|_| daemon.next_command()).collect();
        let rename = commands.pop().expect("three commands");
        sent.push((reply, rename));
    }
    assert_eq!(
        sent,
        vec![
            (
                json!({ "type": "reply", "id": 2, "data": { "renamed": "newest", "name": "Plans" } }),
                json!({ "type": "set_session_name", "activeSessionId": "s1", "name": "Plans" }),
            ),
            (
                json!({ "type": "reply", "id": 3, "data": { "renamed": "newest", "name": "Plans" } }),
                json!({ "type": "rename_saved_session", "sessionPath": "/s/newest.jsonl", "name": "Plans" }),
            ),
        ]
    );
}

/// An export answers the file's bytes and leaves no file behind; the daemon
/// writes it into a private folder of the bridge's choosing.
#[tokio::test]
async fn an_export_answers_the_file_and_leaves_nothing_behind() {
    use base64::Engine as _;
    let dir = tempfile::tempdir().expect("tempdir");
    let daemon = ScriptedDaemon::start(&dir.path().join("daemon.sock"), &[]);
    let port = serve(config(dir.path(), Vec::new()), Running).await;
    let mut socket = bound_tab(port, &daemon).await;

    let mut answers = Vec::new();
    let mut folders = Vec::new();
    for (id, format) in [(2, "html"), (3, "jsonl")] {
        let frame = request(
            &mut socket,
            json!({ "id": id, "op": "export", "format": format }),
        )
        .await;
        let reply = &frame["data"];
        let command = daemon.next_command();
        let path = std::path::PathBuf::from(command["outputPath"].as_str().expect("a path"));
        let folder = path.parent().expect("a folder").to_path_buf();
        let data = base64::engine::general_purpose::STANDARD
            .decode(reply["data"].as_str().expect("base64 data"))
            .expect("decode");
        answers.push((
            frame["type"].clone(),
            reply["name"].clone(),
            reply["mimeType"].clone(),
            String::from_utf8(data).expect("utf-8"),
            command["type"].clone(),
        ));
        folders.push(folder.exists());
    }
    assert_eq!(
        (answers, folders),
        (
            vec![
                (
                    json!("reply"),
                    json!("eukhe-session-s1.html"),
                    json!("text/html"),
                    "export_html of s1".to_string(),
                    json!("export_html"),
                ),
                (
                    json!("reply"),
                    json!("eukhe-session-s1.jsonl"),
                    json!("application/jsonl"),
                    "export_jsonl of s1".to_string(),
                    json!("export_jsonl"),
                ),
            ],
            vec![false, false],
        )
    );
}

#[tokio::test]
async fn events_and_other_requests_never_wait_behind_a_slow_request() {
    let dir = tempfile::tempdir().expect("tempdir");
    let daemon = ScriptedDaemon::start(&dir.path().join("daemon.sock"), &["get_session_stats"]);
    let port = serve(config(dir.path(), Vec::new()), Running).await;
    let mut socket = bound_tab(port, &daemon).await;

    send(
        &mut socket,
        &json!({ "id": 10, "op": "run", "command": { "type": "get_session_stats" } }),
    )
    .await;
    // The daemon has the request and holds its answer.
    let waiting = tokio::task::spawn_blocking(move || {
        let answer = daemon
            .held_answers
            .recv_timeout(DEADLINE)
            .expect("the request reached the daemon");
        (daemon, answer)
    });
    let (daemon, held) = waiting.await.expect("held");

    // Meanwhile an event and another request go through.
    daemon.write(&session_event(4, &json!({ "type": "agent_start" })));
    assert_eq!(
        next_frame(&mut socket).await,
        json!({
            "type": "event", "event": { "type": "agent_start" },
            "cursor": { "generation": "g1", "sequence": 4 },
        })
    );
    let sessions = request(&mut socket, json!({ "id": 11, "op": "sessions" })).await;
    assert_eq!(sessions["data"][0]["id"], "newest", "{sessions}");

    // The slow request answers when the daemon does.
    daemon.write(&held);
    assert_eq!(
        next_frame(&mut socket).await,
        json!({ "type": "reply", "id": 10, "data": { "tokens": { "total": 42 }, "for": "s1" } })
    );
}

#[tokio::test]
async fn a_tab_resumes_from_its_cursor_and_hears_approvals() {
    let dir = tempfile::tempdir().expect("tempdir");
    let daemon = ScriptedDaemon::start(&dir.path().join("daemon.sock"), &[]);
    let port = serve(config(dir.path(), Vec::new()), Running).await;
    let mut socket = open_tab(port).await;
    pair(&mut socket).await;

    // Nothing missed: no transcript, and of the two events in flight only
    // the one after the snapshot follows the reply.
    send(
        &mut socket,
        &json!({
            "id": 1, "op": "open", "sessionId": "newest",
            "resume": { "generation": "g1", "sequence": 3 },
        }),
    )
    .await;
    let after_open = [next_frame(&mut socket).await, next_frame(&mut socket).await];
    let agent_start = json!({
        "type": "event", "event": { "type": "agent_start" },
        "cursor": { "generation": "g1", "sequence": 4 },
    });
    assert_eq!(
        after_open,
        [
            json!({ "type": "reply", "id": 1, "data": {
                "session": { "id": "newest", "path": "/s/newest.jsonl" },
                "state": state(),
                "summary": summary(),
                "messages": null,
                "cursor": { "generation": "g1", "sequence": 3 },
                "replay": "complete",
            } }),
            agent_start.clone(),
        ]
    );
    let attach = std::iter::from_fn(|| daemon.seen.try_recv().ok())
        .find(|command| command["type"] == "attach")
        .expect("an attach");
    assert_eq!(
        attach["resumeCursor"],
        json!({ "generation": "g1", "sequence": 3 })
    );

    // The bound session's approval question reaches the tab; another
    // session's does not.
    let approval = |active_session_id: &str| {
        json!({
            "type": "shell_approval", "activeSessionId": active_session_id,
            "request": { "requestId": active_session_id, "step": 0, "command": "rm -r build", "effects": ["write"] },
        })
    };
    daemon.write(&approval("s2"));
    daemon.write(&approval("s1"));
    assert_eq!(
        next_frame(&mut socket).await,
        json!({
            "type": "approval",
            "request": { "requestId": "s1", "step": 0, "command": "rm -r build", "effects": ["write"] },
        })
    );

    // A cursor the daemon cannot replay from: the whole transcript again.
    send(
        &mut socket,
        &json!({
            "id": 2, "op": "open", "path": "/s/newest.jsonl",
            "resume": { "generation": "g1", "sequence": 1 },
        }),
    )
    .await;
    let after_reopen = [next_frame(&mut socket).await, next_frame(&mut socket).await];
    assert_eq!(
        after_reopen,
        [
            json!({ "type": "reply", "id": 2, "data": {
                "session": { "id": "newest", "path": "/s/newest.jsonl" },
                "state": state(),
                "summary": summary(),
                "messages": transcript(),
                "cursor": { "generation": "g1", "sequence": 3 },
                "replay": "unavailable",
            } }),
            agent_start,
        ]
    );

    let both = request(
        &mut socket,
        json!({ "id": 3, "op": "open", "sessionId": "newest", "path": "/s/newest.jsonl" }),
    )
    .await;
    assert_eq!(
        both,
        json!({ "type": "failure", "id": 3, "error": "open takes a sessionId or a path, not both" })
    );
}

#[tokio::test]
async fn a_new_session_opens_in_the_folder_the_tab_names() {
    let dir = tempfile::tempdir().expect("tempdir");
    let daemon = ScriptedDaemon::start(&dir.path().join("daemon.sock"), &[]);
    let port = serve(config(dir.path(), Vec::new()), Running).await;
    let mut socket = bound_tab(port, &daemon).await;
    let work = dir.path().join("work");
    std::fs::create_dir(&work).expect("mkdir");

    let created = request(
        &mut socket,
        json!({ "id": 2, "op": "new", "cwd": work.display().to_string() }),
    )
    .await;
    assert_eq!(created["type"], "reply", "{created}");
    assert_eq!(
        daemon.next_command(),
        json!({
            "type": "create",
            "config": {
                "script": "/x.json",
                "sessionDir": dir.path().join("sessions").display().to_string(),
                "cwd": work.display().to_string(),
            },
            "lifecycle": "resident",
        })
    );
    let missing = dir.path().join("missing").display().to_string();
    let refused = request(&mut socket, json!({ "id": 3, "op": "new", "cwd": missing })).await;
    assert_eq!(
        refused,
        json!({ "type": "failure", "id": 3, "error": format!("no folder at {missing}") })
    );
}

#[tokio::test]
async fn a_tab_without_a_daemon_hears_why() {
    let dir = tempfile::tempdir().expect("tempdir");
    let port = serve(
        config(dir.path(), Vec::new()),
        Down(Arc::new(AtomicUsize::new(0))),
    )
    .await;
    let mut socket = open_tab(port).await;
    pair(&mut socket).await;
    assert_eq!(
        next_frame(&mut socket).await,
        json!({ "type": "unavailable", "error": "start the eukhe daemon: no daemon here" })
    );
}

/// Whether the server closed the socket next (a close frame, or the end).
async fn closed(socket: &mut Socket) -> bool {
    match tokio::time::timeout(DEADLINE, socket.next())
        .await
        .expect("the next message in time")
    {
        Some(Ok(Message::Close(_)) | Err(_)) | None => true,
        Some(Ok(
            Message::Text(_)
            | Message::Binary(_)
            | Message::Ping(_)
            | Message::Pong(_)
            | Message::Frame(_),
        )) => false,
    }
}

/// A socket runs nothing without the current pairing token: with no
/// pairing first, an empty, other or malformed token, or a token a
/// rotation replaced, it hears `unpaired` and closes; no bridge starts
/// and no command reaches the daemon. The rotated token pairs.
#[tokio::test]
async fn a_socket_without_the_current_token_runs_nothing() {
    let dir = tempfile::tempdir().expect("tempdir");
    let daemon = ScriptedDaemon::start(&dir.path().join("daemon.sock"), &[]);
    let bridges = Arc::new(AtomicUsize::new(0));
    let config = config(dir.path(), Vec::new());
    let token_path = config.token_path.clone();
    let port = serve(config, Counted(Arc::clone(&bridges))).await;
    let unpaired = |error: &str| json!({ "type": "unpaired", "error": error });
    let missing = "pairing needed: open the link that `eukhe dashboard` prints";
    let wrong =
        "this pairing link is not valid any more: open the link that `eukhe dashboard` prints";
    let seen = |daemon: &ScriptedDaemon| -> Vec<Value> {
        std::iter::from_fn(|| daemon.seen.try_recv().ok())
            .map(|command| command["type"].clone())
            .collect()
    };

    let mut heard = Vec::new();
    for first in [
        Message::text(json!({ "id": 1, "op": "sessions" }).to_string()),
        Message::text(json!({ "op": "pair", "token": "" }).to_string()),
        Message::text(json!({ "op": "pair", "token": TOKEN.replace('0', "f") }).to_string()),
        Message::text(json!({ "op": "pair", "token": "secret" }).to_string()),
        Message::binary(TOKEN.as_bytes().to_vec()),
    ] {
        let mut socket = open_tab(port).await;
        socket.send(first).await.expect("send");
        heard.push((next_frame(&mut socket).await, closed(&mut socket).await));
    }
    assert_eq!(
        (heard, bridges.load(Ordering::SeqCst), seen(&daemon)),
        (
            vec![
                (unpaired(missing), true),
                (unpaired(missing), true),
                (unpaired(wrong), true),
                (unpaired(wrong), true),
                (unpaired(missing), true),
            ],
            0,
            Vec::new()
        )
    );

    // A paired tab runs until a rotation; then its next frame runs
    // nothing, the old token pairs no more, and the new one does.
    let mut socket = open_tab(port).await;
    pair(&mut socket).await;
    let listed = request(&mut socket, json!({ "id": 1, "op": "sessions" })).await["type"].clone();
    let ran = seen(&daemon);
    let rotated = eukhe_dashboard::pairing_token(&token_path, eukhe_dashboard::Rotation::Rotate)
        .expect("rotate");
    send(&mut socket, &json!({ "id": 2, "op": "sessions" })).await;
    let stale = (next_frame(&mut socket).await, closed(&mut socket).await);
    let mut old = open_tab(port).await;
    send(&mut old, &json!({ "op": "pair", "token": TOKEN })).await;
    let old_pair = (next_frame(&mut old).await, closed(&mut old).await);
    let after_rotation = seen(&daemon);
    let mut fresh = open_tab(port).await;
    send(
        &mut fresh,
        &json!({ "op": "pair", "token": rotated.secret_hex() }),
    )
    .await;
    let greeted = next_frame(&mut fresh).await["type"].clone();
    assert_eq!(
        (
            listed,
            ran,
            stale,
            old_pair,
            after_rotation,
            greeted,
            bridges.load(Ordering::SeqCst)
        ),
        (
            json!("reply"),
            vec![json!("list_saved_sessions")],
            (unpaired(wrong), true),
            (unpaired(wrong), true),
            Vec::new(),
            json!("hello"),
            2
        )
    );
}
