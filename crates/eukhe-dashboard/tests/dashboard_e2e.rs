//! The dashboard end to end against a scripted daemon socket: the server
//! answers the app's files and its WebSocket only to loopback (or allowed)
//! hosts and to its own origin; a tab's socket greets with `hello`, opens
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

const DEADLINE: Duration = Duration::from_secs(20);

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
/// goes to loopback) and `origin`, if any.
async fn upgrade(
    port: u16,
    host: &str,
    origin: Option<&str>,
) -> Result<Socket, tungstenite::Error> {
    let stream = tokio::net::TcpStream::connect(("127.0.0.1", port))
        .await
        .expect("connect");
    let mut request = format!("ws://{host}/api/ws")
        .into_client_request()
        .expect("request");
    if let Some(origin) = origin {
        request
            .headers_mut()
            .insert("origin", origin.parse().expect("origin"));
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
        Some(&format!("http://127.0.0.1:{port}")),
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

/// The `hello` greeting, as every socket's first frame.
async fn expect_hello(socket: &mut Socket) {
    let hello = next_frame(socket).await;
    let build = hello["build"].as_str().unwrap_or_default().to_string();
    assert!(build.contains("+web."), "{hello}");
    assert_eq!(
        hello,
        json!({
            "type": "hello", "protocol": 2, "build": build,
            "ops": ["sessions", "open", "new", "prompt", "abort", "memory", "run"],
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

fn config(dir: &Path, allowed_hosts: Vec<String>) -> DashboardConfig {
    DashboardConfig {
        socket_path: dir.join("daemon.sock"),
        session_dir: dir.join("sessions"),
        new_session_cwd: dir.to_path_buf(),
        create_config: serde_json::Map::from_iter([("script".to_string(), json!("/x.json"))]),
        allowed_hosts,
    }
}

/// A tab bound to the newest session (`s1`); the daemon's commands so far
/// are consumed.
async fn bound_tab(port: u16, daemon: &ScriptedDaemon) -> Socket {
    let mut socket = open_tab(port).await;
    expect_hello(&mut socket).await;
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

    let refused = |result: Result<Socket, tungstenite::Error>| match result {
        Err(tungstenite::Error::Http(response)) => response.status().as_u16(),
        Err(error) => panic!("expected an HTTP refusal, got {error}"),
        Ok(_) => panic!("the upgrade was accepted"),
    };
    let statuses = [
        // Cross-site WebSocket hijacking: another site's page.
        refused(upgrade(port, &loopback, Some("http://evil.example")).await),
        refused(upgrade(port, &loopback, Some(&format!("http://localhost:{port}"))).await),
        refused(upgrade(port, &loopback, None).await),
        refused(upgrade(port, &rebound, Some(&format!("http://{rebound}"))).await),
        refused(upgrade(port, "box.tail1234.ts.net", Some("https://evil.example")).await),
    ];
    assert_eq!(statuses, [403, 403, 403, 403, 403]);
    assert_eq!(
        bridges.load(Ordering::SeqCst),
        0,
        "no refused socket reached a bridge"
    );

    // The page's own origin, on loopback and under the allowed name.
    for (host, origin) in [
        (loopback.clone(), format!("http://{loopback}")),
        (
            "box.tail1234.ts.net".to_string(),
            "https://box.tail1234.ts.net".to_string(),
        ),
    ] {
        let mut socket = upgrade(port, &host, Some(&origin))
            .await
            .expect("the page's own socket");
        expect_hello(&mut socket).await;
        let frame = next_frame(&mut socket).await;
        assert_eq!(
            frame,
            json!({
                "type": "unavailable",
                "error": "start the eukhe daemon: no daemon here",
            })
        );
    }
    assert_eq!(bridges.load(Ordering::SeqCst), 2);
}

#[tokio::test]
#[allow(clippy::too_many_lines)] // One tab's whole session, in order.
async fn a_tab_chats_and_browses_the_memory_through_the_daemon() {
    let dir = tempfile::tempdir().expect("tempdir");
    let daemon = ScriptedDaemon::start(&dir.path().join("daemon.sock"), &[]);
    let port = serve(config(dir.path(), Vec::new()), Running).await;
    let mut socket = open_tab(port).await;
    expect_hello(&mut socket).await;

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
    expect_hello(&mut socket).await;

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
    expect_hello(&mut socket).await;

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
            "request": { "requestId": active_session_id, "step": 0, "command": "rm -r build", "effect": "write" },
        })
    };
    daemon.write(&approval("s2"));
    daemon.write(&approval("s1"));
    assert_eq!(
        next_frame(&mut socket).await,
        json!({
            "type": "approval",
            "request": { "requestId": "s1", "step": 0, "command": "rm -r build", "effect": "write" },
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
    expect_hello(&mut socket).await;
    assert_eq!(
        next_frame(&mut socket).await,
        json!({ "type": "unavailable", "error": "start the eukhe daemon: no daemon here" })
    );
}
