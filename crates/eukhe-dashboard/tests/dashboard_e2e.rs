//! The dashboard end to end against a scripted daemon socket: the server
//! answers the app's files on loopback, and a tab's WebSocket opens the
//! newest root session (create + attach), sends a message whose reply
//! streams back as session events, reads the memory tree a level at a
//! time, and stops the turn.
#![cfg(unix)]

use std::future::Future;
use std::io::{BufRead, BufReader, Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::time::Duration;

use eukhe_dashboard::{DashboardConfig, Port};
use eukhe_tui::saved_sessions::DaemonLauncher;
use futures::{SinkExt, StreamExt};
use serde_json::{json, Value};
use tokio_tungstenite::tungstenite::Message;

/// The daemon is already up (the scripted socket).
struct Running;

impl DaemonLauncher for Running {
    fn ensure(&self) -> impl Future<Output = anyhow::Result<()>> + Send {
        std::future::ready(Ok(()))
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

/// The scripted daemon: one connection, the commands the bridge sends,
/// and a streamed reply after each prompt. Every command lands in
/// `seen` (type and payload) for the test's checks.
fn serve_daemon(listener: &UnixListener, seen: &std::sync::mpsc::Sender<Value>) {
    let (stream, _) = listener.accept().expect("accept");
    let mut writer = stream.try_clone().expect("clone");
    let mut reader = BufReader::new(stream);
    write_json(
        &mut writer,
        &json!({
            "type": "daemon_hello",
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "serverCapabilities": ["memory", "memory_tree"],
            "clientId": "mock",
        }),
    );
    let mut line = String::new();
    loop {
        line.clear();
        match reader.read_line(&mut line) {
            Ok(0) | Err(_) => break,
            Ok(_) => {}
        }
        let Ok(envelope) = serde_json::from_str::<Value>(line.trim()) else {
            continue;
        };
        let id = envelope["id"].as_str().unwrap_or_default().to_string();
        let command = envelope["command"].clone();
        let command_type = command["type"].as_str().unwrap_or_default().to_string();
        let _ = seen.send(command.clone());
        write_json(
            &mut writer,
            &json!({
                "type": "response", "id": id, "command": command_type,
                "success": true, "data": daemon_answer(&command),
            }),
        );
        if command_type == "prompt" {
            stream_reply(&mut writer);
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
        "attach" => json!({
            "activeSessionId": "s1",
            "snapshot": {
                "state": { "isStreaming": false, "cwd": "/", "sessionName": null },
                "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }],
            },
        }),
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
        _ => json!({}),
    }
}

/// A prompt's reply as the daemon streams it: a run with one assistant
/// message started, updated and settled.
fn stream_reply(writer: &mut UnixStream) {
    let event = |payload: Value| json!({ "type": "session_event", "activeSessionId": "s1", "event": payload });
    let events = [
        json!({ "type": "agent_start" }),
        json!({ "type": "message_start", "message": assistant("") }),
        json!({
            "type": "message_update",
            "message": assistant("hel"),
            "assistantMessageEvent": { "type": "text_delta", "delta": "hel" },
        }),
        json!({ "type": "message_end", "message": assistant("hello") }),
        json!({ "type": "agent_end", "messages": [] }),
    ];
    for payload in events {
        write_json(writer, &event(payload));
    }
}

/// One plain HTTP/1.1 GET: the status line, the headers, and the body.
fn get(port: u16, path: &str) -> (String, String, String) {
    let mut stream = std::net::TcpStream::connect(("127.0.0.1", port)).expect("connect");
    stream.set_read_timeout(Some(DEADLINE)).expect("timeout");
    write!(
        stream,
        "GET {path} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nConnection: close\r\n\r\n"
    )
    .expect("request");
    let mut response = String::new();
    stream.read_to_string(&mut response).expect("response");
    let (head, body) = response.split_once("\r\n\r\n").expect("head");
    let (status, headers) = head.split_once("\r\n").expect("status");
    (status.to_string(), headers.to_lowercase(), body.to_string())
}

type Socket =
    tokio_tungstenite::WebSocketStream<tokio_tungstenite::MaybeTlsStream<tokio::net::TcpStream>>;

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

async fn request(socket: &mut Socket, frame: Value) -> Value {
    let id = frame["id"].clone();
    socket
        .send(Message::text(frame.to_string()))
        .await
        .expect("send");
    loop {
        let reply = next_frame(socket).await;
        if reply["id"] == id && reply["type"] != "event" {
            return reply;
        }
    }
}

/// The app's files on loopback, also under a path prefix; nothing else.
async fn check_files(port: u16) {
    let (status, headers, body) = tokio::task::spawn_blocking(move || get(port, "/"))
        .await
        .expect("get");
    assert_eq!(status, "HTTP/1.1 200 OK");
    assert!(headers.contains("content-type: text/html"), "{headers}");
    assert!(body.contains("<title>eukhe</title>"), "{body}");
    let (status, headers, _) = tokio::task::spawn_blocking(move || get(port, "/eukhe/app.js"))
        .await
        .expect("get");
    assert_eq!(status, "HTTP/1.1 200 OK");
    assert!(
        headers.contains("content-type: text/javascript"),
        "{headers}"
    );
    let (status, _, _) = tokio::task::spawn_blocking(move || get(port, "/etc/passwd"))
        .await
        .expect("get");
    assert_eq!(status, "HTTP/1.1 404 Not Found");
}

#[tokio::test]
async fn a_tab_chats_and_browses_the_memory_through_the_daemon() {
    let dir = tempfile::tempdir().expect("tempdir");
    let socket_path = dir.path().join("daemon.sock");
    let listener = UnixListener::bind(&socket_path).expect("bind daemon");
    let (seen_sender, seen) = std::sync::mpsc::channel();
    std::thread::spawn(move || serve_daemon(&listener, &seen_sender));

    let http = eukhe_dashboard::bind(Port::Free).await.expect("bind");
    let address = http.local_addr().expect("address");
    assert!(address.ip().is_loopback(), "{address}");
    let port = address.port();
    let config = DashboardConfig {
        socket_path,
        session_dir: dir.path().join("sessions"),
        new_session_cwd: dir.path().to_path_buf(),
        create_config: serde_json::Map::from_iter([("script".to_string(), json!("/x.json"))]),
    };
    tokio::spawn(eukhe_dashboard::serve(http, config, Running));

    check_files(port).await;

    let (mut socket, _) = tokio_tungstenite::connect_async(format!("ws://127.0.0.1:{port}/api/ws"))
        .await
        .expect("the bridge's socket");

    // Open: the newest root session, created resident and attached.
    let opened = request(&mut socket, json!({ "id": 1, "op": "open", "path": null })).await;
    assert_eq!(
        opened,
        json!({ "type": "reply", "id": 1, "data": {
            "session": { "id": "newest", "path": "/s/newest.jsonl" },
            "state": { "isStreaming": false, "cwd": "/", "sessionName": null },
            "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }],
        } })
    );
    let commands: Vec<Value> = seen.try_iter().collect();
    let create = commands
        .iter()
        .find(|command| command["type"] == "create")
        .expect("a create");
    assert_eq!(create["sessionPath"], "/s/newest.jsonl");
    assert_eq!(create["lifecycle"], "resident");
    assert_eq!(create["config"]["script"], "/x.json");
    assert_eq!(
        create["config"]["sessionDir"],
        dir.path().join("sessions").display().to_string()
    );

    // A message: accepted, then its reply streams as events.
    let sent = request(
        &mut socket,
        json!({ "id": 2, "op": "prompt", "text": "say hello", "mode": "steer" }),
    )
    .await;
    assert_eq!(sent, json!({ "type": "reply", "id": 2, "data": null }));
    let prompt = seen
        .recv_timeout(DEADLINE)
        .expect("the prompt reached the daemon");
    assert_eq!(prompt["type"], "prompt");
    assert_eq!(prompt["message"], "say hello");
    assert_eq!(prompt["activeSessionId"], "s1");
    assert_eq!(prompt["streamingBehavior"], "steer");
    assert_eq!(prompt["queueIfBusy"], true);
    let mut events = Vec::new();
    while events.last() != Some(&json!("agent_end")) {
        let frame = next_frame(&mut socket).await;
        assert_eq!(frame["type"], "event", "{frame}");
        if frame["event"]["type"] == "message_end" {
            assert_eq!(frame["event"]["message"]["content"][1]["text"], "hello");
        }
        events.push(frame["event"]["type"].clone());
    }
    assert_eq!(
        events,
        [
            "agent_start",
            "message_start",
            "message_update",
            "message_end",
            "agent_end"
        ]
    );

    // The memory: the view's lines, then one opened down to its message.
    let top = request(
        &mut socket,
        json!({ "id": 3, "op": "memory", "node": null }),
    )
    .await;
    assert_eq!(top["type"], "reply");
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
}

#[tokio::test]
async fn a_tab_without_a_daemon_hears_why() {
    struct Down;
    impl DaemonLauncher for Down {
        fn ensure(&self) -> impl Future<Output = anyhow::Result<()>> + Send {
            std::future::ready(Err(anyhow::anyhow!("no daemon here")))
        }
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let http = eukhe_dashboard::bind(Port::Free).await.expect("bind");
    let port = http.local_addr().expect("address").port();
    let config = DashboardConfig {
        socket_path: dir.path().join("none.sock"),
        session_dir: dir.path().to_path_buf(),
        new_session_cwd: dir.path().to_path_buf(),
        create_config: serde_json::Map::new(),
    };
    tokio::spawn(eukhe_dashboard::serve(http, config, Down));
    let (mut socket, _) = tokio_tungstenite::connect_async(format!("ws://127.0.0.1:{port}/api/ws"))
        .await
        .expect("the bridge's socket");
    let frame = next_frame(&mut socket).await;
    assert_eq!(frame["type"], "unavailable");
    assert!(
        frame["error"]
            .as_str()
            .unwrap_or_default()
            .contains("no daemon here"),
        "{frame}"
    );
}
