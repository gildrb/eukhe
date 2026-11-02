//! End-to-end: `pause_workers` / `resume_workers` through the real
//! supervisor and a scripted worker. Without `ownRun` (a client on main)
//! the session's own run keeps going and the reply lists its workers; with
//! `ownRun` the session's run pauses: the reply lists its workers, its
//! summary says `isPaused`, and a roster update pushes it to subscribers;
//! the resume clears it with another push.
#![allow(clippy::large_futures)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::time::{Duration, Instant};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::supervisor_command;
use process::Daemon;
use serde_json::{json, Value};

struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> Self {
        let stream = UnixStream::connect(socket).expect("connect supervisor");
        let writer = stream.try_clone().expect("clone socket");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
        };
        assert_eq!(client.read_line()["type"], "daemon_hello");
        client
    }

    fn send_command(&mut self, id: &str, command: &Value) {
        let mut line = json!({
            "type": "command",
            "id": id,
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "command": command,
        })
        .to_string();
        line.push('\n');
        self.writer.write_all(line.as_bytes()).expect("send");
        self.writer.flush().expect("flush");
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        self.reader
            .get_mut()
            .set_read_timeout(Some(Duration::from_secs(30)))
            .expect("set timeout");
        loop {
            match self.reader.read_line(&mut line) {
                Ok(0) => panic!("supervisor closed the connection"),
                Ok(_) if line.trim().is_empty() => line.clear(),
                Ok(_) => return serde_json::from_str(line.trim()).expect("parse line"),
                Err(error) => panic!("timed out reading: {error}"),
            }
        }
    }

    fn read_response(&mut self, id: &str) -> Value {
        loop {
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                return line;
            }
        }
    }

    /// Send `command` as `id`; its response, once a roster update showing
    /// `session` with `isPaused == paused` arrived too.
    fn command_with_push(
        &mut self,
        id: &str,
        command: &Value,
        session: &str,
        paused: bool,
    ) -> Value {
        self.send_command(id, command);
        let deadline = Instant::now() + Duration::from_secs(30);
        let (mut response, mut pushed) = (None, false);
        while response.is_none() || !pushed {
            assert!(Instant::now() < deadline, "no response or roster push");
            let line = self.read_line();
            if line["type"] == "roster_update" {
                pushed |= line["changed"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .any(|entry| {
                        entry["summary"]["activeSessionId"] == session
                            && entry["summary"]["isPaused"].as_bool().unwrap_or(false) == paused
                    });
            }
            if line.get("id").and_then(Value::as_str) == Some(id) {
                response = Some(line);
            }
        }
        response.expect("the response")
    }
}

#[test]
fn pause_and_resume_workers_reply_flag_and_push() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let _daemon = Daemon::spawn_bound(
        supervisor_command(&socket, &agent_dir).env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            "15000",
        ),
        &socket,
        Duration::from_secs(10),
    );
    let mut client = Client::connect(&socket);
    let script = dir.path().join("script.json");
    std::fs::write(&script, json!({ "responses": ["hello"] }).to_string()).expect("script");
    client.send_command(
        "c1",
        &json!({
            "type": "create",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": agent_dir.join("sessions").to_string_lossy(),
                "script": script.to_string_lossy(),
            },
        }),
    );
    let created = client.read_response("c1");
    assert_eq!(created["success"], true, "create failed: {created}");
    let session = created["data"]["id"]
        .as_str()
        .or_else(|| created["data"]["sessionId"].as_str())
        .expect("session id")
        .to_string();
    client.send_command("r1", &json!({ "type": "roster_subscribe" }));
    assert_eq!(client.read_response("r1")["success"], true);

    // A client on main: main's run keeps going; no worker yet.
    client.send_command(
        "p0",
        &json!({ "type": "pause_workers", "activeSessionId": session }),
    );
    let main_only = client.read_response("p0");
    assert_eq!(
        (&main_only["success"], &main_only["data"]),
        (&json!(true), &json!({ "workers": [] }))
    );

    // A parent on its child (`ownRun`): this session's run pauses.
    let paused = client.command_with_push(
        "p1",
        &json!({ "type": "pause_workers", "activeSessionId": session, "ownRun": true }),
        &session,
        true,
    );
    assert_eq!(
        (&paused["success"], &paused["data"]),
        (&json!(true), &json!({ "workers": [] }))
    );
    let resumed = client.command_with_push(
        "p2",
        &json!({ "type": "resume_workers", "activeSessionId": session, "ownRun": true }),
        &session,
        false,
    );
    assert_eq!(
        (&resumed["success"], &resumed["data"]),
        (&json!(true), &json!({ "workers": [] }))
    );
}
