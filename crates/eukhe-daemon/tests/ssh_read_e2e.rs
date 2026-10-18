//! `ssh://` reads end to end (docs/tools.md S7.9): a daemon session (a
//! scripted faux provider) with a fake `ssh` first on `PATH` and
//! `ssh.hosts` in the global settings. The `read` tool reads a file of an
//! allowed host through the fake, a host outside `ssh.hosts` is rejected
//! by name with no `ssh` run, and a host that refuses the keys is the
//! typed `auth` rejection.

use std::io::{BufRead, BufReader, Write};
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::supervisor_command;
use process::Daemon;

/// JSONL supervisor client (command envelopes, id-matched responses).
struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> (Self, Value) {
        let stream = UnixStream::connect(socket).expect("connect supervisor");
        let writer = stream.try_clone().expect("clone socket");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
        };
        let hello = client.read_line();
        (client, hello)
    }

    fn command(&mut self, id: &str, command: &Value) -> Value {
        let mut line = serde_json::to_string(&json!({
            "type": "command",
            "id": id,
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "command": command,
        }))
        .expect("serialize command");
        line.push('\n');
        self.writer.write_all(line.as_bytes()).expect("send");
        self.writer.flush().expect("flush");
        let deadline = Instant::now() + Duration::from_mins(4);
        loop {
            assert!(Instant::now() < deadline, "no response for id {id}");
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                assert_eq!(line["success"], true, "{id} failed: {line}");
                return line;
            }
        }
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        let deadline = Instant::now() + Duration::from_mins(2);
        self.reader
            .get_mut()
            .set_read_timeout(Some(Duration::from_millis(100)))
            .expect("set timeout");
        loop {
            match self.reader.read_line(&mut line) {
                Ok(0) => panic!("supervisor closed the connection"),
                Ok(_) if line.trim().is_empty() => line.clear(),
                Ok(_) => return serde_json::from_str(line.trim()).expect("parse response line"),
                Err(error) => {
                    assert!(
                        Instant::now() < deadline,
                        "timed out waiting for supervisor line: {error}"
                    );
                }
            }
        }
    }
}

#[test]
// One scenario, read top to bottom.
#[allow(clippy::too_many_lines)]
fn the_read_tool_reads_an_allowed_host_through_the_users_ssh() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let sessions_dir = agent_dir.join("sessions");
    let bin = dir.path().join("bin");
    let remote_home = dir.path().join("remote-home");
    for made in [&sessions_dir, &bin, &remote_home] {
        std::fs::create_dir_all(made).expect("dir");
    }
    std::fs::write(remote_home.join("hello.txt"), "hello from fakebox\n").expect("remote file");
    let ssh = bin.join("ssh");
    std::fs::write(
        &ssh,
        format!(
            r#"#!/bin/sh
printf '%s\0' "$@" >> '{log}'
while [ "$1" != "--" ]; do shift; done
case "$2" in
  fakebox) cd '{home}' && exec sh -c "$3" ;;
  nokey) echo "me@nokey: Permission denied (publickey)." >&2; exit 255 ;;
esac
exit 255
"#,
            log = dir.path().join("ssh-args").display(),
            home = remote_home.display(),
        ),
    )
    .expect("fake ssh");
    std::fs::set_permissions(&ssh, std::fs::Permissions::from_mode(0o755)).expect("chmod");
    std::fs::write(
        agent_dir.join("settings.json"),
        json!({ "ssh": { "hosts": ["fakebox", "nokey"] } }).to_string(),
    )
    .expect("write settings.json");
    let read =
        |path: &str| json!({ "type": "toolCall", "name": "read", "arguments": { "path": path } });
    let script = dir.path().join("faux.json");
    std::fs::write(
        &script,
        json!({
            "engine": "faux",
            "responses": [
                { "content": [
                    read("ssh://fakebox/~/hello.txt"),
                    read("ssh://elsewhere/etc/hosts"),
                    read("ssh://nokey/etc/hosts"),
                ] },
                { "text": "done" },
            ],
        })
        .to_string(),
    )
    .expect("write faux script");

    let socket = dir.path().join("ssh.sock");
    let path = format!("{}:{}", bin.display(), std::env::var("PATH").expect("PATH"));
    let _daemon = Daemon::spawn_listening(
        supervisor_command(&socket, &agent_dir)
            .env("EUKHE_CODING_AGENT_DIR", &agent_dir)
            .env("PATH", path)
            .env_remove("PRIME_API_KEY")
            .env(
                eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
                "15000",
            ),
        &socket,
        Duration::from_secs(15),
    );
    let (mut client, hello) = Client::connect(&socket);
    assert_eq!(hello["type"], "daemon_hello");
    let created = client.command(
        "c1",
        &json!({
            "type": "create",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": sessions_dir.to_string_lossy(),
                "script": script.to_string_lossy(),
            },
        }),
    );
    let session = created["data"]["activeSessionId"]
        .as_str()
        .or_else(|| created["data"]["id"].as_str())
        .expect("active session id")
        .to_owned();
    client.command(
        "p1",
        &json!({ "type": "prompt", "activeSessionId": session, "message": "read the remote files" }),
    );
    client.command(
        "w1",
        &json!({ "type": "wait_for_idle", "activeSessionId": session }),
    );
    let messages = client.command(
        "m1",
        &json!({ "type": "get_messages", "activeSessionId": session }),
    );
    // The reads run at once and settle in any order: results and
    // invocations are compared sorted.
    let mut results: Vec<(String, bool)> = messages["data"]["messages"]
        .as_array()
        .expect("messages")
        .iter()
        .filter(|message| message["role"] == "toolResult")
        .map(|message| {
            let text = message["content"]
                .as_array()
                .expect("content blocks")
                .iter()
                .filter_map(|block| block["text"].as_str())
                .collect::<Vec<_>>()
                .join("\n");
            (text, message["isError"] == true)
        })
        .collect();
    results.sort();
    // One invocation is ten arguments.
    let arguments: Vec<String> = std::fs::read(dir.path().join("ssh-args"))
        .expect("ssh ran")
        .split(|byte| *byte == 0)
        .filter(|arg| !arg.is_empty())
        .map(|arg| String::from_utf8(arg.to_vec()).expect("utf-8 argument"))
        .collect();
    let mut invocations: Vec<Vec<String>> = arguments.chunks(10).map(<[String]>::to_vec).collect();
    invocations.sort();
    let invocation = |host: &str, command: &str| {
        [
            "-T",
            "-o",
            "BatchMode=yes",
            "-o",
            "ConnectTimeout=30",
            "-o",
            "ClearAllForwardings=yes",
            "--",
            host,
            command,
        ]
        .map(str::to_owned)
        .to_vec()
    };
    assert_eq!(
        (results, invocations),
        (
            vec![
                ("hello from fakebox\n".to_owned(), false),
                (
                    "ssh://elsewhere/etc/hosts: the host elsewhere is not in the setting `ssh.hosts` (it allows fakebox, nokey); add the host to `ssh.hosts` in the global settings.json to read from it".to_owned(),
                    true,
                ),
                (
                    "ssh://nokey/etc/hosts: authentication failed: me@nokey: Permission denied (publickey).; eukhe gives ssh no password or passphrase (BatchMode), so load the key into ssh-agent or name it in ~/.ssh/config".to_owned(),
                    true,
                ),
            ],
            vec![
                invocation("fakebox", "cat -- 'hello.txt'"),
                invocation("nokey", "cat -- '/etc/hosts'"),
            ],
        )
    );
}
