//! Real-daemon e2e of irreversible effects over the dashboard: the
//! dashboard's bridge serves a tab against a real supervisor, and a
//! scripted run commits an edit and pushes it to a local bare repository.
//!
//! - The push runs unasked: the remote has the commit when the run ends.
//! - The end-of-run message reaches the tab once, in the words every
//!   surface shows; a later run with nothing irreversible carries none.
//! - `/effects` (`get_ran_effects`) answers the session's ledger.
//! - `/undo` (`undo_turn`, twice: the second prompt, then the first)
//!   restores the file and names the push it cannot take back.
#![cfg(unix)]

use std::future::Future;
use std::path::Path;
use std::process::Command;
use std::time::Duration;

use eukhe_client::saved_sessions::DaemonLauncher;
use eukhe_dashboard::{DashboardConfig, Port};
use futures::{SinkExt, StreamExt};
use serde_json::{json, Value};
use tokio_tungstenite::tungstenite::client::IntoClientRequest;
use tokio_tungstenite::tungstenite::Message;

#[path = "support/eukhe.rs"]
mod eukhe;
#[path = "../../eukhe-daemon/tests/support/process.rs"]
mod process;

use eukhe::{daemon_mode_args, eukhe_command, scrub_provider_keys};
use process::Daemon;

/// The model's one step: commit an edit, then push it.
const STEP: &str = "echo two >> notes.txt && git -c user.name=t -c user.email=t@e commit -qam two && git push -q origin main";

/// The push, as the end-of-run message, `/effects` and `/undo` name it.
const PUSH_LINE: &str = "- e1 git push -q origin main (exec+net)";

/// The pairing token the test stores.
const TOKEN: &str = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

/// A run and a snapshot restore each wait on the daemon.
const DEADLINE: Duration = Duration::from_secs(90);

/// The daemon runs already (the test started it).
struct Running;

impl DaemonLauncher for Running {
    fn ensure(&self) -> impl Future<Output = anyhow::Result<()>> + Send {
        std::future::ready(Ok(()))
    }
}

type Socket = tokio_tungstenite::WebSocketStream<tokio::net::TcpStream>;

/// A paired tab and every pushed frame it heard so far.
struct Tab {
    socket: Socket,
    heard: Vec<Value>,
}

impl Tab {
    /// Open the bridge's socket as the served page does, and pair.
    async fn open(port: u16) -> Tab {
        let stream = tokio::net::TcpStream::connect(("127.0.0.1", port))
            .await
            .expect("connect");
        let mut request = format!("ws://127.0.0.1:{port}/api/ws")
            .into_client_request()
            .expect("request");
        request.headers_mut().append(
            "origin",
            format!("http://127.0.0.1:{port}")
                .parse()
                .expect("origin header"),
        );
        let (socket, _) = tokio_tungstenite::client_async(request, stream)
            .await
            .expect("the bridge's socket");
        let mut tab = Tab {
            socket,
            heard: Vec::new(),
        };
        tab.send(&json!({ "op": "pair", "token": TOKEN })).await;
        assert_eq!(tab.next().await["type"], "hello");
        tab
    }

    async fn send(&mut self, frame: &Value) {
        self.socket
            .send(Message::text(frame.to_string()))
            .await
            .expect("send");
    }

    async fn next(&mut self) -> Value {
        loop {
            let message = tokio::time::timeout(DEADLINE, self.socket.next())
                .await
                .expect("a frame in time")
                .expect("the socket is open")
                .expect("a frame");
            if let Message::Text(text) = message {
                return serde_json::from_str(text.as_str()).expect("JSON frame");
            }
        }
    }

    /// Send a request; its answer. Frames pushed meanwhile are kept.
    async fn request(&mut self, frame: Value) -> Value {
        self.send(&frame).await;
        loop {
            let reply = self.next().await;
            if reply["id"] == frame["id"]
                && matches!(reply["type"].as_str(), Some("reply" | "failure"))
            {
                return reply;
            }
            self.heard.push(reply);
        }
    }

    /// Hear pushed frames until the frames heard pass `done`.
    async fn hear_until(&mut self, done: impl Fn(&[Value]) -> bool) {
        while !done(&self.heard) {
            let frame = self.next().await;
            self.heard.push(frame);
        }
    }

    /// The words of a `run` command's reply.
    async fn run_text(&mut self, id: u64, command: Value) -> Value {
        let reply = self
            .request(json!({ "id": id, "op": "run", "command": command }))
            .await;
        assert_eq!(reply["type"], "reply", "{reply}");
        reply["data"]["text"].clone()
    }
}

/// How many `agent_end` events the tab heard.
fn ends(heard: &[Value]) -> usize {
    heard
        .iter()
        .filter(|frame| frame["event"]["type"] == "agent_end")
        .count()
}

/// Run `git` in `dir`; its trimmed stdout.
fn git(dir: &Path, args: &[&str]) -> String {
    let output = Command::new("git")
        .args(args)
        .current_dir(dir)
        .env("GIT_AUTHOR_NAME", "test")
        .env("GIT_AUTHOR_EMAIL", "test@example.com")
        .env("GIT_COMMITTER_NAME", "test")
        .env("GIT_COMMITTER_EMAIL", "test@example.com")
        .output()
        .expect("git runs");
    assert!(
        output.status.success(),
        "git {args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).trim().to_owned()
}

/// `work` (one commit of `notes.txt`) pushed to the bare `root/remote.git`,
/// its `origin`.
fn seed_repos(root: &Path, work: &Path) {
    let remote = root.join("remote.git");
    std::fs::create_dir_all(work).expect("workspace");
    git(root, &["init", "-q", "--bare", "-b", "main", "remote.git"]);
    git(work, &["init", "-q", "-b", "main"]);
    std::fs::write(work.join("notes.txt"), "one\n").expect("seed file");
    git(work, &["add", "notes.txt"]);
    git(work, &["commit", "-q", "-m", "one"]);
    git(
        work,
        &["remote", "add", "origin", &remote.display().to_string()],
    );
    git(work, &["push", "-q", "origin", "main"]);
}

#[tokio::test(flavor = "multi_thread")]
async fn an_irreversible_step_runs_unasked_and_the_dashboard_reports_lists_and_names_it() {
    let root = tempfile::TempDir::new().expect("temp root");
    let work = root.path().join("work");
    let remote = root.path().join("remote.git");
    seed_repos(root.path(), &work);
    let script = root.path().join("script.json");
    std::fs::write(
        &script,
        json!({ "responses": [
            { "content": [{ "type": "toolCall", "name": "bash", "id": "call-1",
                "arguments": { "script": STEP } }], "stopReason": "toolUse" },
            { "text": "Committed and pushed." },
            { "text": "Nothing else to do." },
        ]})
        .to_string(),
    )
    .expect("write script");
    let agent_dir = root.path().join("agent");
    std::fs::create_dir_all(agent_dir.join("sessions")).expect("agent dir");
    let socket = root.path().join("daemon.sock");
    let mut command = eukhe_command();
    daemon_mode_args(&mut command, &socket, &agent_dir);
    scrub_provider_keys(&mut command)
        .env("HOME", root.path())
        .env("EUKHE_DAEMON_WORKER_CONNECT_TIMEOUT_MS", "90000");
    let _daemon = Daemon::spawn_listening(&mut command, &socket, Duration::from_mins(1));

    let token_path = agent_dir.join("dashboard-token");
    std::fs::write(&token_path, format!("{TOKEN}\n")).expect("store the token");
    let config = DashboardConfig {
        socket_path: socket,
        session_dir: agent_dir.join("sessions"),
        new_session_cwd: work.clone(),
        create_config: serde_json::Map::from_iter([(
            "script".to_string(),
            json!(script.display().to_string()),
        )]),
        allowed_hosts: Vec::new(),
        token_path,
    };
    let http = eukhe_dashboard::bind(Port::Free).await.expect("bind");
    let port = http.local_addr().expect("address").port();
    tokio::spawn(eukhe_dashboard::serve(http, config, Running));
    let mut tab = Tab::open(port).await;
    let opened = tab
        .request(json!({ "id": 1, "op": "open", "path": null }))
        .await;
    assert_eq!(opened["type"], "reply", "{opened}");

    // The push runs unasked; the end-of-run message follows the run's end.
    let sent = tab
        .request(json!({ "id": 2, "op": "prompt", "text": "Commit and push.", "mode": "followUp" }))
        .await;
    assert_eq!(sent["type"], "reply", "{sent}");
    tab.hear_until(|heard| heard.iter().any(|frame| frame.get("report").is_some()))
        .await;
    assert_eq!(
        git(&remote, &["rev-parse", "main"]),
        git(&work, &["rev-parse", "main"]),
        "the push ran without a question"
    );

    // A run with nothing irreversible.
    let sent = tab
        .request(json!({ "id": 3, "op": "prompt", "text": "Anything else?", "mode": "followUp" }))
        .await;
    assert_eq!(sent["type"], "reply", "{sent}");
    tab.hear_until(|heard| ends(heard) == 2).await;

    // The ledger; then `/undo` twice: the second prompt, then the first.
    let ledger = tab.run_text(4, json!({ "type": "get_ran_effects" })).await;
    let first_undo = tab.run_text(5, json!({ "type": "undo_turn" })).await;
    let second_undo = tab.run_text(6, json!({ "type": "undo_turn" })).await;
    assert_eq!(
        std::fs::read_to_string(work.join("notes.txt")).expect("read notes"),
        "one\n",
        "/undo restored the file"
    );

    let reports: Vec<Value> = tab
        .heard
        .iter()
        .filter_map(|frame| frame.get("report").cloned())
        .collect();
    assert_eq!(
        (reports, ledger, first_undo, second_undo),
        (
            vec![json!(format!(
                "Irreversible effects ran this run:\n{PUSH_LINE}"
            ))],
            json!(format!(
                "Irreversible effects ran in this session:\n{PUSH_LINE}"
            )),
            json!("Restored the workspace to the start of prompt 2 (0 paths).\n1 more prompt to undo."),
            json!(format!(
                "Restored the workspace to the start of prompt 1 (1 path).\n  notes.txt\nNothing more to undo.\nNot undone (irreversible):\n{PUSH_LINE}"
            )),
        )
    );
}
