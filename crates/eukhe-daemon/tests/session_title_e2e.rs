//! The generated session title (the `tiny` role)
//! through the real daemon: the first prompt of a new top-level session
//! starts the worker's background title (`worker/title.rs`), the title
//! lands as the session name (`session_info_changed`, the `list`
//! summary), and `titles.generate: false` produces none. The supervisor
//! runs on a temp socket and agent dir; the session's provider is the
//! scripted OpenAI-compatible mock. No tiny model is installed in the temp
//! agent dir, so the role's chain ends on the session's provider model,
//! the mock.

use std::time::Duration;

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/isolated_supervisor.rs"]
mod isolated_supervisor;
#[path = "support/mock_llm.rs"]
mod mock_llm;
#[path = "support/process.rs"]
mod process;
#[path = "support/wire_client.rs"]
mod wire_client;

use isolated_supervisor::Supervisor;
use mock_llm::{MockLlm, Reply, Request};
use wire_client::WireClient;

const MODEL: &str = "mock-1";

/// The start of the title request's system prompt
/// (`eukhe_tiny::TITLE_SYSTEM_PROMPT`).
const TITLE_MARKER: &str = "You name conversations.";

const FIRST_PROMPT: &str = "How do I resize a btrfs partition on an encrypted LUKS volume?";

const BUDGET: Duration = Duration::from_mins(3);

fn is_title_request(request: &Request) -> bool {
    request.body.to_string().contains(TITLE_MARKER)
}

/// The title request gets a title; everything else an answer.
fn script(request: &Request) -> Reply {
    if is_title_request(request) {
        Reply::text("<title>Resizing Btrfs on LUKS</title>")
    } else {
        Reply::text("Grow the LUKS mapping first, then the filesystem.")
    }
}

/// A supervisor with one new, attached top-level session on the mock.
struct Session {
    // Dropped last: the supervisor and the mock use its paths.
    _dir: tempfile::TempDir,
    _supervisor: Supervisor,
    mock: MockLlm,
    client: WireClient,
    id: String,
}

impl Session {
    fn start(settings: &Value) -> Session {
        let dir = tempfile::tempdir().expect("temp dir");
        let agent_dir = dir.path().join("agent");
        let session_dir = agent_dir.join("sessions");
        std::fs::create_dir_all(&session_dir).expect("session dir");
        let mock = MockLlm::start(script);
        std::fs::write(agent_dir.join("settings.json"), settings.to_string()).expect("settings");
        std::fs::write(
            agent_dir.join("models.json"),
            mock.models_json(MODEL, 128_000, 2_048).to_string(),
        )
        .expect("models.json");
        let socket = dir.path().join("daemon.sock");
        let supervisor = Supervisor::start(&socket, &agent_dir, &dir.path().join("supervisor.log"));
        let mut client = WireClient::connect(&socket);
        let created = client.request(
            &json!({ "type": "create", "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": session_dir.to_string_lossy(),
                "provider": "mock",
                "model": MODEL,
            }}),
            BUDGET,
        );
        assert_eq!(created["success"], true, "create: {created}");
        let id = created["data"]["activeSessionId"]
            .as_str()
            .expect("session id")
            .to_owned();
        let attached = client.request(&json!({ "type": "attach", "activeSessionId": id }), BUDGET);
        assert_eq!(attached["success"], true, "attach: {attached}");
        Session {
            _dir: dir,
            _supervisor: supervisor,
            mock,
            client,
            id,
        }
    }

    /// Runs the first prompt to its end.
    fn first_prompt(&mut self) {
        let done = self.client.request(
            &json!({
                "type": "prompt_and_wait", "activeSessionId": self.id, "message": FIRST_PROMPT,
            }),
            BUDGET,
        );
        assert_eq!(done["success"], true, "prompt: {done}");
    }

    /// The session's `list` summary name.
    fn listed_name(&mut self) -> Option<String> {
        let listed = self.client.request(&json!({ "type": "list" }), BUDGET);
        assert_eq!(listed["success"], true, "list: {listed}");
        let sessions = listed["data"]["sessions"].as_array().expect("sessions");
        let summary = sessions
            .iter()
            .find(|summary| summary["activeSessionId"] == self.id.as_str())
            .unwrap_or_else(|| panic!("the session is listed: {listed}"));
        summary["sessionName"].as_str().map(str::to_owned)
    }

    /// The user text of each title request the mock got.
    fn title_requests(&self) -> Vec<String> {
        self.mock
            .log()
            .iter()
            .filter(|entry| is_title_request(&entry.request))
            .map(|entry| entry.request.prompt.clone())
            .collect()
    }

    /// The names of the `session_info_changed` events so far.
    fn renames(&self) -> Vec<Option<String>> {
        self.client
            .events_from(0)
            .iter()
            .filter(|event| event["type"] == "session_info_changed")
            .map(|event| event["name"].as_str().map(str::to_owned))
            .collect()
    }
}

#[test]
fn the_first_prompt_titles_the_session() {
    let mut session = Session::start(&json!({}));
    session.first_prompt();
    session
        .client
        .wait_event_from(0, BUDGET, "the session title", |event| {
            event["type"] == "session_info_changed"
        });
    assert_eq!(
        (
            session.renames(),
            session.listed_name(),
            session.title_requests()
        ),
        (
            vec![Some("Resizing Btrfs on LUKS".to_owned())],
            Some("Resizing Btrfs on LUKS".to_owned()),
            vec![FIRST_PROMPT.to_owned()],
        )
    );
}

#[test]
fn titles_generate_false_titles_nothing() {
    let mut session = Session::start(&json!({ "titles": { "generate": false } }));
    session.first_prompt();
    // A title that is never made has no event to wait for. The title task
    // starts when the prompt arrives and reads `titles.generate` before
    // any request; these checks run after the whole turn settled.
    assert_eq!(
        (
            session.renames(),
            session.listed_name(),
            session.title_requests()
        ),
        (Vec::new(), None, Vec::<String>::new())
    );
}
