//! A session and the pinned Python its kernel runs on, without network
//! (the fetch itself, the pinned version on a machine with other Pythons,
//! and the locked package installs run against the real binary in
//! `crates/eukhe-cli/tests/packaged_layout_e2e.rs`). A machine that has not
//! fetched the Python and is offline: the session offers no ipython tool
//! and reports one notification saying the fetch failed. A fetch that fails
//! between the open and the first call: the ipython tool answers with the
//! failed fetch, and the other tools run (the model's laws on a failed
//! setup in `laws/kernel_local.bend`; these tests run the real session).

use std::collections::HashMap;
use std::ffi::OsString;
use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep,
};
use eukhe_types::pi_ai::{JsonObject, Message, StopReason, UserContent};
use serde_json::{json, Value};

use super::{KERNEL_ENV_LOCK, KERNEL_FETCH_FAILED, KERNEL_INSTALL_COMMAND};
use crate::durable::compaction::auxiliary_model::show_notice_row;
use crate::durable::rlm::kernel_unavailable_notice::KERNEL_UNAVAILABLE_CUSTOM_TYPE;
use crate::durable::rlm::tests::{
    cx, entries, result_text, results, settle, submit, text, Fixture,
};
use crate::durable::{CustomEntryData, EukheSession, SessionConfig, SessionStorage, CUSTOM_ENTRY};

/// Sets the kernel env of a test and puts the old values back when the
/// test ends, also when it fails.
struct KernelEnv(Vec<(&'static str, Option<OsString>)>);

impl Drop for KernelEnv {
    fn drop(&mut self) {
        for (name, value) in self.0.drain(..) {
            match value {
                Some(value) => std::env::set_var(name, value),
                None => std::env::remove_var(name),
            }
        }
    }
}

impl KernelEnv {
    /// Set each variable (`None`: unset it) until the guard drops.
    fn set(vars: Vec<(&'static str, Option<OsString>)>) -> Self {
        let mut old = Vec::with_capacity(vars.len());
        for (name, value) in vars {
            old.push((name, std::env::var_os(name)));
            match value {
                Some(value) => std::env::set_var(name, value),
                None => std::env::remove_var(name),
            }
        }
        Self(old)
    }
}

/// The tests' own kernel interpreter (built before a test moves `HOME`).
fn tests_python() -> OsString {
    SessionConfig::new("agent", "work", "session", SessionStorage::Memory)
        .kernel_python
        .expect("the tests' kernel python")
        .into_os_string()
}

/// The kernel env of an offline machine that never fetched the Python: a
/// new `HOME` (an empty `~/.eukhe/kernel`), no override, `EUKHE_OFFLINE`.
fn offline_machine(home: &Path) -> KernelEnv {
    tests_python();
    std::fs::create_dir_all(home).expect("the fresh HOME");
    let checkout = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .into_os_string();
    KernelEnv::set(vec![
        ("HOME", Some(home.as_os_str().to_owned())),
        ("EUKHE_KERNEL_DIR", None),
        ("EUKHE_KERNEL_PYTHON", None),
        ("XDG_DATA_HOME", None),
        ("EUKHE_OFFLINE", Some(OsString::from("1"))),
        ("EUKHE_PACKAGE_DIR", Some(checkout)),
    ])
}

/// The tool names and the prompt sections in force at each model request.
type Seen = Arc<Mutex<Vec<(Vec<String>, String)>>>;

/// A model step that records what the request offered (the tools and the
/// prompt sections after every system message's additions, removals and
/// replacements), then answers.
fn recorded(seen: &Seen) -> FauxResponseStep {
    let seen = Arc::clone(seen);
    let reply = faux_assistant_message(
        vec![faux_text("done")],
        FauxAssistantMessageOptions::default(),
    );
    FauxResponseStep::factory(move |context, _, _, _| {
        let mut tools: Vec<String> = Vec::new();
        let mut sections: HashMap<String, String> = HashMap::new();
        for message in context.messages() {
            let Message::System(system) = message else {
                continue;
            };
            for removed in system.tools_removed.iter().flatten() {
                tools.retain(|name| *name != removed.name);
            }
            tools.extend(
                system
                    .tools_added
                    .iter()
                    .flatten()
                    .map(|tool| tool.name.clone()),
            );
            for (key, text) in system.sections.iter().flatten() {
                match text {
                    Some(text) => sections.insert(key.clone(), text.clone()),
                    None => sections.remove(key),
                };
            }
        }
        let prompt = sections.into_values().collect::<Vec<_>>().join("\n\n");
        seen.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push((tools, prompt));
        Ok(reply.clone())
    })
}

/// The kernel-unavailable rows of the session's main conversation.
async fn notices(session: &EukheSession) -> Vec<CustomEntryData> {
    entries(session)
        .await
        .into_iter()
        .filter_map(|entry| CUSTOM_ENTRY.narrow(entry).expect("custom data"))
        .map(|entry| entry.data().clone())
        .filter(|data| data.custom_type == KERNEL_UNAVAILABLE_CUSTOM_TYPE)
        .collect()
}

/// Who has the session open.
#[derive(Clone, Copy)]
enum Host {
    /// An interactive client is attached: it shows the session's
    /// notification the first time since the kernel was last usable
    /// (what the TUI does at its attach).
    Interactive,
    /// Print, json or rpc mode: nothing shows a notification.
    Headless,
}

/// One open of the fixture's session with one model turn: whether the
/// model was offered `ipython` (its request's tools, checked against the
/// agent's), and the notification `host` showed. No open leaves a
/// kernel-unavailable row in the session.
async fn open_and_ask(
    fixture: &Fixture,
    seen: &Seen,
    host: Host,
    configure: impl FnOnce(&mut SessionConfig),
) -> (bool, Option<String>) {
    fixture.faux.set_responses(vec![recorded(seen)]);
    let session = fixture.open_configured(configure).await;
    let shown = match host {
        Host::Interactive => session
            .deps()
            .kernel_unavailable_notice()
            .filter(|_| eukhe_types::kernel_notice::first_showing(&session.deps().agent_dir)),
        Host::Headless => None,
    };
    let id = submit(&session, "list the files here").await;
    settle(&session, id).await;
    let agent = session.main().agent(cx()).await.expect("agent");
    let offered = agent.tools.iter().any(|tool| tool.name == "ipython");
    let rows = notices(&session).await;
    session.close(cx()).await.expect("close");
    assert_eq!(rows, Vec::new(), "the notice is no session entry");
    let (tools, prompt) = seen
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .pop()
        .expect("one model request");
    assert_eq!(tools.iter().any(|tool| tool == "ipython"), offered);
    assert_eq!(
        prompt.contains("This session has no Python REPL (`ipython` tool)"),
        !offered
    );
    (offered, shown)
}

/// A model step that calls `tool` with `arguments`.
fn call(tool: &str, id: &str, arguments: Value) -> FauxResponseStep {
    let Value::Object(arguments) = arguments else {
        unreachable!("an object literal");
    };
    faux_assistant_message(
        vec![faux_tool_call(
            tool,
            arguments.into_iter().collect::<JsonObject>(),
            Some(id.to_owned()),
        )],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

/// Is `notice` the notification of a fetch that failed because the
/// machine is offline.
fn is_offline_notice(notice: &str) -> bool {
    notice.starts_with(&format!(
        "The Python kernel cannot start: {KERNEL_FETCH_FAILED}: EUKHE_OFFLINE is set and uv {} is not fetched yet.",
        super::pinned_uv_version()
    )) && notice.contains(&format!("CPython {}", super::pinned_python_version()))
        && notice.contains(KERNEL_INSTALL_COMMAND)
        && notice.ends_with(
            "This session has no `ipython` tool; the other tools work. The next session tries the fetch again.",
        )
}

/// Regression (Local Studio): a session whose kernel cannot start offered
/// the ipython tool. The kernel's Python is fetched on its own, so the
/// only machine without a kernel is one that never fetched it and is
/// offline: there the model is offered no ipython tool, its prompt says
/// the session has no Python REPL, and the user is told by a notification
/// saying the fetch failed, once per state: at the first interactive
/// session, not a reopened one, not the second, not once a kernel works,
/// and once more at the first session after it is gone again. A headless
/// run (print, json, rpc) neither shows it nor uses it up.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn offline_without_the_python_is_not_offered_and_notified_once() {
    let _env_lock = KERNEL_ENV_LOCK.lock().await;
    let python = tests_python();
    let fixture = Fixture::new();
    let home = fixture.dir.path().join("home");
    let _env = offline_machine(&home);
    let seen = Seen::default();
    // A fresh session of the fixture's install: its own id and storage.
    let fresh = |n: u8| {
        let dir = fixture
            .dir
            .path()
            .join("sessions")
            .join(format!("fresh-{n}"));
        move |config: &mut SessionConfig| {
            config.kernel_python = None;
            config.session_id = format!("019a0000-0000-7000-8000-0000000001{n:02}");
            config.storage = SessionStorage::Jsonl { dir, fsync: false };
        }
    };

    let headless = open_and_ask(&fixture, &seen, Host::Headless, fresh(0)).await;
    assert_eq!(headless, (false, None));
    let (offered, shown) = open_and_ask(&fixture, &seen, Host::Interactive, fresh(1)).await;
    assert!(!offered);
    assert!(shown.as_deref().is_some_and(is_offline_notice), "{shown:?}");
    let reopened = open_and_ask(&fixture, &seen, Host::Interactive, fresh(1)).await;
    assert_eq!(reopened, (false, None));
    let second = open_and_ask(&fixture, &seen, Host::Interactive, fresh(2)).await;
    assert_eq!(second, (false, None));
    assert!(
        !home.join(".eukhe").join("kernel").join("uv").exists(),
        "an offline machine fetches nothing"
    );

    std::env::set_var("EUKHE_KERNEL_PYTHON", &python);
    let usable = open_and_ask(&fixture, &seen, Host::Interactive, fresh(3)).await;
    assert_eq!(usable, (true, None));

    std::env::remove_var("EUKHE_KERNEL_PYTHON");
    let (offered, lost) = open_and_ask(&fixture, &seen, Host::Interactive, fresh(4)).await;
    assert!(!offered);
    assert!(lost.as_deref().is_some_and(is_offline_notice), "{lost:?}");
    let after = open_and_ask(&fixture, &seen, Host::Interactive, fresh(5)).await;
    assert_eq!(after, (false, None));
}

/// The open writes no notice row into a new session of an offline machine
/// without the Python (the row made the TUI hide its start banner, `/tree`
/// open an empty panel, rpc `get_state` count one message); the session
/// reports the notification instead.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_new_session_without_the_python_holds_no_notice_row() {
    let _env_lock = KERNEL_ENV_LOCK.lock().await;
    let fixture = Fixture::new();
    let home = fixture.dir.path().join("home");
    let _env = offline_machine(&home);
    let session = fixture
        .open_configured(|config| config.kernel_python = None)
        .await;
    let notice = session.deps().kernel_unavailable_notice();
    let rows = notices(&session).await;
    session.close(cx()).await.expect("close");
    assert!(
        notice.as_deref().is_some_and(is_offline_notice),
        "{notice:?}"
    );
    assert_eq!(rows, Vec::new());
}

/// A session stored while the notice was still a row keeps it: it opens,
/// its next turn runs, the row stays where it was and no second one
/// joins it.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_session_stored_with_the_notice_row_still_opens() {
    let _env_lock = KERNEL_ENV_LOCK.lock().await;
    let fixture = Fixture::new();
    let home = fixture.dir.path().join("home");
    let _env = offline_machine(&home);
    let stored =
        "The Python kernel is not installed, so this session has no `ipython` tool.".to_owned();
    let session = fixture
        .open_configured(|config| config.kernel_python = None)
        .await;
    show_notice_row(
        &session.main(),
        KERNEL_UNAVAILABLE_CUSTOM_TYPE,
        stored.clone(),
        cx(),
    )
    .await;
    session.close(cx()).await.expect("close");

    fixture.faux.set_responses(vec![text("done")]);
    let session = fixture
        .open_configured(|config| config.kernel_python = None)
        .await;
    let id = submit(&session, "go on").await;
    settle(&session, id).await;
    let rows = notices(&session).await;
    session.close(cx()).await.expect("close");
    assert_eq!(rows.len(), 1, "the stored row, and no new one: {rows:?}");
    assert_eq!(rows[0].content, Some(UserContent::Text(stored)));
    assert!(rows[0].display && !rows[0].input);
}

/// A fetch that fails between the open and the first call (the session
/// opened with a kernel; the machine then has none and is offline): the
/// ipython tool answers with the failed fetch and the command that
/// retries it, and the other tools run.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_failed_fetch_answers_the_ipython_tool_and_spares_the_other_tools() {
    let _env_lock = KERNEL_ENV_LOCK.lock().await;
    let python = tests_python();
    let fixture = Fixture::new();
    let home = fixture.dir.path().join("home");
    let _env = offline_machine(&home);
    std::env::set_var("EUKHE_KERNEL_PYTHON", &python);
    fixture.faux.set_responses(vec![
        call("bash", "call-0", json!({ "script": "echo 1" })),
        call("ipython", "call-1", json!({ "code": "print('ran')" })),
        call("ipython", "call-2", json!({ "code": "print('ran')" })),
        call("bash", "call-3", json!({ "script": "echo 2" })),
        text("done"),
    ]);
    let session = fixture
        .open_configured(|config| config.kernel_python = None)
        .await;
    std::env::remove_var("EUKHE_KERNEL_PYTHON");
    let id = submit(&session, "go").await;
    settle(&session, id).await;
    let answers: Vec<&str> = results(&entries(&session).await)
        .iter()
        .map(|result| {
            let text = result_text(result);
            if text.contains(KERNEL_FETCH_FAILED) && text.contains(KERNEL_INSTALL_COMMAND) {
                "fetch failed"
            } else if result.is_error {
                "error"
            } else {
                "ran"
            }
        })
        .collect();
    session.close(cx()).await.expect("close");
    assert_eq!(answers, ["ran", "fetch failed", "fetch failed", "ran"]);
}

/// A working kernel is offered with no notice on a machine without the
/// pinned Python: the `EUKHE_KERNEL_PYTHON` override, or the session's own
/// interpreter (both the tests' kernel), starts it.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_named_interpreter_is_offered_without_a_notice() {
    let _env_lock = KERNEL_ENV_LOCK.lock().await;
    let python = tests_python();
    let fixture = Fixture::new();
    let home = fixture.dir.path().join("home");
    let _env = offline_machine(&home);
    std::env::set_var("EUKHE_KERNEL_PYTHON", python);
    let seen = Seen::default();
    let overridden = open_and_ask(&fixture, &seen, Host::Interactive, |config| {
        config.kernel_python = None;
    })
    .await;
    assert_eq!(overridden, (true, None));
    std::env::remove_var("EUKHE_KERNEL_PYTHON");
    let configured = open_and_ask(&fixture, &seen, Host::Interactive, |_| {}).await;
    assert_eq!(configured, (true, None));
}
