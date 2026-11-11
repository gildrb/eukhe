//! A session whose kernel is missing. A venv that is not current: the
//! ipython tool answers with the install command, and the other tools run
//! (the model's laws `kernel_missing_names_install` and
//! `kernel_missing_spares_tools` in `laws/kernel_local.bend`; this test
//! runs the real session). No venv at all: the session offers no ipython
//! tool and reports a notification naming the install, which a client
//! shows once per install state; the session itself gets no entry.

use std::collections::HashMap;
use std::ffi::OsString;
use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep,
};
use eukhe_types::pi_ai::{JsonObject, Message, StopReason};
use serde_json::{json, Value};

use super::{KernelUnavailable, KERNEL_ENV_LOCK, KERNEL_INSTALL_COMMAND};
use crate::durable::compaction::auxiliary_model::show_notice_row;
use crate::durable::rlm::kernel_unavailable_notice::{notice_text, KERNEL_UNAVAILABLE_CUSTOM_TYPE};
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

/// The checkout's directory holding `eukhe-runtime/`: the runtime is
/// found whether or not the test binary runs inside the checkout.
fn checkout_package_dir() -> OsString {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .into_os_string()
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

/// A session whose kernel venv is not current and cannot be set up from
/// local files (its path is a file, so the local build fails before it
/// runs uv). Regression: a session's first ipython call downloaded Python
/// and the kernel packages; now the ipython tool answers with the install
/// command, and the other tools run.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_missing_kernel_names_the_install_and_spares_the_other_tools() {
    let _env_lock = KERNEL_ENV_LOCK.lock().await;
    let fixture = Fixture::new();
    let venv = fixture.dir.path().join("kernel-venv");
    std::fs::write(&venv, "").expect("the venv path as a file");
    let _env = KernelEnv::set(vec![
        ("EUKHE_KERNEL_VENV", Some(venv.into_os_string())),
        ("EUKHE_PACKAGE_DIR", Some(checkout_package_dir())),
        ("EUKHE_KERNEL_PYTHON", None),
    ]);
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
    let id = submit(&session, "go").await;
    settle(&session, id).await;
    let answers: Vec<&str> = results(&entries(&session).await)
        .iter()
        .map(|result| {
            if result_text(result).contains(KERNEL_INSTALL_COMMAND) {
                "install"
            } else if result.is_error {
                "error"
            } else {
                "ran"
            }
        })
        .collect();
    session.close(cx()).await.expect("close");
    assert_eq!(answers, ["ran", "install", "install", "ran"]);
}

/// Regression (Local Studio): a session whose kernel cannot start offered
/// the ipython tool, so the model's first call was a cell that could only
/// answer with the install command. Now the probe at open finds no kernel
/// venv: the model is offered no ipython tool and its prompt says the
/// session has no Python REPL. The user is told by a notification naming
/// the install, once per install state (a first-launch warning): at
/// the first interactive session, not the second, not once the venv
/// appears, and once more at the first session after it is gone again. A
/// reopened session does not show it again either, and a headless run
/// (print, json, rpc: no notification surface) neither shows it nor uses
/// it up.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_kernel_that_cannot_start_is_not_offered_and_notified_once() {
    let _env_lock = KERNEL_ENV_LOCK.lock().await;
    let fixture = Fixture::new();
    let venv = fixture.dir.path().join("kernel-venv");
    let _env = KernelEnv::set(vec![
        ("EUKHE_KERNEL_VENV", Some(venv.clone().into_os_string())),
        ("EUKHE_PACKAGE_DIR", Some(checkout_package_dir())),
        ("EUKHE_KERNEL_PYTHON", None),
    ]);
    let notice = notice_text(&KernelUnavailable::NotInstalled(venv.clone()));
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
    let first = open_and_ask(&fixture, &seen, Host::Interactive, fresh(1)).await;
    assert_eq!(first, (false, Some(notice.clone())));
    let reopened = open_and_ask(&fixture, &seen, Host::Interactive, fresh(1)).await;
    assert_eq!(reopened, (false, None));
    let second = open_and_ask(&fixture, &seen, Host::Interactive, fresh(2)).await;
    assert_eq!(second, (false, None));

    std::fs::create_dir(&venv).expect("a venv appears");
    let installed = open_and_ask(&fixture, &seen, Host::Interactive, fresh(3)).await;
    assert_eq!(installed, (true, None));

    std::fs::remove_dir(&venv).expect("the venv is gone again");
    let lost = open_and_ask(&fixture, &seen, Host::Interactive, fresh(4)).await;
    assert_eq!(lost, (false, Some(notice)));
    let after = open_and_ask(&fixture, &seen, Host::Interactive, fresh(5)).await;
    assert_eq!(after, (false, None));
}

/// Regression: the notice was a `kernel_unavailable` row the open wrote
/// into the first session of an install without the kernel, so that
/// session was not empty before the user typed anything (the TUI hid its
/// start banner, `/tree` opened an empty panel instead of saying "No
/// entries in session", rpc `get_state` counted one message). The open
/// writes no row; the session reports the notification instead.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_new_session_without_a_kernel_holds_no_notice_row() {
    let _env_lock = KERNEL_ENV_LOCK.lock().await;
    let fixture = Fixture::new();
    let venv = fixture.dir.path().join("kernel-venv");
    let _env = KernelEnv::set(vec![
        ("EUKHE_KERNEL_VENV", Some(venv.clone().into_os_string())),
        ("EUKHE_PACKAGE_DIR", Some(checkout_package_dir())),
        ("EUKHE_KERNEL_PYTHON", None),
    ]);
    let session = fixture
        .open_configured(|config| config.kernel_python = None)
        .await;
    assert_eq!(
        session.deps().kernel_unavailable_notice(),
        Some(notice_text(&KernelUnavailable::NotInstalled(venv)))
    );
    let rows = notices(&session).await;
    session.close(cx()).await.expect("close");
    assert_eq!(rows, Vec::new());
}

/// A session stored while the notice was still a row keeps it: it opens,
/// its next turn runs, the row stays where it was and no second one
/// joins it.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_session_stored_with_the_notice_row_still_opens() {
    let _env_lock = KERNEL_ENV_LOCK.lock().await;
    let fixture = Fixture::new();
    let venv = fixture.dir.path().join("kernel-venv");
    let _env = KernelEnv::set(vec![
        ("EUKHE_KERNEL_VENV", Some(venv.clone().into_os_string())),
        ("EUKHE_PACKAGE_DIR", Some(checkout_package_dir())),
        ("EUKHE_KERNEL_PYTHON", None),
    ]);
    let stored = notice_text(&KernelUnavailable::NotInstalled(venv));
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
    assert_eq!(
        rows[0].content,
        Some(eukhe_types::pi_ai::UserContent::Text(stored))
    );
    assert!(rows[0].display && !rows[0].input);
}

/// A working kernel is offered with no notice, even with no kernel venv:
/// the `EUKHE_KERNEL_PYTHON` override, or the session's own interpreter
/// (both the tests' kernel), starts it.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_working_kernel_is_offered_without_a_notice() {
    let _env_lock = KERNEL_ENV_LOCK.lock().await;
    let python = SessionConfig::new("agent", "work", "session", SessionStorage::Memory)
        .kernel_python
        .expect("the tests' kernel python");
    let fixture = Fixture::new();
    let _env = KernelEnv::set(vec![
        (
            "EUKHE_KERNEL_VENV",
            Some(fixture.dir.path().join("kernel-venv").into_os_string()),
        ),
        ("EUKHE_PACKAGE_DIR", Some(checkout_package_dir())),
        ("EUKHE_KERNEL_PYTHON", Some(python.into_os_string())),
    ]);
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
