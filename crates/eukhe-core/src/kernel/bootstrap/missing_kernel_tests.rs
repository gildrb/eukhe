//! A session whose kernel is missing: the ipython tool answers with the
//! install command, and the other tools run (the model's laws
//! `kernel_missing_names_install` and `kernel_missing_spares_tools` in
//! `laws/kernel_local.bend`; this test runs the real session).

use std::ffi::OsString;

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_tool_call, FauxAssistantMessageOptions, FauxResponseStep,
};
use eukhe_types::pi_ai::{JsonObject, StopReason};
use serde_json::{json, Value};

use super::{KERNEL_ENV_LOCK, KERNEL_INSTALL_COMMAND};
use crate::durable::rlm::tests::{
    cx, entries, result_text, results, settle, submit, text, Fixture,
};

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

/// A session whose kernel venv is missing and cannot be set up from local
/// files (its path is a file, so the local build fails before it runs
/// uv). Regression: a session's first ipython call downloaded Python and
/// the kernel packages; now the ipython tool answers with the install
/// command, and the other tools run.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_missing_kernel_names_the_install_and_spares_the_other_tools() {
    let _env_lock = KERNEL_ENV_LOCK.lock().await;
    let fixture = Fixture::new();
    let venv = fixture.dir.path().join("kernel-venv");
    std::fs::write(&venv, "").expect("the venv path as a file");
    let _env = KernelEnv(vec![
        ("EUKHE_KERNEL_VENV", std::env::var_os("EUKHE_KERNEL_VENV")),
        (
            "EUKHE_KERNEL_PYTHON",
            std::env::var_os("EUKHE_KERNEL_PYTHON"),
        ),
    ]);
    std::env::set_var("EUKHE_KERNEL_VENV", &venv);
    std::env::remove_var("EUKHE_KERNEL_PYTHON");
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
