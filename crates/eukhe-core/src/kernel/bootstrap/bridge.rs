//! The bridges between the kernel setup, the session's tools while the
//! kernel is missing, the bootstrap lock, and their Bend model
//! (`bend/kernel_local.bend`, whose laws `laws/kernel_local.bend` and
//! `PROOF.bend` prove): both run the same scenarios and must print the
//! same transcript, byte for byte. `bridge/bridge_kernel_local.bend`
//! documents the scenario format.
//!
//! A uv command is a fetch unless it has `--offline`; a fetch is hashed
//! when it has `--require-hashes` or is `uv python install` (uv checks a
//! Python download against the sha256 it pins for it).
//!
//! [`compare`] runs them (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::ffi::OsString;
use std::fmt::Write as _;
use std::path::Path;

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_tool_call, FauxAssistantMessageOptions, FauxResponseStep,
};
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::pi_ai::{JsonObject, StopReason};
use serde_json::{json, Value};

use super::dir_lock::{sweep_leftovers, try_acquire_dir_lock, DirLockAttempt};
use super::setup::{setup_step, Found, KernelSetup, SetupStep};
use super::venv::{skill_install_args, venv_build_commands};
use super::{format_setup_failure, KERNEL_ENV_LOCK, KERNEL_INSTALL_COMMAND};
use crate::durable::rlm::tests::{
    cx, entries, result_text, results, settle, submit, text, Fixture,
};

/// One uv command as the model reads it.
fn act(args: &[String]) -> &'static str {
    let has = |flag: &str| args.iter().any(|arg| arg == flag);
    if has("--offline") {
        " o"
    } else if has("--require-hashes") || args.starts_with(&["python".into(), "install".into()]) {
        " f1"
    } else {
        " f0"
    }
}

/// The setup bridge: every venv found, both setups, a sync or build that
/// works or fails; the actions and the kernel after them.
#[test]
fn the_rust_setup_equals_the_bend_model() {
    let venv = Path::new("/state/kernel-venv");
    let source = Path::new("/opt/eukhe/eukhe-runtime");
    let python = "/state/kernel-venv/bin/python";
    let mut scenarios = Vec::new();
    for (found, found_code) in [
        (Found::Ready, 0),
        (Found::SkillsStale, 1),
        (Found::Stale, 2),
    ] {
        for (setup, setup_code) in [(KernelSetup::Local, 0), (KernelSetup::Install, 1)] {
            for ok in [true, false] {
                let step = setup_step(found, setup);
                let mut transcript = String::from("a");
                let worked = match step {
                    SetupStep::Use => true,
                    SetupStep::SyncSkills => {
                        transcript.push_str(act(&skill_install_args(python, &[])));
                        ok
                    }
                    SetupStep::Build(fetch) => {
                        for command in venv_build_commands(venv, python, source, fetch) {
                            transcript.push_str(act(&command));
                        }
                        transcript.push_str(" c");
                        ok
                    }
                };
                transcript.push_str(" r\nk ");
                if worked {
                    transcript.push_str("up\n");
                } else if format_setup_failure(&anyhow::anyhow!("no uv cache"), setup)
                    .to_string()
                    .contains(KERNEL_INSTALL_COMMAND)
                {
                    transcript.push_str("missing\n");
                } else {
                    transcript.push_str("other\n");
                }
                scenarios.push(Scenario {
                    name: format!("{found:?}-{setup:?}-{ok}"),
                    events: format!("p {found_code} {setup_code}\no {}\n", u8::from(ok)),
                    transcript,
                });
            }
        }
    }
    compare("bridge/bridge_kernel_local.bend", scenarios);
}

/// A pid with no process: a child that already exited.
fn dead_pid() -> u32 {
    let mut child = std::process::Command::new("true")
        .spawn()
        .expect("spawn `true`");
    let pid = child.id();
    child.wait().expect("wait for `true`");
    pid
}

/// The lock bridge: a lock that is free or held by a live or dead owner,
/// and leftovers of live and dead attempts beside other files; the sweep
/// and one attempt, then the attempt's end, its own leftovers, and the
/// files the sweep kept.
#[test]
fn the_rust_lock_equals_the_bend_model() {
    let live = std::process::id();
    let dead = dead_pid();
    let mut rng = Rng(0x10c4_ca1e);
    let mut scenarios = Vec::new();
    for at in 0..40 {
        let dir = tempfile::tempdir().expect("temp dir");
        let lock = dir.path().join("kernel-venv.bootstrap.lock");
        let lock_name = "kernel-venv.bootstrap.lock";
        let lock_code = rng.below(3);
        let mut events = format!("l {lock_code}\n");
        match lock_code {
            0 => {}
            1 => std::fs::write(&lock, format!("{live}\n")).expect("live lock"),
            _ => std::fs::write(&lock, format!("{dead}\n")).expect("dead lock"),
        }
        let mut files = Vec::new();
        for file in 0..rng.range(0, 6) {
            let kind = rng.below(3);
            let alive = rng.below(2);
            let pid = if alive == 1 { live } else { dead };
            let name = match kind {
                0 => format!("{lock_name}.candidate-{pid}-ev{file}"),
                1 => format!("{lock_name}.stale-{pid}-ev{file}"),
                _ => format!("{lock_name}.candidate-x{pid}-ev{file}"),
            };
            std::fs::write(dir.path().join(&name), format!("{pid}\n")).expect("leftover");
            writeln!(events, "f {kind} {alive}").unwrap();
            files.push((name, kind, alive));
        }
        sweep_leftovers(&lock);
        let end = match try_acquire_dir_lock(&lock).expect("an attempt") {
            DirLockAttempt::Acquired => "got",
            DirLockAttempt::Held => "busy",
            DirLockAttempt::Reclaimed => "freed",
        };
        let own = std::fs::read_dir(dir.path())
            .expect("the lock dir")
            .filter_map(Result::ok)
            .filter(|entry| {
                let name = entry.file_name().to_string_lossy().into_owned();
                name != lock_name && !name.contains("-ev")
            })
            .count();
        let mut transcript = format!("e {end}\nw {own}\n");
        for (name, kind, alive) in files {
            if dir.path().join(name).exists() {
                writeln!(transcript, "s {kind} {alive}").unwrap();
            }
        }
        scenarios.push(Scenario {
            name: format!("{at}"),
            events,
            transcript,
        });
    }
    compare("bridge/bridge_kernel_local.bend", scenarios);
}

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

/// The tools bridge: a session whose kernel venv is missing and cannot be
/// set up from local files (its path is a file, so the local build fails
/// before it runs uv). Regression: a session's first ipython call
/// downloaded Python and the kernel packages; now the ipython tool
/// answers with the install command, and the other tools run.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_missing_kernel_answers_as_its_model() {
    let _env_lock = KERNEL_ENV_LOCK.lock().await;
    let mut rng = Rng(0x0ff1_1e0c);
    let mut scenarios = Vec::new();
    for at in 0..4 {
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
        let tools: Vec<u64> = (0..rng.range(1, 4)).map(|_| rng.below(3)).collect();
        let mut events = String::from("k 0\n");
        let mut steps = Vec::new();
        for (index, &tool) in tools.iter().enumerate() {
            writeln!(events, "t {tool}").unwrap();
            let id = format!("call-{index}");
            steps.push(match tool {
                0 => call("ipython", &id, json!({ "code": "print('ran')" })),
                n => call("bash", &id, json!({ "script": format!("echo {n}") })),
            });
        }
        steps.push(text("done"));
        fixture.faux.set_responses(steps);
        let session = fixture
            .open_configured(|config| config.kernel_python = None)
            .await;
        let id = submit(&session, "go").await;
        settle(&session, id).await;
        let mut transcript = String::new();
        for result in results(&entries(&session).await) {
            let answer = if result_text(&result).contains(KERNEL_INSTALL_COMMAND) {
                "install"
            } else if result.is_error {
                "error"
            } else {
                "ran"
            };
            writeln!(transcript, "t {answer}").unwrap();
        }
        session.close(cx()).await.expect("close");
        scenarios.push(Scenario {
            name: format!("tools-{at}"),
            events,
            transcript,
        });
    }
    compare("bridge/bridge_kernel_local.bend", scenarios);
}
