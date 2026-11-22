//! The runners of code: the registry a session installs against the
//! compiled core's (`bend/runners.bend` `registry`, entry
//! `bend/ffi_runners.bend`), and a `python` cell on a real kernel.

use std::sync::Arc;

use eukhe_bend::rules::runners::{self, ChatMemory, Covered};
use eukhe_durable::harness::types::RegistryReader;
use eukhe_types::shell::ShellEffects;
use serde_json::json;

use super::{Gate, Runner};
use crate::durable::rlm::kernel_test_lock;
use crate::durable::rlm::tests::{
    entries, python, result_text, results, settle, submit, text, Fixture,
};
use crate::durable::{EukheSession, SessionRole};
use crate::memory::{Memory, ResponseStarted, Summarizer, SummarizerFuture};

/// Every tool of the session's registry: its name, caps and gate.
fn dump(session: &EukheSession) -> Vec<(String, ShellEffects, Covered)> {
    session
        .registry()
        .snapshot()
        .tools()
        .iter()
        .map(|installed| {
            let tool = &installed.tool;
            let (caps, gate) = match tool.extra::<Runner>() {
                Some(runner) => (
                    runner.caps,
                    match runner.gate {
                        Gate::EachStep => Covered::EachStep,
                        Gate::EachCall => Covered::EachCall,
                    },
                ),
                None => (ShellEffects::NONE, Covered::Ungated),
            };
            (tool.name.clone(), caps, gate)
        })
        .collect()
}

/// A chat memory compactor with no model (the registry test sends no turn).
struct NoModel;

impl Summarizer for NoModel {
    fn complete(
        &self,
        _context: eukhe_types::pi_ai::Context,
        _started: ResponseStarted,
    ) -> SummarizerFuture {
        Box::pin(async { Err(anyhow::anyhow!("no model in this test")) })
    }
}

/// The real registry of a session without and with chat memory is the
/// compiled core's one registry (`registry`, whose laws
/// `gate_covers_every_runner` and `python_gated_each_call` pin it): chat
/// memory adds no tool, so a subagent offers its parent's tool list.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_registry_is_its_model() {
    let fixture = Fixture::new();
    let classic = fixture.open_configured(|_| {}).await;
    let fixture = Fixture::new();
    let memory = Memory::open(fixture.dir.path().join("chat"), Arc::new(NoModel))
        .await
        .expect("chat memory");
    let chat = fixture
        .open_configured(move |config| config.memory = Some(memory))
        .await;
    let model: Vec<_> = runners::registry()
        .into_iter()
        .map(|tool| (tool.name, tool.caps, tool.gate))
        .collect();
    assert_eq!((dump(&classic), dump(&chat)), (model.clone(), model));
}

/// The roster of a session opened under `settings` (`settings.json`) as
/// `role`, with chat memory or not: name, caps and gate of each tool.
async fn roster_of(
    settings: serde_json::Value,
    role: SessionRole,
    chat: ChatMemory,
) -> Vec<(String, ShellEffects, Covered)> {
    let fixture = Fixture::new();
    std::fs::write(
        fixture.dir.path().join("agent").join("settings.json"),
        settings.to_string(),
    )
    .expect("settings");
    let memory = match chat {
        ChatMemory::On => Some(
            Memory::open(fixture.dir.path().join("chat"), Arc::new(NoModel))
                .await
                .expect("chat memory"),
        ),
        ChatMemory::Off => None,
    };
    let session = fixture
        .open_configured(move |config| {
            config.role = role;
            config.memory = memory;
        })
        .await;
    dump(&session)
}

/// The tool surface is decided by role and shape when the session opens:
/// a root in the `main-worker` shape offers the compiled core's main
/// roster (read-only tools and the worker tools, with and without chat
/// memory); a `single` root and a child of a `main-worker` family offer
/// the full registry, which has no worker tool.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_tool_surface_follows_role_and_shape() {
    let main_worker = json!({ "sessionShape": "main-worker" });
    let single = json!({ "sessionShape": "single" });
    let child = SessionRole {
        rlm_depth: 1,
        rlm_max_depth: 2,
        ..SessionRole::default()
    };
    let model = |tools: Vec<runners::Tool>| {
        tools
            .into_iter()
            .map(|tool| (tool.name, tool.caps, tool.gate))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        (
            roster_of(main_worker.clone(), SessionRole::default(), ChatMemory::On).await,
            roster_of(main_worker.clone(), SessionRole::default(), ChatMemory::Off).await,
            roster_of(single, SessionRole::default(), ChatMemory::On).await,
            roster_of(main_worker, child, ChatMemory::Off).await,
        ),
        (
            model(runners::main_roster(ChatMemory::On)),
            model(runners::main_roster(ChatMemory::Off)),
            model(runners::registry()),
            model(runners::registry()),
        )
    );
}

/// Regression (audit C1): an `python` cell ran outside any rule. Now a
/// cell runs unasked as every runner of code does: its marker file is
/// written and the model reads its output.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_cell_runs_unasked() {
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    let mark = fixture.dir.path().join("mark");
    let code =
        format!("import pathlib\npathlib.Path({mark:?}).write_text('ran')\nprint('cell ran')");
    fixture
        .faux
        .set_responses(vec![python("c1", &code), text("done")]);
    let session = fixture.open_configured(|_| {}).await;
    let id = submit(&session, "go").await;
    settle(&session, id).await;
    let all = results(&entries(&session).await);
    assert_eq!(
        all.iter()
            .map(|result| (result_text(result), result.is_error))
            .collect::<Vec<_>>(),
        vec![("cell ran\n".to_owned(), false)]
    );
    assert_eq!(std::fs::read_to_string(&mark).expect("the cell ran"), "ran");
}
