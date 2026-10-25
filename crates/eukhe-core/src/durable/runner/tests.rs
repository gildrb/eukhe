//! The runners of code: the registry a session installs against the
//! compiled core's (`bend/runners.bend` `registry`, entry
//! `bend/ffi_runners.bend`), and the `ipython` gate on a real kernel.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_bend::rules::runners::{self, ChatMemory, Covered};
use eukhe_durable::harness::types::RegistryReader;
use eukhe_types::pi_ai::ToolResultMessage;
use eukhe_types::shell::{ShellAnswer, ShellApprovalRequest, ShellEffect, ShellEffects};
use futures::FutureExt;
use serde_json::json;

use super::{Gate, Runner};
use crate::durable::rlm::kernel_test_lock;
use crate::durable::rlm::tests::{
    entries, ipython, result_text, results, settle, submit, text, Fixture,
};
use crate::durable::{EukheSession, SessionRole, ShellApprovalSink};
use crate::memory::{Memory, ResponseStarted, Summarizer, SummarizerFuture};

/// What a denied cell's call says.
const DENIED: &str =
    "ipython did not run (exec): the user denied it. Do not try it again unless the user asks for it.";

/// What an unanswered cell's call says.
const UNANSWERED: &str = "ipython did not run (exec): it needs the user's approval, and no client \
answered. Ask the user to attach a client, or to allow its effect in shell.autoEffects if that is \
not secret; or use read-only steps.";

/// Who answers a call's question.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Asker {
    NoClient,
    Deny,
}

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
/// compiled core's (`registry`, whose laws `gate_covers_every_runner` and
/// `ipython_gated_each_call` pin it).
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
    let model = |chat| {
        runners::registry(chat)
            .into_iter()
            .map(|tool| (tool.name, tool.caps, tool.gate))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        (dump(&classic), dump(&chat)),
        (model(ChatMemory::Off), model(ChatMemory::On))
    );
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
            model(runners::registry(ChatMemory::On)),
            model(runners::registry(ChatMemory::Off)),
        )
    );
}

/// One `ipython` call of `code` under `auto`, answered by `asker`: its
/// result and every question the session asked.
async fn call(
    fixture: &Fixture,
    auto: &[ShellEffect],
    asker: Asker,
    code: &str,
) -> (ToolResultMessage, Vec<ShellApprovalRequest>) {
    let names: Vec<&str> = auto.iter().map(|effect| effect.as_str()).collect();
    std::fs::write(
        fixture.dir.path().join("agent").join("settings.json"),
        json!({ "shell": { "autoEffects": names } }).to_string(),
    )
    .expect("settings");
    fixture
        .faux
        .set_responses(vec![ipython("c1", code), text("done")]);
    let questions: Arc<Mutex<Vec<ShellApprovalRequest>>> = Arc::default();
    let seen = Arc::clone(&questions);
    let sink: ShellApprovalSink = Arc::new(move |request: ShellApprovalRequest| {
        seen.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(request);
        std::future::ready(ShellAnswer::Deny).boxed()
    });
    let session = fixture
        .open_configured(move |config| {
            config.shell_approval = match asker {
                Asker::NoClient => None,
                Asker::Deny => Some(sink),
            };
        })
        .await;
    let id = submit(&session, "go").await;
    settle(&session, id).await;
    let mut all = results(&entries(&session).await);
    assert_eq!(all.len(), 1, "{all:?}");
    let questions = questions
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    (all.remove(0), questions)
}

/// Regression (audit C1): an `ipython` cell ran unasked whatever the auto
/// set. Now, with `read` only and no client, and with a client that
/// denies, the cell does not run (its marker file stays absent) and the
/// model reads why; with `exec` in the auto set it runs, unasked.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_cell_runs_only_within_the_auto_set_or_approved() {
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    let mark = fixture.dir.path().join("mark");
    let code =
        format!("import pathlib\npathlib.Path({mark:?}).write_text('ran')\nprint('cell ran')");

    let (result, asked) = call(&fixture, &[ShellEffect::Read], Asker::NoClient, &code).await;
    assert_eq!(
        (result_text(&result), result.is_error, asked),
        (UNANSWERED.to_owned(), true, vec![])
    );
    assert!(!mark.exists(), "the unanswered cell ran");

    let fixture = Fixture::new();
    let mark = fixture.dir.path().join("mark");
    let code =
        format!("import pathlib\npathlib.Path({mark:?}).write_text('ran')\nprint('cell ran')");
    let (result, asked) = call(&fixture, &[ShellEffect::Read], Asker::Deny, &code).await;
    let request_id = asked
        .first()
        .map(|request| request.request_id.clone())
        .unwrap_or_default();
    assert!(request_id.ends_with(":cell"), "{request_id}");
    assert_eq!(
        (result_text(&result), result.is_error, asked),
        (
            DENIED.to_owned(),
            true,
            vec![ShellApprovalRequest {
                request_id,
                step: 0,
                command: code.clone(),
                effects: ShellEffects::of(&[ShellEffect::Exec]),
            }]
        )
    );
    assert!(!mark.exists(), "the denied cell ran");

    let fixture = Fixture::new();
    let mark = fixture.dir.path().join("mark");
    let code =
        format!("import pathlib\npathlib.Path({mark:?}).write_text('ran')\nprint('cell ran')");
    let (result, asked) = call(
        &fixture,
        &[ShellEffect::Read, ShellEffect::Exec],
        Asker::NoClient,
        &code,
    )
    .await;
    assert_eq!(
        (result_text(&result), result.is_error, asked),
        ("cell ran\n".to_owned(), false, vec![])
    );
    assert_eq!(std::fs::read_to_string(&mark).expect("the cell ran"), "ran");
}
