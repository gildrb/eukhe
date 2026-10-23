//! The runners of code against their Bend model (`bend/runners.bend`, the
//! (G4) laws of `laws/runners.bend`). The registry bridge dumps every tool
//! a session installs (its name, caps and gate) and the gate bridge runs
//! one `ipython` call on each scenario (an auto set, an asker): both print
//! what `bridge/bridge_runners.bend` prints, byte for byte.

use std::fmt::Write as _;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_durable::harness::types::RegistryReader;
use eukhe_durable::testing::bridge::{compare, Scenario};
use eukhe_types::pi_ai::ToolResultMessage;
use eukhe_types::shell::{ShellAnswer, ShellApprovalRequest, ShellEffect, ShellEffects};
use futures::FutureExt;
use serde_json::json;

use super::{Gate, Runner};
use crate::durable::rlm::kernel_test_lock;
use crate::durable::rlm::tests::{
    entries, ipython, result_text, results, settle, submit, text, Fixture,
};
use crate::durable::{EukheSession, ShellApprovalSink};
use crate::memory::{Memory, ResponseStarted, Summarizer, SummarizerFuture};

/// What a denied cell's call says.
const DENIED: &str =
    "ipython did not run (exec): the user denied it. Do not try it again unless the user asks for it.";

/// What an unanswered cell's call says.
const UNANSWERED: &str = "ipython did not run (exec): it needs the user's approval, and no client \
answered. Ask the user to attach a client, or to allow its effect in shell.autoEffects if that is \
write, exec or net; or use read-only steps.";

/// Who answers a scenario's question (bend/runners.bend `Asker`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Asker {
    NoClient,
    Silent,
    Deny,
    Approve,
}

impl Asker {
    /// The asker's code in the events (`bridge/bridge_runners.bend` `p`).
    fn code(self) -> u8 {
        match self {
            Self::NoClient => 0,
            Self::Silent => 1,
            Self::Deny => 2,
            Self::Approve => 3,
        }
    }
}

/// The effect codes of `effects`, each after a space.
fn codes(effects: impl IntoIterator<Item = ShellEffect>) -> String {
    effects
        .into_iter()
        .fold(String::new(), |mut codes, effect| {
            write!(codes, " {}", effect.code()).expect("a String takes every write");
            codes
        })
}

/// Every tool of the session's registry, one line each:
/// `NAME caps E E ... gate none|step|call`.
fn dump(session: &EukheSession) -> String {
    session
        .registry()
        .snapshot()
        .tools()
        .iter()
        .fold(String::new(), |mut dump, installed| {
            let tool = &installed.tool;
            let (caps, gate) = match tool.extra::<Runner>() {
                Some(runner) => (
                    runner.caps,
                    match runner.gate {
                        Gate::EachStep => "step",
                        Gate::EachCall => "call",
                    },
                ),
                None => (ShellEffects::NONE, "none"),
            };
            writeln!(dump, "{} caps{} gate {gate}", tool.name, codes(caps.iter()))
                .expect("a String takes every write");
            dump
        })
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

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_registry_is_its_model() {
    let fixture = Fixture::new();
    let classic = fixture.open_configured(|_| {}).await;
    let classic = dump(&classic);
    let fixture = Fixture::new();
    let memory = Memory::open(fixture.dir.path().join("chat"), Arc::new(NoModel))
        .await
        .expect("chat memory");
    let chat = fixture
        .open_configured(move |config| config.memory = Some(memory))
        .await;
    compare(
        "bridge/bridge_runners.bend",
        [
            Scenario {
                name: "registry".to_owned(),
                events: "r 0\n".to_owned(),
                transcript: classic,
            },
            Scenario {
                name: "chat registry".to_owned(),
                events: "r 1\n".to_owned(),
                transcript: dump(&chat),
            },
        ],
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
        std::future::ready(match asker {
            Asker::NoClient | Asker::Silent => ShellAnswer::Unanswered,
            Asker::Deny => ShellAnswer::Deny,
            Asker::Approve => ShellAnswer::Approve,
        })
        .boxed()
    });
    let session = fixture
        .open_configured(move |config| {
            config.shell_approval = match asker {
                Asker::NoClient => None,
                Asker::Silent | Asker::Deny | Asker::Approve => Some(sink),
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

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_ipython_gate_runs_as_its_model() {
    let _kernel = kernel_test_lock().await;
    let read = [ShellEffect::Read];
    let granted = [ShellEffect::Read, ShellEffect::Write, ShellEffect::Net];
    let exec = [ShellEffect::Read, ShellEffect::Exec];
    let plan: [(&[ShellEffect], Asker); 12] = [
        (&[], Asker::NoClient),
        (&[], Asker::Deny),
        (&read, Asker::NoClient),
        (&read, Asker::Silent),
        (&read, Asker::Deny),
        (&read, Asker::Approve),
        (&granted, Asker::NoClient),
        (&granted, Asker::Silent),
        (&granted, Asker::Deny),
        (&granted, Asker::Approve),
        (&exec, Asker::NoClient),
        (&exec, Asker::Deny),
    ];
    let mut scenarios = Vec::new();
    for (at, (auto, asker)) in plan.into_iter().enumerate() {
        let fixture = Fixture::new();
        let (result, asked) = call(&fixture, auto, asker, "print('cell ran')").await;
        let text = result_text(&result);
        let end = match text.as_str() {
            DENIED => "denied",
            UNANSWERED => "unanswered",
            "cell ran\n" => "ran",
            other => panic!("an unexpected result: {other:?}"),
        };
        let codes = codes(auto.iter().copied());
        scenarios.push(Scenario {
            name: format!("gate {at}"),
            events: format!("a{codes}\np {}\ng\n", asker.code()),
            transcript: format!("asked {}\nend {end}\n", asked.len()),
        });
    }
    compare("bridge/bridge_runners.bend", scenarios);
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
