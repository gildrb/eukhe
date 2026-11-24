//! The computer tools in a session on a fake desktop: offered only while
//! `computer.enabled` is on; a window outside `computer.apps`, an
//! unallowed consequential step and the desktop's own typed refusals send
//! nothing; and a replay never sends input again: an act a crash
//! interrupted is reported, and a `codemode` script that resumes gets its
//! finished act from the journal.

use std::sync::Arc;
use std::time::Duration;

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_tool_call, FauxAssistantMessageOptions, FauxResponseStep,
};
use eukhe_desktop::{
    Error, Focus, GlobalRect, Refusal as DesktopRefusal, Window, WindowError, WindowId,
};
use eukhe_durable::types::SubmissionStatus;
use eukhe_types::pi_ai::{JsonObject, StopReason};
use serde_json::{json, Value};

use super::fake::{FakeDesktop, Hold, TREE};
use super::policy::Refusal;
use super::DesktopPort;
use crate::durable::rlm::tests::{
    cx, entries, result_text, results, settle, submit, text, wait_for, Fixture, WAIT_MS,
};
use crate::durable::EukheSession;
use crate::settings::types::Consequence;

/// A model step that calls `tool` with `arguments`.
fn call(tool: &str, call_id: &str, arguments: Value) -> FauxResponseStep {
    let Value::Object(arguments) = arguments else {
        unreachable!("an object literal");
    };
    faux_assistant_message(
        vec![faux_tool_call(
            tool,
            arguments.into_iter().collect::<JsonObject>(),
            Some(call_id.to_owned()),
        )],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

fn window(id: &str, app: &str) -> Window {
    Window {
        id: WindowId::new(id),
        title: "Notes".to_owned(),
        app: app.to_owned(),
        pid: None,
        bounds: GlobalRect {
            x: 0,
            y: 0,
            width: 800,
            height: 600,
        },
        focus: Focus::Unfocused,
    }
}

/// A fixture whose global settings set `computer` to `computer`.
fn fixture(computer: &Value) -> Fixture {
    let fixture = Fixture::new();
    std::fs::write(
        fixture.dir.path().join("agent").join("settings.json"),
        json!({ "computer": computer }).to_string(),
    )
    .expect("settings");
    fixture
}

async fn open(fixture: &Fixture, fake: &Arc<FakeDesktop>) -> EukheSession {
    let port = DesktopPort::Fake(Arc::clone(fake));
    fixture
        .open_configured(move |config| config.desktop = port)
        .await
}

/// Run the faux turns queued on `fixture` and return each tool result's
/// text and error flag.
async fn run(session: &EukheSession) -> Vec<(String, bool)> {
    let id = submit(session, "go").await;
    assert_eq!(settle(session, id).await, SubmissionStatus::Done);
    results(&entries(session).await)
        .iter()
        .map(|result| (result_text(result), result.is_error))
        .collect()
}

const ACT_E1: &str = r#"{ "window": { "id": "w1" }, "steps": [{ "type": "press", "target": "e1" }], "observe_after": false }"#;

fn act_e1() -> Value {
    serde_json::from_str(ACT_E1).expect("an act")
}

/// Off by default: a session offers no computer tool, and a call to one
/// reaches no desktop.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_tools_are_offered_only_while_computer_use_is_on() {
    let fake = Arc::new(FakeDesktop::new(
        vec![window("w1", "TextEdit")],
        Hold::Nothing,
    ));
    let fixture = Fixture::new();
    fixture.faux.set_responses(vec![
        call("computer_windows", "c1", json!({})),
        text("done"),
    ]);
    let session = open(&fixture, &fake).await;
    let answered = run(&session).await;
    assert_eq!(answered.len(), 1, "{answered:?}");
    assert!(answered[0].1, "{answered:?}");
    session.close(cx()).await.expect("close");

    let fixture = self::fixture(&json!({ "enabled": true, "apps": ["textedit"] }));
    fixture.faux.set_responses(vec![
        call("computer_windows", "c1", json!({})),
        text("done"),
    ]);
    let session = open(&fixture, &fake).await;
    assert_eq!(
        run(&session).await,
        [(
            "- id=w1 app=\"TextEdit\" title=\"Notes\" at 0,0 800x600\n".to_owned(),
            false
        )]
    );
    session.close(cx()).await.expect("close");
}

/// A window of an app the user did not allow, a consequential step the
/// user did not allow, and a window the desktop cannot find are each
/// refused with nothing sent, and say why; an allowed step runs once.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn refusals_send_nothing_and_say_why() {
    let fake = Arc::new(FakeDesktop::new(
        vec![window("w1", "TextEdit"), window("w2", "Mail")],
        Hold::Nothing,
    ));
    let fixture = fixture(&json!({ "enabled": true, "apps": ["TextEdit"] }));
    fixture.faux.set_responses(vec![
        call(
            "computer_observe",
            "c1",
            json!({ "window": { "app": "mail" } }),
        ),
        call(
            "computer_act",
            "c2",
            json!({
                "window": { "id": "w1" },
                "steps": [{ "type": "press", "target": "e1", "consequence": "send" }]
            }),
        ),
        call(
            "computer_observe",
            "c3",
            json!({ "window": { "id": "gone" }, "screenshot": false }),
        ),
        call("computer_act", "c4", act_e1()),
        text("done"),
    ]);
    let session = open(&fixture, &fake).await;
    assert_eq!(
        run(&session).await,
        [
            (
                Refusal::App {
                    app: "Mail".to_owned()
                }
                .to_string(),
                true
            ),
            (
                Refusal::Consequential {
                    step: 1,
                    consequence: Consequence::Send
                }
                .to_string(),
                true
            ),
            (
                Error::Refused(DesktopRefusal::Window(WindowError::NotFound(
                    WindowId::new("gone")
                )))
                .to_string(),
                true
            ),
            ("1. press: confirmed\n".to_owned(), false),
        ]
    );
    assert_eq!((fake.observes(), fake.acts()), (0, 1));
    session.close(cx()).await.expect("close");
}

/// Speculation, then effect (`effect_once` in `laws/tool_call.bend`): a
/// crash while an act runs settles it `interrupted` after the reopen, and
/// the act is never sent again.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_resume_never_resends_an_act_a_crash_interrupted() {
    let fake = Arc::new(FakeDesktop::new(
        vec![window("w1", "TextEdit")],
        Hold::FirstAct,
    ));
    let fixture = fixture(&json!({ "enabled": true, "apps": ["TextEdit"] }));
    fixture
        .faux
        .set_responses(vec![call("computer_act", "a1", act_e1()), text("done")]);
    let session = open(&fixture, &fake).await;
    let id = submit(&session, "go").await;
    let started = Arc::clone(&fake);
    wait_for("the act reaches the desktop", move || {
        let acted = started.acts() == 1;
        async move { acted }
    })
    .await;
    // The worker dies mid-act: nothing more commits.
    session.harness().close(cx()).await.expect("harness close");
    drop(session);

    let session = open(&fixture, &fake).await;
    assert_eq!(settle(&session, id).await, SubmissionStatus::Done);
    let all = results(&entries(&session).await);
    assert_eq!(
        (all.len(), result_text(&all[0]), fake.acts()),
        (
            1,
            "<harness>\n[error] Tool computer_act was interrupted and may have partially run. Check the state it changes (files, processes, jobs) before you run it again.\n</harness>".to_owned(),
            1
        )
    );
    fake.release();
    session.close(cx()).await.expect("close");
}

/// A `codemode` script that acts, then observes, is cut off by a crash
/// during the observation; the resumed script replays from its journal:
/// the observation (replay-safe) runs again, the finished act is answered
/// from the journal and never sent again, and the script ends as it would
/// have.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_codemode_replay_answers_a_finished_act_from_the_journal() {
    let fake = Arc::new(FakeDesktop::new(
        vec![window("w1", "TextEdit")],
        Hold::FirstObserve,
    ));
    let fixture = fixture(&json!({ "enabled": true, "apps": ["TextEdit"] }));
    let script = format!(
        "const acted = await tools.computer_act({ACT_E1});\n\
         const seen = await tools.computer_observe({{ window: {{ id: \"w1\" }}, screenshot: false }});\n\
         return [acted, seen];"
    );
    fixture.faux.set_responses(vec![
        call("codemode", "s1", json!({ "code": script })),
        text("done"),
    ]);
    let session = open(&fixture, &fake).await;
    let id = submit(&session, "go").await;
    let started = Arc::clone(&fake);
    wait_for("the observation reaches the desktop", move || {
        let observed = started.observes() == 1;
        async move { observed }
    })
    .await;
    session.harness().close(cx()).await.expect("harness close");
    drop(session);
    fake.release();

    let session = open(&fixture, &fake).await;
    tokio::time::timeout(Duration::from_millis(WAIT_MS), settle(&session, id))
        .await
        .expect("the resumed script settles");
    let all = results(&entries(&session).await);
    assert_eq!(all.len(), 1, "{all:?}");
    assert!(!all[0].is_error, "{}", result_text(&all[0]));
    // A codemode result reports the script: completed, and its return is
    // the journaled act's report, then the replayed observation,
    // JSON-encoded.
    let acted = "1. press: confirmed\n";
    let seen = format!("- id=w1 app=\"TextEdit\" title=\"Notes\" at 0,0 800x600\n{TREE}\n");
    let returned =
        serde_json::to_string(&[acted, seen.as_str()]).unwrap_or_else(|error| panic!("{error}"));
    let answer = result_text(&all[0]);
    assert!(answer.starts_with("Script completed\n"), "{answer}");
    assert!(answer.contains(&returned), "{answer}");
    assert_eq!((fake.acts(), fake.observes()), (1, 2));
    session.close(cx()).await.expect("close");
}
