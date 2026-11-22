//! Session commands on an open eukhe session with faux script models.

use std::sync::Arc;

use eukhe_ai::providers::faux::{
    faux_assistant_message, FauxAssistantMessageOptions, FauxResponseStep,
};
use eukhe_ai::providers::faux_script::{
    create_faux_script_models, parse_faux_script, FauxScriptProvider,
};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::entries::{COMPACTION_ENTRY, USER_ENTRY};
use eukhe_durable::harness::types::InputSubmissionDraft;
use eukhe_durable::harness::ConversationEntryQuery;
use eukhe_durable::types::{EntryRecord, TaskOutcome};
use eukhe_types::acceptance::{AcceptanceLabel, AcceptanceState, CheckSpec};
use eukhe_types::pi_ai::{Message, UserContent};
use serde_json::{json, Value};

use super::*;
use crate::autonomous::AgentAutonomousConfig;
use crate::durable::directors::{director_state, DirectorState, DIRECTOR_NOTICE_CUSTOM_TYPE};
use crate::durable::entries::{CustomEntryData, CustomStateData, CUSTOM_ENTRY, CUSTOM_STATE_ENTRY};
use crate::durable::messages::REFINEMENT_AUDIT_CUSTOM_TYPE;
use crate::durable::{open_session, ModelRequest, SessionConfig, SessionStorage};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// The failure text of `outcome`.
fn failed(outcome: &SessionCommandOutcome) -> Option<String> {
    outcome.error.as_ref().map(ToString::to_string)
}

struct Fixture {
    _dir: tempfile::TempDir,
    session: EukheSession,
    provider: FauxScriptProvider,
}

/// An in-memory session on a faux script answering `responses` in order.
async fn open(responses: &[Value]) -> Fixture {
    open_with_settings(responses, &json!({})).await
}

/// [`open`] with the agent's `settings.json`.
async fn open_with_settings(responses: &[Value], settings: &Value) -> Fixture {
    let dir = tempfile::tempdir().expect("tempdir");
    let agent_dir = dir.path().join("agent");
    let cwd = dir.path().join("project");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    std::fs::create_dir_all(&cwd).expect("cwd");
    std::fs::write(agent_dir.join("settings.json"), settings.to_string()).expect("settings");
    let script = parse_faux_script(&json!({ "responses": responses }).to_string())
        .expect("the faux script parses");
    let (models, provider) = create_faux_script_models(script);
    let mut config = SessionConfig::new(
        &agent_dir,
        &cwd,
        "0192a000-0000-7000-8000-0000000000c1",
        SessionStorage::Memory,
    );
    config.models = Some(models);
    config.model = Some(ModelRequest {
        provider: Some("faux".to_owned()),
        pattern: "faux-1".to_owned(),
    });
    let session = open_session(config, cx()).await.expect("the session opens");
    Fixture {
        _dir: dir,
        session,
        provider,
    }
}

impl Fixture {
    async fn run(&self, text: &str) -> SessionCommandOutcome {
        let command = classify_session_command(text).expect("a session command");
        let conversation = self.session.main();
        execute_session_command(&self.session, &conversation, &command, cx()).await
    }

    /// Submit `text` to the main conversation and wait for its run.
    async fn ask(&self, text: &str) {
        self.session
            .main()
            .submit(InputSubmissionDraft::new(text), cx())
            .await
            .expect("submit")
            .wait(cx())
            .await
            .expect("wait");
    }

    async fn idle(&self) {
        self.session
            .harness()
            .wait_for_idle(cx())
            .await
            .expect("idle");
    }

    async fn entries(&self) -> Vec<EntryRecord> {
        let page = self
            .session
            .main()
            .entries(ConversationEntryQuery::default(), 1000, None, cx())
            .await
            .expect("entries");
        page.items.into_iter().rev().collect()
    }

    /// The custom rows of `types`, oldest first.
    async fn rows(&self, types: &[&str]) -> Vec<CustomEntryData> {
        self.entries()
            .await
            .into_iter()
            .filter_map(|entry| CUSTOM_ENTRY.narrow(entry).expect("narrow"))
            .map(|entry| entry.data().clone())
            .filter(|data| types.contains(&data.custom_type.as_str()))
            .collect()
    }

    /// The echo and result rows, oldest first.
    async fn command_rows(&self) -> Vec<CustomEntryData> {
        self.rows(&[
            SESSION_SLASH_COMMAND_CUSTOM_TYPE,
            SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE,
        ])
        .await
    }

    async fn user_texts(&self) -> Vec<String> {
        self.entries()
            .await
            .into_iter()
            .filter(|entry| entry.kind == USER_ENTRY.kind())
            .filter_map(|entry| match entry.model.as_ref()?.first()? {
                Message::User(message) => match &message.content {
                    UserContent::Text(text) => Some(text.clone()),
                    UserContent::Blocks(_) => None,
                },
                _ => None,
            })
            .collect()
    }

    async fn close(self) {
        self.session.close(cx()).await.expect("close");
    }
}

fn command(text: &str) -> SessionCommand {
    classify_session_command(text).expect("a session command")
}

fn echo(text: &str) -> CustomEntryData {
    let command = command(text);
    CustomEntryData {
        custom_type: SESSION_SLASH_COMMAND_CUSTOM_TYPE.to_owned(),
        content: Some(UserContent::Text(text.to_owned())),
        display: true,
        details: Some(command_details(&command)),
        input: false,
        origin: None,
    }
}

fn result(text: &str, content: &str, display: bool) -> CustomEntryData {
    let command = command(text);
    let mut details = command_details(&command);
    details["success"] = json!(true);
    details["severity"] = json!("info");
    CustomEntryData {
        custom_type: SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE.to_owned(),
        content: Some(UserContent::Text(content.to_owned())),
        display,
        details: Some(details),
        input: false,
        origin: None,
    }
}

fn failure(text: &str, error: &str) -> CustomEntryData {
    let command = command(text);
    let mut details = command_details(&command);
    details["success"] = json!(false);
    details["severity"] = json!("error");
    details["error"] = json!(error);
    CustomEntryData {
        custom_type: SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE.to_owned(),
        content: Some(UserContent::Text(format!("Command failed: {error}"))),
        display: true,
        details: Some(details),
        input: false,
        origin: None,
    }
}

fn error_response(message: &str) -> Value {
    json!({ "content": [], "stopReason": "error", "errorMessage": message })
}

#[test]
fn classify_recognizes_only_session_commands() {
    assert_eq!(
        classify_session_command("/compact focus on tests"),
        Some(SessionCommand {
            name: SessionCommandName::Compact,
            args: "focus on tests".to_owned(),
            text: "/compact focus on tests".to_owned(),
        })
    );
    assert_eq!(
        classify_session_command("/goal"),
        Some(SessionCommand {
            name: SessionCommandName::Goal,
            args: String::new(),
            text: "/goal".to_owned(),
        })
    );
    assert_eq!(
        classify_session_command("/refine --global tweak").map(|command| command.name),
        Some(SessionCommandName::Refine)
    );
    assert_eq!(
        ["/auto ship it", "/autonomous on"]
            .map(|text| classify_session_command(text).map(|command| command.name)),
        [
            Some(SessionCommandName::Auto(AutoName::Auto)),
            Some(SessionCommandName::Auto(AutoName::Autonomous)),
        ]
    );
    assert_eq!(classify_session_command("/model"), None);
    assert_eq!(classify_session_command("/unknown x"), None);
    assert_eq!(classify_session_command("compact"), None);
    for name in [
        SessionCommandName::Compact,
        SessionCommandName::Refine,
        SessionCommandName::Auto(AutoName::Auto),
        SessionCommandName::Goal,
        SessionCommandName::Accept,
        SessionCommandName::Remind,
        SessionCommandName::Force,
        SessionCommandName::Loop,
    ] {
        assert_eq!(SessionCommandName::from_name(name.as_str()), Some(name));
    }
}

/// The removed `/goal`'s one answer.
const GOAL_POINTER: &str = "/goal is removed: use /auto";

/// `/goal`, whatever it is given (alone, a task, a budget, its old
/// `pause`/`resume`, a malformed budget), answers only its pointer to
/// `/auto`: no run starts, no message is sent, nothing fails.
#[tokio::test]
async fn goal_answers_only_its_pointer() {
    let fixture = open(&[]).await;
    let texts = [
        "/goal",
        "/goal ship it",
        "/goal --budget 5000 ship it",
        "/goal resume",
        "/goal pause",
        "/goal --budget nope ship it",
    ];
    for text in texts {
        let outcome = fixture.run(text).await;
        assert_eq!(
            (failed(&outcome), outcome.autonomous),
            (None, None),
            "{text}"
        );
    }
    fixture.idle().await;
    let expected: Vec<CustomEntryData> = texts
        .into_iter()
        .flat_map(|text| [echo(text), result(text, GOAL_POINTER, true)])
        .collect();
    assert_eq!(
        (
            fixture
                .rows(&[
                    SESSION_SLASH_COMMAND_CUSTOM_TYPE,
                    SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE,
                    AUTONOMOUS_STATUS_CUSTOM_TYPE,
                ])
                .await,
            fixture.user_texts().await,
        ),
        (expected, Vec::<String>::new())
    );
    fixture.close().await;
}

/// `/auto <task>` turns autonomous mode on, then sends the task as the
/// user's message.
#[tokio::test]
async fn auto_task_turns_autonomous_on_and_sends_the_task() {
    // The run fails at the provider: no continuation follows it.
    let fixture = open(&[error_response("provider exploded")]).await;
    let outcome = fixture.run("/auto ship it").await;
    assert_eq!(failed(&outcome), None);
    assert!(outcome.autonomous.expect("the status").enabled);
    fixture.idle().await;
    assert_eq!(
        (fixture.command_rows().await, fixture.user_texts().await),
        (vec![echo("/auto ship it")], vec!["ship it".to_owned()])
    );
    fixture.close().await;
}

/// On main (`main-worker`) `/auto` (as typed in any of its names) is the
/// worker's: main starts no run of its own; with no worker yet the command
/// says so.
#[tokio::test]
async fn main_directors_go_to_the_worker_and_without_one_are_refused() {
    let fixture = open_with_settings(&[], &json!({ "sessionShape": "main-worker" })).await;
    let error = "No worker yet: /auto applies to the worker, which main creates with the first work you give it";
    for text in ["/auto ship it", "/autonomous on"] {
        let outcome = fixture.run(text).await;
        assert_eq!(
            (
                outcome.error.as_ref().map(ToString::to_string),
                outcome.autonomous.is_none()
            ),
            (Some(error.to_owned()), true),
        );
    }
    fixture.idle().await;
    assert_eq!(
        (fixture.command_rows().await, fixture.user_texts().await),
        (
            vec![
                echo("/auto ship it"),
                failure("/auto ship it", error),
                echo("/autonomous on"),
                failure("/autonomous on", error),
            ],
            Vec::<String>::new(),
        )
    );
    fixture.close().await;
}

#[tokio::test]
async fn autonomous_status_on_and_off_append_status_rows() {
    let fixture = open(&[]).await;
    let status = fixture.run("/autonomous").await;
    assert_eq!(failed(&status), None);
    let off = status.autonomous.expect("the status");
    assert!(!off.enabled);

    let on = fixture.run("/autonomous on --max-turns 5").await;
    assert_eq!(failed(&on), None);
    let enabled = on.autonomous.expect("the status");
    assert!(enabled.enabled);
    let AutonomousCommand::On { config } =
        parse_auto_command(AutoName::Autonomous, "on --max-turns 5").expect("parses")
    else {
        panic!("expected on");
    };
    assert_ne!(config, AgentAutonomousConfig::default());

    let disabled = fixture.run("/autonomous off").await;
    assert_eq!(failed(&disabled), None);
    let disabled = disabled.autonomous.expect("the status");
    assert!(!disabled.enabled);

    let rows = fixture
        .rows(&[
            SESSION_SLASH_COMMAND_CUSTOM_TYPE,
            AUTONOMOUS_STATUS_CUSTOM_TYPE,
        ])
        .await;
    let status_row = |status: &AgentAutonomousStatus| CustomEntryData {
        custom_type: AUTONOMOUS_STATUS_CUSTOM_TYPE.to_owned(),
        content: None,
        display: true,
        details: Some(serde_json::to_value(status).expect("status json")),
        input: false,
        origin: None,
    };
    // Status rows reach the model: their text rides in `model`.
    assert_eq!(
        rows,
        vec![
            echo("/autonomous"),
            status_row(&off),
            echo("/autonomous on --max-turns 5"),
            status_row(&enabled),
            echo("/autonomous off"),
            status_row(&disabled),
        ]
    );
    let texts: Vec<String> = fixture
        .entries()
        .await
        .into_iter()
        .filter_map(|entry| {
            let data = CUSTOM_ENTRY.narrow(entry.clone()).expect("narrow")?;
            (data.data().custom_type == AUTONOMOUS_STATUS_CUSTOM_TYPE).then_some(entry)
        })
        .filter_map(|entry| match entry.model.as_ref()?.first()? {
            Message::User(message) => match &message.content {
                UserContent::Text(text) => Some(text.clone()),
                UserContent::Blocks(blocks) => blocks.iter().find_map(|block| match block {
                    eukhe_types::pi_ai::UserContentBlock::Text(text) => Some(text.text.clone()),
                    eukhe_types::pi_ai::UserContentBlock::Image(_) => None,
                }),
            },
            _ => None,
        })
        .collect();
    assert_eq!(texts[0], format_autonomous_status(&off));
    assert_eq!(texts.len(), 3);
    fixture.close().await;
}

#[tokio::test]
async fn an_invalid_autonomous_command_appends_the_failure_row() {
    let fixture = open(&[]).await;
    let text = "/autonomous status now";
    let expected =
        parse_auto_command(AutoName::Autonomous, &command(text).args).expect_err("extra arguments");
    let outcome = fixture.run(text).await;
    assert_eq!(failed(&outcome), Some(expected.to_string()));
    assert_eq!(outcome.autonomous, None);
    assert_eq!(
        fixture.command_rows().await,
        vec![echo(text), failure(text, &expected.text)]
    );
    fixture.close().await;
}

#[tokio::test]
async fn compact_admits_a_compaction_task() {
    let fixture = open_with_settings(
        &[json!("hi there"), json!("sure"), json!("the summary")],
        &json!({ "compaction": { "keepRecentTokens": 1 } }),
    )
    .await;
    fixture.ask("hello").await;
    fixture.ask("again").await;
    let outcome = fixture.run("/compact keep the greeting").await;
    assert_eq!(failed(&outcome), None);
    let task = outcome.compaction.expect("the compaction task");
    let settled = fixture
        .session
        .harness()
        .wait_for_task(task, cx())
        .await
        .expect("the compaction settles")
        .decode::<CompactionResult>()
        .expect("the compaction result");
    assert!(
        matches!(settled.outcome, TaskOutcome::Completed { .. }),
        "{:?}",
        settled.outcome
    );
    fixture.idle().await;
    assert_eq!(
        fixture.command_rows().await,
        vec![echo("/compact keep the greeting")]
    );
    let kinds: Vec<String> = fixture
        .entries()
        .await
        .into_iter()
        .map(|entry| entry.kind)
        .filter(|kind| kind != "pi.system")
        .collect();
    assert_eq!(
        kinds,
        [
            "pi.user",
            "pi.assistant",
            "pi.user",
            "pi.assistant",
            CUSTOM_ENTRY.kind(),
            COMPACTION_ENTRY.kind(),
        ]
    );
    fixture.close().await;
}

#[tokio::test]
async fn local_refine_without_a_session_directory_fails() {
    let fixture = open(&[]).await;
    let outcome = fixture.run("/refine").await;
    let error =
        "Local harness refinement requires a session directory; use global refinement instead.";
    assert_eq!(failed(&outcome).as_deref(), Some(error));
    assert_eq!(
        outcome
            .refinement_failed()
            .map(ToString::to_string)
            .as_deref(),
        Some(error)
    );
    assert_eq!(
        fixture.command_rows().await,
        vec![echo("/refine"), failure("/refine", error)]
    );
    fixture.close().await;
}

#[tokio::test]
async fn refine_rollback_without_an_id_fails_with_the_usage() {
    let fixture = open(&[]).await;
    let outcome = fixture.run("/refine rollback").await;
    let error = "Usage: /refine rollback <refinement-id>";
    assert_eq!(failed(&outcome).as_deref(), Some(error));
    // A usage error never ran a refinement.
    assert!(outcome.refinement_failed().is_none());
    assert_eq!(
        fixture.command_rows().await,
        vec![echo("/refine rollback"), failure("/refine rollback", error)]
    );
    fixture.close().await;
}

#[tokio::test]
async fn global_refine_records_its_rows_and_the_applied_count() {
    let plan = r#"{"summary":"global lesson","edits":[{"action":"create","kind":"memory","id":"g1","title":"Lesson","content":"durable"}]}"#;
    let fixture = open(&[json!(plan)]).await;
    let outcome = fixture.run("/refine --global").await;
    assert_eq!(failed(&outcome), None);
    assert!(outcome.refinement_failed().is_none());
    let rows = fixture
        .rows(&[
            SESSION_SLASH_COMMAND_CUSTOM_TYPE,
            SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE,
            "refinement_outcome",
            "refinement_notice",
        ])
        .await;
    let types: Vec<&str> = rows.iter().map(|row| row.custom_type.as_str()).collect();
    assert_eq!(
        types,
        [
            SESSION_SLASH_COMMAND_CUSTOM_TYPE,
            "refinement_outcome",
            "refinement_notice",
            SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE,
        ]
    );
    assert_eq!(
        rows[3],
        result(
            "/refine --global",
            "Refined continual harness state: 1 edit applied.",
            false
        )
    );
    let audits: Vec<CustomStateData> = fixture
        .entries()
        .await
        .into_iter()
        .filter_map(|entry| CUSTOM_STATE_ENTRY.narrow(entry).expect("narrow"))
        .map(|entry| entry.data().clone())
        .filter(|data| data.custom_type == REFINEMENT_AUDIT_CUSTOM_TYPE)
        .collect();
    assert_eq!(audits.len(), 1);
    fixture.close().await;
}

#[test]
fn refine_options_parsing() {
    assert_eq!(
        parse_refine_command_options("do the thing").unwrap(),
        RefineCommandOptions {
            instructions: Some("do the thing".to_string()),
            rollback_id: None,
            global: false,
        }
    );
    assert_eq!(
        parse_refine_command_options("").unwrap(),
        RefineCommandOptions::default()
    );
    assert_eq!(
        parse_refine_command_options("--global tweak").unwrap(),
        RefineCommandOptions {
            instructions: Some("tweak".to_string()),
            rollback_id: None,
            global: true,
        }
    );
    assert_eq!(
        parse_refine_command_options("rollback ref_123").unwrap(),
        RefineCommandOptions {
            instructions: None,
            rollback_id: Some("ref_123".to_string()),
            global: false,
        }
    );
    assert!(
        parse_refine_command_options("--global rollback ref_123")
            .unwrap()
            .global
    );
    assert_eq!(
        parse_refine_command_options("rollback")
            .unwrap_err()
            .to_string(),
        "Usage: /refine rollback <refinement-id>"
    );
    assert_eq!(
        parse_refine_command_options("rollback ")
            .unwrap_err()
            .to_string(),
        "Usage: /refine rollback <refinement-id>"
    );
}

#[test]
fn force_options_parsing() {
    let text = |args| parse_force_command(args).map_err(|error| error.to_string());
    assert_eq!(text("lookup"), Ok(("lookup".to_owned(), 1)));
    assert_eq!(text(" lookup --tries 3 "), Ok(("lookup".to_owned(), 3)));
    let usage = Err("Usage: /force <tool> [--tries <n>]".to_owned());
    for args in [
        "",
        "--tries 2",
        "lookup --tries",
        "lookup --tries -1",
        "lookup extra",
    ] {
        assert_eq!(text(args), usage, "{args:?}");
    }
}

#[tokio::test]
async fn remind_and_force_put_their_layers_on_the_director_stack() {
    let fixture = open(&[]).await;
    for text in ["/remind Run the tests first.", "/force lookup --tries 2"] {
        assert_eq!(failed(&fixture.run(text).await), None, "{text}");
    }
    let usage = "Usage: /remind <text>";
    assert_eq!(
        failed(&fixture.run("/remind").await).as_deref(),
        Some(usage)
    );
    assert_eq!(
        fixture.command_rows().await,
        vec![
            echo("/remind Run the tests first."),
            result(
                "/remind Run the tests first.",
                "Reminder added: it leads the next continuation.",
                true
            ),
            echo("/force lookup --tries 2"),
            result(
                "/force lookup --tries 2",
                "The next requests force a call to `lookup`.",
                true
            ),
            echo("/remind"),
            failure("/remind", usage),
        ]
    );
    let main = fixture.session.main();
    assert_eq!(
        director_state(fixture.session.harness(), main.id(), cx())
            .await
            .expect("read"),
        DirectorState {
            stack: vec![
                Layer::reminder("Run the tests first.".to_owned()),
                Layer::force_tool("lookup".to_owned(), 2),
            ],
            run: None,
            work_left: None,
            found_left: None,
        }
    );
    fixture.close().await;
}

/// Answer `message`, recording the last user text of each request.
fn recorded(seen: &Arc<std::sync::Mutex<Vec<String>>>, text: &str) -> FauxResponseStep {
    let seen = Arc::clone(seen);
    let message = faux_assistant_message(text, FauxAssistantMessageOptions::default());
    FauxResponseStep::factory(move |request, _, _, _| {
        let last = match request.messages().last() {
            Some(Message::User(message)) => match &message.content {
                UserContent::Text(text) => text.clone(),
                UserContent::Blocks(_) => String::new(),
            },
            _ => String::new(),
        };
        seen.lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push(last);
        Ok(message.clone())
    })
}

#[tokio::test]
async fn a_forced_call_never_made_fails_once_and_the_next_ask_is_not_forced() {
    let fixture = open(&[]).await;
    let seen = Arc::default();
    fixture.provider.set_responses(vec![
        recorded(&seen, "no call"),
        recorded(&seen, "plain"),
        // Taken only by a forced second ask.
        recorded(&seen, "unused"),
    ]);
    assert_eq!(failed(&fixture.run("/force lookup --tries 0").await), None);

    fixture.ask("go").await;
    fixture.ask("again").await;
    fixture.idle().await;

    let soft = "Call the `lookup` tool now: your reply must include a call to `lookup`.";
    assert_eq!(
        *seen
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner),
        vec![soft.to_owned(), "again".to_owned()]
    );
    assert_eq!(fixture.provider.get_pending_response_count(), 1);
    assert_eq!(
        fixture.rows(&[DIRECTOR_NOTICE_CUSTOM_TYPE]).await,
        vec![CustomEntryData {
            custom_type: DIRECTOR_NOTICE_CUSTOM_TYPE.to_owned(),
            content: Some(UserContent::Text(
                "The model did not call the forced tool lookup in 1 requests. The forced call left the Director stack."
                    .to_owned()
            )),
            display: true,
            details: Some(json!({ "kind": "notCalled", "tool": "lookup", "attempts": 1 })),
            input: false,
            origin: None,
        }]
    );
    let main = fixture.session.main();
    // The forced call left the stack and the loop; the work-left
    // Director's record of the final answer stays beside them.
    let state = director_state(fixture.session.harness(), main.id(), cx())
        .await
        .expect("read");
    assert_eq!((state.stack, state.run), (Vec::new(), None));
    fixture.close().await;
}

/// `/accept`: the owner sets, shows and clears the conversation's
/// acceptance checks; each change is a new revision, and arguments that
/// name no check answer the usage and change nothing.
#[tokio::test]
async fn accept_sets_shows_and_clears_the_checks() {
    let fixture = open(&[]).await;
    let command_check = CheckSpec::Command {
        command: "cargo test".to_owned(),
        expect: 0,
        timeout_ms: None,
        protect: Vec::new(),
        strength: None,
    };
    let judge_check = CheckSpec::Judge {
        condition: "the README names the flag".to_owned(),
        evidence: Vec::new(),
        model: None,
    };

    let empty = fixture.run("/accept").await;
    fixture.run("/accept cmd cargo test").await;
    fixture.run("/accept judge the README names the flag").await;
    let capped = fixture.run("/accept returns 1").await;
    let usage = fixture.run("/accept cmd").await;
    let shown = fixture.run("/accept status").await;
    let cleared = fixture.run("/accept clear").await;

    assert_eq!(
        empty.acceptance.map(|state| (state.label, state.checks)),
        Some((AcceptanceLabel::Unverified, Vec::new()))
    );
    let specs = |state: &AcceptanceState| -> Vec<CheckSpec> {
        state
            .checks
            .iter()
            .map(|check| check.spec.clone())
            .collect()
    };
    let capped = capped.acceptance.expect("the acceptance");
    assert_eq!(
        (capped.revision, capped.max_returns, specs(&capped)),
        (3, 1, vec![command_check, judge_check, CheckSpec::intent()])
    );
    assert_eq!(failed(&usage).as_deref(), Some(ACCEPT_USAGE));
    assert_eq!(shown.acceptance, Some(capped));
    assert_eq!(
        cleared
            .acceptance
            .map(|state| (state.revision, state.label, state.checks)),
        Some((4, AcceptanceLabel::Unverified, Vec::new()))
    );
    // A command check shows its strength; the judges have none.
    let unmeasured = "; strength: not measured on this state (needs 80 % of the breaks caught)";
    let judged = format!("Acceptance: unverified (revision 3, returns 0 of 1).\n1. command `cargo test` (expect exit 0): not judged{unmeasured}\n2. judge: the README names the flag: not judged\n3. intent: what the user's messages ask for now holds on the final state: not judged");
    assert_eq!(
        fixture.command_rows().await,
        vec![
            echo("/accept"),
            result(
                "/accept",
                "Acceptance: unverified (no acceptance checks).",
                true
            ),
            echo("/accept cmd cargo test"),
            result(
                "/accept cmd cargo test",
                &format!("Acceptance: unverified (revision 1, returns 0 of 3).\n1. command `cargo test` (expect exit 0): not judged{unmeasured}\n2. intent: what the user's messages ask for now holds on the final state: not judged"),
                true
            ),
            echo("/accept judge the README names the flag"),
            result(
                "/accept judge the README names the flag",
                &format!("Acceptance: unverified (revision 2, returns 0 of 3).\n1. command `cargo test` (expect exit 0): not judged{unmeasured}\n2. judge: the README names the flag: not judged\n3. intent: what the user's messages ask for now holds on the final state: not judged"),
                true
            ),
            echo("/accept returns 1"),
            result("/accept returns 1", &judged, true),
            echo("/accept cmd"),
            failure("/accept cmd", ACCEPT_USAGE),
            echo("/accept status"),
            result("/accept status", &judged, true),
            echo("/accept clear"),
            result(
                "/accept clear",
                "Acceptance: unverified (no acceptance checks).",
                true
            ),
        ]
    );
    fixture.close().await;
}
