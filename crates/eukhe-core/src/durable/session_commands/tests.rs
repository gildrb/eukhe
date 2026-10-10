//! Session commands on an open eukhe session with faux script models.

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::entries::{COMPACTION_ENTRY, USER_ENTRY};
use eukhe_durable::harness::types::InputSubmissionDraft;
use eukhe_durable::harness::ConversationEntryQuery;
use eukhe_durable::types::{EntryRecord, TaskOutcome};
use eukhe_pi_ai::providers::faux_script::{create_faux_script_models, parse_faux_script};
use eukhe_types::pi_ai::{Message, UserContent};
use serde_json::{json, Value};

use super::*;
use crate::autonomous::AgentAutonomousConfig;
use crate::durable::entries::{CustomEntryData, CustomStateData, CUSTOM_ENTRY, CUSTOM_STATE_ENTRY};
use crate::durable::{open_session, ModelRequest, SessionConfig, SessionStorage};
use crate::session_engine::refine::REFINEMENT_AUDIT_CUSTOM_TYPE;

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

struct Fixture {
    _dir: tempfile::TempDir,
    session: EukheSession,
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
    let (models, _provider) = create_faux_script_models(script);
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
    Fixture { _dir: dir, session }
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
        classify_session_command("/autonomous on").map(|command| command.name),
        Some(SessionCommandName::Autonomous)
    );
    assert_eq!(classify_session_command("/model"), None);
    assert_eq!(classify_session_command("/unknown x"), None);
    assert_eq!(classify_session_command("compact"), None);
    for name in [
        SessionCommandName::Compact,
        SessionCommandName::Refine,
        SessionCommandName::Goal,
        SessionCommandName::Autonomous,
    ] {
        assert_eq!(SessionCommandName::from_name(name.as_str()), Some(name));
    }
}

#[tokio::test]
async fn goal_status_without_a_goal_answers_no_active_goal() {
    let fixture = open(&[]).await;
    let outcome = fixture.run("/goal").await;
    assert_eq!(outcome.error, None);
    assert_eq!(outcome.goal, Some(GoalState::default()));
    assert_eq!(
        fixture.command_rows().await,
        vec![echo("/goal"), result("/goal", "No active goal.", true)]
    );
    fixture.close().await;
}

#[tokio::test]
async fn goal_start_submits_its_continuation_and_reports_the_goal() {
    // The first run fails at the provider: no continuation follows it.
    let fixture = open(&[error_response("provider exploded")]).await;
    let outcome = fixture.run("/goal ship it").await;
    assert_eq!(outcome.error, None);
    let goal = outcome.goal.expect("the goal");
    assert_eq!(goal.status, GoalStatus::Active);
    assert_eq!(goal.objective.as_deref(), Some("ship it"));
    fixture.idle().await;
    assert_eq!(
        fixture.command_rows().await,
        vec![
            echo("/goal ship it"),
            result("/goal ship it", "Goal active: ship it", true),
        ]
    );
    let texts = fixture.user_texts().await;
    assert_eq!(texts.len(), 1, "{texts:?}");
    assert!(texts[0].starts_with("[goal: continuation]"), "{texts:?}");
    fixture.close().await;
}

#[tokio::test]
async fn goal_pause_resume_and_clear_report_each_state() {
    let fixture = open(&[
        error_response("provider exploded"),
        error_response("provider exploded again"),
    ])
    .await;
    fixture.run("/goal ship it").await;
    fixture.idle().await;

    let paused = fixture.run("/goal pause").await;
    assert_eq!(paused.error, None);
    assert_eq!(
        paused.goal.as_ref().map(|goal| goal.status),
        Some(GoalStatus::Paused)
    );

    let resumed = fixture.run("/goal resume").await;
    assert_eq!(resumed.error, None);
    assert_eq!(
        resumed.goal.as_ref().map(|goal| goal.status),
        Some(GoalStatus::Active)
    );
    fixture.idle().await;
    let texts = fixture.user_texts().await;
    assert_eq!(texts.len(), 2, "{texts:?}");

    let cleared = fixture.run("/goal clear").await;
    assert_eq!(cleared.error, None);
    let cleared_goal = cleared.goal.expect("the goal");
    assert_eq!(
        (cleared_goal.status, cleared_goal.objective),
        (GoalStatus::Idle, None)
    );
    let again = fixture.run("/goal clear").await;
    let again_goal = again.goal.expect("the goal");
    assert_eq!(
        (again_goal.status, again_goal.objective),
        (GoalStatus::Idle, None)
    );

    assert_eq!(
        fixture.command_rows().await,
        vec![
            echo("/goal ship it"),
            result("/goal ship it", "Goal active: ship it", true),
            echo("/goal pause"),
            result("/goal pause", "Goal paused: ship it", true),
            echo("/goal resume"),
            result("/goal resume", "Goal active: ship it", true),
            echo("/goal clear"),
            result("/goal clear", "Goal cleared.", true),
            echo("/goal clear"),
            result("/goal clear", "No active goal.", true),
        ]
    );
    fixture.close().await;
}

#[tokio::test]
async fn an_invalid_goal_command_appends_the_failure_row() {
    let fixture = open(&[]).await;
    let text = "/goal --budget nope ship it";
    let expected = parse_goal_command(&command(text).args).expect_err("an invalid budget");
    let outcome = fixture.run(text).await;
    assert_eq!(outcome.error.as_deref(), Some(expected.as_str()));
    assert_eq!(outcome.goal, None);
    assert_eq!(
        fixture.command_rows().await,
        vec![echo(text), failure(text, &expected)]
    );
    fixture.close().await;
}

#[tokio::test]
async fn autonomous_status_on_and_off_append_status_rows() {
    let fixture = open(&[]).await;
    let status = fixture.run("/autonomous").await;
    assert_eq!(status.error, None);
    let off = status.autonomous.expect("the status");
    assert!(!off.enabled);

    let on = fixture.run("/autonomous on --max-turns 5").await;
    assert_eq!(on.error, None);
    let enabled = on.autonomous.expect("the status");
    assert!(enabled.enabled);
    let AutonomousCommand::On { config } =
        parse_autonomous_command("on --max-turns 5").expect("parses")
    else {
        panic!("expected on");
    };
    assert_ne!(config, AgentAutonomousConfig::default());

    let disabled = fixture.run("/autonomous off").await;
    assert_eq!(disabled.error, None);
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
    let expected = parse_autonomous_command(&command(text).args).expect_err("extra arguments");
    let outcome = fixture.run(text).await;
    assert_eq!(outcome.error.as_deref(), Some(expected.as_str()));
    assert_eq!(outcome.autonomous, None);
    assert_eq!(
        fixture.command_rows().await,
        vec![echo(text), failure(text, &expected)]
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
    assert_eq!(outcome.error, None);
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
            CUSTOM_ENTRY.kind(),
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
    assert_eq!(outcome.error.as_deref(), Some(error));
    assert_eq!(outcome.refinement_failed.as_deref(), Some(error));
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
    assert_eq!(outcome.error.as_deref(), Some(error));
    // A usage error never ran a refinement.
    assert_eq!(outcome.refinement_failed, None);
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
    assert_eq!(outcome.error, None);
    assert_eq!(outcome.refinement_failed, None);
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
