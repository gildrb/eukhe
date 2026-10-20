use std::path::{Path, PathBuf};

use eukhe_ai::models::{create_models as create_pi_models, CreateModelsOptions};
use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_provider, FauxAssistantMessageOptions, FauxProviderHandle,
    RegisterFauxProviderOptions,
};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::types::{ConversationCreateOptions, InputSubmissionDraft, ModelRef};
use eukhe_durable::harness::ConversationEntryQuery;
use eukhe_durable::types::ConversationOwnership;
use futures::FutureExt;
use serde_json::{json, Value};

use super::*;
use crate::durable::{
    open_session, set_main_conversation, EukheSettings, SessionConfig, SessionStorage,
};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

struct Fixture {
    _dir: tempfile::TempDir,
    agent_dir: PathBuf,
    cwd: PathBuf,
    faux: FauxProviderHandle,
    models: eukhe_ai::models::Models,
}

fn fixture() -> Fixture {
    let dir = tempfile::tempdir().expect("tempdir");
    let agent_dir = dir.path().join("agent");
    let cwd = dir.path().join("project");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    std::fs::create_dir_all(&cwd).expect("cwd");
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_pi_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    Fixture {
        _dir: dir,
        agent_dir,
        cwd,
        faux,
        models,
    }
}

impl Fixture {
    fn config(&self) -> SessionConfig {
        let id = "0192a000-0000-7000-8000-000000000001";
        let mut config = SessionConfig::new(
            &self.agent_dir,
            &self.cwd,
            id,
            SessionStorage::Jsonl {
                dir: self.agent_dir.join("sessions").join(id),
                fsync: true,
            },
        );
        config.models = Some(self.models.clone());
        let model = self.faux.get_model();
        config.model = Some(
            ModelRef {
                provider: model.provider,
                model_id: model.id,
            }
            .into(),
        );
        config
    }
}

fn transport(settings: &EukheSettings) -> Option<Value> {
    settings.manager().cvars().value_of("transport")
}

fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().expect("parent")).expect("mkdir");
    std::fs::write(path, text).expect("write");
}

/// A `/set` commits the agent state on the main conversation: a fork at
/// an earlier entry starts from the state as of that entry, the session
/// reads it when the fork becomes main, and a reopen keeps it.
#[tokio::test]
async fn a_fork_starts_from_the_agent_state_at_its_fork_point() {
    let fixture = fixture();
    fixture.faux.set_responses(vec![faux_assistant_message(
        "answer",
        FauxAssistantMessageOptions::default(),
    )
    .into()]);
    let session = open_session(fixture.config(), cx()).await.expect("open");
    run_cvar_line(&session, "set transport sse", CvarLineScope::Session, cx())
        .await
        .expect("set");
    session
        .root()
        .submit(InputSubmissionDraft::new("question"), cx())
        .await
        .expect("submit")
        .wait(cx())
        .await
        .expect("wait");
    run_cvar_line(
        &session,
        "set transport web-socket",
        CvarLineScope::Session,
        cx(),
    )
    .await
    .expect("set");
    let settings = &session.deps().settings;
    assert_eq!(transport(settings), Some(json!("web-socket")));

    let at = session
        .root()
        .entries(ConversationEntryQuery::default(), 1000, None, cx())
        .await
        .expect("entries")
        .items
        .into_iter()
        .find(|entry| entry.kind == "pi.user")
        .expect("user entry")
        .id;
    let mut options = ConversationCreateOptions::new(ConversationOwnership::Ownerless);
    options.init = Some(Box::new(|tx, id| {
        async move { set_main_conversation(&tx, id).await }.boxed()
    }));
    let fork = session.root().fork(at, options, cx()).await.expect("fork");
    session.reload_main(cx()).await.expect("main");
    assert_eq!(
        session.deps().settings.agent_state(),
        AgentState {
            sets: Sets(vec![Set {
                id: "transport".to_string(),
                value: json!("sse"),
            }]),
            aliases: Vec::new(),
        }
    );
    assert_eq!(transport(&session.deps().settings), Some(json!("sse")));
    session.close(cx()).await.expect("close");

    let session = open_session(fixture.config(), cx()).await.expect("reopen");
    assert_eq!(session.main().id(), fork.id());
    assert_eq!(transport(&session.deps().settings), Some(json!("sse")));
    session
        .set_main(&session.root().clone(), cx())
        .await
        .expect("set main");
    assert_eq!(
        transport(&session.deps().settings),
        Some(json!("web-socket"))
    );
    session.close(cx()).await.expect("close");
}

/// A session cannot set a Global cvar, a rejected command applies
/// nothing of its line, and an alias the session defines runs its body
/// and is kept in the agent state.
#[tokio::test]
async fn a_session_line_applies_whole_or_not_at_all() {
    let fixture = fixture();
    let session = open_session(fixture.config(), cx()).await.expect("open");
    let rejected = run_cvar_line(
        &session,
        "set transport sse; set rlmMaxDepth 5",
        CvarLineScope::Session,
        cx(),
    )
    .await;
    assert!(
        matches!(
            &rejected,
            Err(CvarLineError::Cvar(CvarError::Global { id })) if id == "rlmMaxDepth"
        ),
        "{rejected:?}"
    );
    assert_eq!(session.deps().settings.agent_state(), AgentState::default());

    run_cvar_line(
        &session,
        "alias quiet \"set retry.enabled false; toggle compaction.enabled\"; quiet",
        CvarLineScope::Session,
        cx(),
    )
    .await
    .expect("alias");
    assert_eq!(
        session.deps().settings.agent_state(),
        AgentState {
            sets: Sets(vec![
                Set {
                    id: "retry.enabled".to_string(),
                    value: json!(false),
                },
                Set {
                    id: "compaction.enabled".to_string(),
                    value: json!(false),
                },
            ]),
            aliases: vec![AliasEntry {
                name: "quiet".to_string(),
                body: "set retry.enabled false; toggle compaction.enabled".to_string(),
            }],
        }
    );
    session.close(cx()).await.expect("close");
}

/// `/set --global` writes the global config.cfg (every session reads it),
/// and `cvar save` writes the session's persisting sets to
/// `agents/main.cfg`.
#[tokio::test]
async fn global_lines_and_saves_write_the_cfg_files() {
    let fixture = fixture();
    let session = open_session(fixture.config(), cx()).await.expect("open");
    run_cvar_line(&session, "set rlmMaxDepth 5", CvarLineScope::Global, cx())
        .await
        .expect("global set");
    assert_eq!(
        session
            .deps()
            .settings
            .manager()
            .cvars()
            .value_of("rlmMaxDepth"),
        Some(json!(5))
    );
    let other = EukheSettings::new(&fixture.cwd, &fixture.agent_dir);
    assert_eq!(
        other.manager().cvars().value_of("rlmMaxDepth"),
        Some(json!(5))
    );
    let not_global = run_cvar_line(
        &session,
        "alias a \"set transport sse\"",
        CvarLineScope::Global,
        cx(),
    )
    .await;
    assert!(
        matches!(&not_global, Err(CvarLineError::NotGlobal { .. })),
        "{not_global:?}"
    );

    run_cvar_line(&session, "set transport sse", CvarLineScope::Session, cx())
        .await
        .expect("set");
    save_agent_cfg(&session).await.expect("save");
    assert_eq!(
        std::fs::read_to_string(fixture.agent_dir.join("agents/main.cfg")).expect("main.cfg"),
        "set transport sse\n"
    );
    session.close(cx()).await.expect("close");
}

/// A subagent starts from its parent's family: it inherits the parent's
/// Local set, `subagent.cfg` overrides it, and a Global cvar keeps the
/// config's value whatever a profile says.
#[test]
fn a_subagent_inherits_its_parents_family_under_its_profile() {
    let dir = tempfile::tempdir().expect("tempdir");
    let agent_dir = dir.path().join("agent");
    let cwd = dir.path().join("project");
    write(&agent_dir.join("settings.json"), r#"{"rlmMaxDepth": 2}"#);
    let parent = EukheSettings::new(&cwd, &agent_dir);
    let state = parent
        .plan(&eukhe_types::cvar::parse_list("set transport sse").expect("parse"))
        .expect("plan")
        .expect("a change");
    parent.set_agent_state(state);
    let family = parent.manager().cvars().family().to_vec();

    let child = EukheSettings::with_agent(
        &cwd,
        &agent_dir,
        CvarAgent::Subagent {
            inherited: family,
            name: Some("scout".to_string()),
        },
    );
    let values = |settings: &EukheSettings| {
        let cvars = settings.manager().cvars().clone();
        (cvars.value_of("transport"), cvars.value_of("rlmMaxDepth"))
    };
    assert_eq!(values(&child), (Some(json!("sse")), Some(json!(2))));

    write(
        &agent_dir.join("subagent.cfg"),
        "set transport web-socket\nset rlmMaxDepth 9\n",
    );
    assert_eq!(values(&child), (Some(json!("web-socket")), Some(json!(2))));

    write(&agent_dir.join("agents/scout.cfg"), "set transport auto\n");
    assert_eq!(values(&child), (Some(json!("auto")), Some(json!(2))));
    assert_eq!(values(&parent), (Some(json!("sse")), Some(json!(2))));
}

/// The settings error rows of `main` (oldest first), once there are
/// `count` of them.
async fn settings_error_rows(main: &Conversation, count: usize) -> Vec<Value> {
    for _ in 0..500 {
        let rows: Vec<Value> = main
            .entries(ConversationEntryQuery::default(), 1000, None, cx())
            .await
            .expect("entries")
            .items
            .iter()
            .rev()
            .map(|entry| serde_json::to_value(&entry.data).expect("entry data"))
            .filter(|data| {
                data["customType"] == crate::durable::settings::SETTINGS_ERROR_CUSTOM_TYPE
            })
            .map(|data| json!([data["content"], data["display"]]))
            .collect();
        if rows.len() >= count {
            return rows;
        }
        tokio::time::sleep(std::time::Duration::from_millis(20)).await;
    }
    panic!("fewer than {count} settings error rows");
}

/// Regression: the settings errors of a session (here a bad line of the
/// global config.cfg) reached no one. They show as a row of the main
/// conversation at open, and a reload that finds a new error shows a row
/// of the new error only.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn settings_errors_show_as_a_row_of_the_session() {
    let fixture = fixture();
    let config = fixture.agent_dir.join("config.cfg");
    write(&config, "set nope on\n");
    let session = open_session(fixture.config(), cx()).await.expect("open");
    let first = json!([
        "Settings errors (the rest of the settings apply):\n- global: config.cfg: no cvar `nope`",
        true
    ]);
    assert_eq!(
        settings_error_rows(&session.main(), 1).await,
        vec![first.clone()]
    );

    write(&config, "set nope on\nset transport pigeon\n");
    let _reload = session.deps().settings.harness();
    assert_eq!(
        settings_error_rows(&session.main(), 2).await,
        vec![
            first,
            json!([
                "Settings errors (the rest of the settings apply):\n- global: config.cfg: `pigeon` is not a value of `transport` (one of auto, sse, web-socket, websocket-cached)",
                true
            ]),
        ]
    );
    session.close(cx()).await.expect("close");
}

/// Regression: an `mcpServers` entry that did not parse was dropped from
/// the session with no word. It shows on the settings error row.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_bad_mcp_server_shows_as_a_settings_error_row() {
    let fixture = fixture();
    write(
        &fixture.agent_dir.join("settings.json"),
        r#"{"mcpServers": {"bad": {"type": "http"}}}"#,
    );
    let session = open_session(fixture.config(), cx()).await.expect("open");
    assert_eq!(
        settings_error_rows(&session.main(), 1).await,
        vec![json!([
            "Settings errors (the rest of the settings apply):\n- global: mcpServers.bad: missing field `url`",
            true
        ])]
    );
    session.close(cx()).await.expect("close");
}
