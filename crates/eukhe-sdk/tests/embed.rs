//! A host embeds the engine through the facade alone: it lists the models,
//! opens a session on the scripted faux provider, prompts it and reads the
//! answer from the conversation's event stream; it sets, watches, adds to,
//! reads and audits a session's budget.

use std::time::Duration;

use eukhe_ai::providers::faux_script::{create_faux_script_models, parse_faux_script};
use eukhe_sdk::budget::{
    BudgetAmounts, BudgetLimits, BudgetReport, BudgetSources, LimitSource, RunKind,
};
use eukhe_sdk::context::BACKGROUND_CONTEXT;
use eukhe_sdk::{
    add_budget, audit_budget, available_models, budget_report, new_session_id, open_session,
    prompt, set_budget, watch, watch_budget, AgentEvent, BudgetAudit, ModelRequest, SessionConfig,
    SessionStorage,
};

#[tokio::test]
async fn a_host_opens_a_session_prompts_it_and_reads_its_events() {
    let cx = &*BACKGROUND_CONTEXT;
    let dir = tempfile::TempDir::new().unwrap();
    let script =
        parse_faux_script(&serde_json::json!({ "responses": ["hello from faux"] }).to_string())
            .unwrap();
    let model_id = script.model.id.clone();
    let (models, _provider) = create_faux_script_models(script);
    let listed: Vec<(String, String)> = available_models(&models)
        .await
        .unwrap()
        .into_iter()
        .map(|model| (model.provider, model.id))
        .collect();
    assert_eq!(listed, [("faux".to_owned(), model_id.clone())]);

    let mut config = SessionConfig::new(
        dir.path().join("agent"),
        dir.path(),
        new_session_id(),
        SessionStorage::Memory,
    );
    config.models = Some(models);
    config.model = Some(ModelRequest {
        provider: Some("faux".to_owned()),
        pattern: model_id,
    });
    let session = open_session(config, cx).await.unwrap();
    let conversation = session.main();
    let mut events = watch(&session, &conversation, cx).await.unwrap();
    prompt(&session, &conversation, "hi", cx).await.unwrap();
    events.delivered().await;
    events.stop().await;

    let mut framing = Vec::new();
    let mut answers = Vec::new();
    while let Some(batch) = events.try_next() {
        for event in batch.iter() {
            if matches!(
                event,
                AgentEvent::RunStart { .. }
                    | AgentEvent::TurnStart
                    | AgentEvent::TurnEnd
                    | AgentEvent::RunEnd { .. }
            ) {
                framing.push(event.kind());
            }
            if !matches!(event, AgentEvent::MessageEnd { .. }) {
                continue;
            }
            let event = serde_json::to_value(event).unwrap();
            if event["entry"]["kind"] == "pi.assistant" {
                answers.extend(
                    event["entry"]["model"][0]["content"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .filter_map(|block| block["text"].as_str().map(str::to_owned)),
                );
            }
        }
    }
    session.close(cx).await.unwrap();
    assert_eq!(
        (framing, answers),
        (
            vec!["run_start", "turn_start", "turn_end", "run_end"],
            vec!["hello from faux".to_owned()]
        )
    );
}

/// A budget set through the facade is the session's: it reads back with
/// its limits free as the principal's for an SDK run, its change reaches
/// the watch, a second set replaces it, added budget raises it, and its
/// ledger replays exactly (B1, B6, B8, B9, B15, B19).
#[tokio::test]
async fn a_host_sets_watches_adds_to_reads_and_audits_a_sessions_budget() {
    let cx = &*BACKGROUND_CONTEXT;
    let dir = tempfile::TempDir::new().unwrap();
    let script =
        parse_faux_script(&serde_json::json!({ "responses": ["unused"] }).to_string()).unwrap();
    let model_id = script.model.id.clone();
    let (models, _provider) = create_faux_script_models(script);
    let session_id = new_session_id();
    let mut config = SessionConfig::new(
        dir.path().join("agent"),
        dir.path(),
        session_id.clone(),
        SessionStorage::Memory,
    );
    config.models = Some(models);
    config.model = Some(ModelRequest {
        provider: Some("faux".to_owned()),
        pattern: model_id,
    });
    let session = open_session(config, cx).await.unwrap();

    let amounts = |tokens| BudgetAmounts {
        tokens,
        ..BudgetAmounts::default()
    };
    let limits = |tokens| BudgetLimits {
        tokens: Some(tokens),
        ..BudgetLimits::default()
    };
    let mut changes = watch_budget(&session);
    let before = budget_report(&session).await.unwrap();
    let set = set_budget(&session, limits(100_000)).await.unwrap();
    tokio::time::timeout(Duration::from_secs(20), changes.changed())
        .await
        .expect("the set budget reaches the watch")
        .unwrap();
    let watched = changes.borrow_and_update().clone();
    let again = set_budget(&session, limits(7)).await.unwrap();
    let added = add_budget(&session, amounts(25_000)).await.unwrap();
    let read = budget_report(&session).await.unwrap();
    let audit = audit_budget(&session).await.unwrap();
    session.close(cx).await.unwrap();

    let report = |tokens| BudgetReport {
        session_id: session_id.clone(),
        agent_session_id: session_id.clone(),
        limits: limits(tokens),
        free: amounts(tokens),
        kind: Some(RunKind::Sdk),
        sources: BudgetSources {
            tokens: LimitSource::Set,
            ..BudgetSources::default()
        },
        ..BudgetReport::default()
    };
    assert_eq!(
        (before, set, watched, again, added, read, audit),
        (
            None,
            report(100_000),
            Some(report(100_000)),
            report(7),
            report(25_007),
            Some(report(25_007)),
            BudgetAudit {
                records: 3,
                settled: BudgetAmounts::default(),
                spent: BudgetAmounts::default(),
                exact: true,
                first_mismatch: None,
            },
        )
    );
}
