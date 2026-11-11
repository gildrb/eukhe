//! A host embeds the engine through the facade alone: it lists the models,
//! opens a session on the scripted faux provider, prompts it and reads the
//! answer from the conversation's event stream.

use eukhe_ai::providers::faux_script::{create_faux_script_models, parse_faux_script};
use eukhe_sdk::context::BACKGROUND_CONTEXT;
use eukhe_sdk::{
    available_models, new_session_id, open_session, prompt, watch, AgentEvent, ModelRequest,
    SessionConfig, SessionStorage,
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
    prompt(&conversation, "hi", cx).await.unwrap();
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
