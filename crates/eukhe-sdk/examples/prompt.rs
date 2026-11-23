//! A minimal embedding: one SDK run of a prompt, its budget report after.
//!
//! `cargo run -p eukhe-sdk --example prompt -- <agent dir> <cwd> <model> <prompt>`
//! (`<model>` as `provider/pattern`).
//! Prints the agent's answers, then the run's budget report as JSON.

use eukhe_sdk::context::BACKGROUND_CONTEXT;
use eukhe_sdk::{open_session, ModelRequest, SessionConfig, SessionStorage};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [agent_dir, cwd, model, text] = args.as_slice() else {
        anyhow::bail!("usage: prompt <agent dir> <cwd> <provider/model> <prompt>");
    };
    let (provider, pattern) = model
        .split_once('/')
        .ok_or_else(|| anyhow::anyhow!("model as provider/pattern"))?;
    let cx = &*BACKGROUND_CONTEXT;
    let mut config = SessionConfig::new(
        agent_dir,
        cwd,
        eukhe_sdk::new_session_id(),
        SessionStorage::Memory,
    );
    config.model = Some(ModelRequest {
        provider: Some(provider.to_owned()),
        pattern: pattern.to_owned(),
    });
    let session = open_session(config, cx).await?;
    let conversation = session.main();
    let mut notices = eukhe_sdk::watch_plan_notices(&session);
    let mut events = eukhe_sdk::watch(&session, &conversation, cx).await?;
    eukhe_sdk::prompt(&session, &conversation, text, cx).await?;
    events.delivered().await;
    events.stop().await;
    while let Some(batch) = events.try_next() {
        for event in batch.iter() {
            let event = serde_json::to_value(event)?;
            if event["entry"]["kind"] == "pi.assistant" {
                for block in event["entry"]["model"][0]["content"]
                    .as_array()
                    .into_iter()
                    .flatten()
                {
                    if let Some(text) = block["text"].as_str() {
                        println!("{text}");
                    }
                }
            }
        }
    }
    while let Ok(notice) = notices.try_recv() {
        println!("plan_usage {}", serde_json::to_string(&notice)?);
    }
    let report = eukhe_sdk::budget_report(&session).await?;
    println!("budget {}", serde_json::to_string(&report)?);
    session.close(cx).await?;
    Ok(())
}
