//! Port of `test/zen.test.ts`: the `OpenCode` smoke test (one TS case per
//! model) runs as one ignored test per provider over every model.

mod common;

use common::user;
use eukhe_pi_ai::compat::complete;
use eukhe_pi_ai::models_generated::MODELS;
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{Context, StopReason};

async fn smoke(key: &str, label: &str) {
    for model in MODELS.get(key).expect("provider models").values() {
        let response = tokio::time::timeout(
            std::time::Duration::from_secs(60),
            complete(
                model,
                Context {
                    system_prompt: None,
                    messages: vec![user("Say hello.")],
                    tools: None,
                },
                ProviderStreamOptions::default(),
            ),
        )
        .await
        .unwrap_or_else(|_| panic!("{label}: {} timed out", model.id))
        .unwrap_or_else(|error| panic!("{label}: {}: {error:?}", model.id));

        assert!(!response.content.is_empty(), "{label}: {}", model.id);
        assert_eq!(
            response.stop_reason,
            StopReason::Stop,
            "{label}: {}",
            model.id
        );
    }
}

#[tokio::test]
#[ignore = "needs OPENCODE_API_KEY; run with --ignored"]
async fn opencode_zen_models() {
    smoke("opencode", "OpenCode Zen").await;
}

#[tokio::test]
#[ignore = "needs OPENCODE_API_KEY; run with --ignored"]
async fn opencode_go_models() {
    smoke("opencode-go", "OpenCode Go").await;
}
