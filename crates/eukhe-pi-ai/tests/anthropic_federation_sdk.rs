//! Port of `test/anthropic-federation-sdk.test.ts`: the module's SDK-side
//! federation against a fake fetch, checking how often the workload
//! identity token exchange happens
//! (<https://github.com/earendil-works/pi/issues/10177>).

mod anthropic_support;

use std::io::Write as _;

use anthropic_support::{federation_fetch, model, requests, Captured};
use eukhe_pi_ai::api::anthropic_messages::stream;
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{ProviderEnv, ProviderHeaders, StopReason, TranscriptContext};
use serde_json::json;
use tempfile::TempDir;

/// TS `beforeAll`: a temp dir holding `identity.jwt` and the env naming it.
/// Dropping the dir is the TS `afterAll`.
fn federation_env() -> (TempDir, ProviderEnv) {
    let temp_dir = tempfile::Builder::new()
        .prefix("pi-anthropic-federation-")
        .tempdir()
        .expect("temp dir");
    let identity_token_file = temp_dir.path().join("identity.jwt");
    std::fs::File::create(&identity_token_file)
        .and_then(|mut file| file.write_all(b"header.payload.signature"))
        .expect("write identity token");
    let env: ProviderEnv = [
        ("ANTHROPIC_FEDERATION_RULE_ID", "fdrl_test"),
        ("ANTHROPIC_ORGANIZATION_ID", "org-test"),
        (
            "ANTHROPIC_IDENTITY_TOKEN_FILE",
            identity_token_file.to_str().expect("utf-8 path"),
        ),
    ]
    .into_iter()
    .map(|(name, value)| (name.to_owned(), value.to_owned()))
    .collect();
    (temp_dir, env)
}

/// TS `RecordedRequest`s: `{ path, authorization }`.
fn recorded(captured: &Captured) -> Vec<(String, Option<String>)> {
    requests(captured)
        .iter()
        .map(|request| (request.path(), request.header("authorization")))
        .collect()
}

fn test_context() -> TranscriptContext {
    anthropic_support::context(&json!({
        "systemPrompt": "System prompt.",
        "messages": [{ "role": "user", "content": "Hello", "timestamp": 1 }],
    }))
}

/// Restores process env vars on drop (TS `vi.unstubAllEnvs`).
struct StubbedEnv(Vec<(String, Option<String>)>);

impl StubbedEnv {
    fn stub(env: &ProviderEnv) -> Self {
        let saved = env
            .iter()
            .map(|(name, value)| {
                let previous = std::env::var(name).ok();
                std::env::set_var(name, value);
                (name.clone(), previous)
            })
            .collect();
        Self(saved)
    }
}

impl Drop for StubbedEnv {
    fn drop(&mut self) {
        for (name, previous) in &self.0 {
            match previous {
                Some(value) => std::env::set_var(name, value),
                None => std::env::remove_var(name),
            }
        }
    }
}

#[tokio::test]
async fn exchanges_the_identity_token_once_across_requests() {
    let (_temp_dir, env) = federation_env();
    let (fetch, captured) = federation_fetch();

    for _ in 0..3 {
        let mut options = ProviderStreamOptions::default();
        options.stream.request.env = Some(env.clone());
        options.stream.request.fetch = Some(fetch.clone());
        let message = stream(&model(&json!({})), &test_context(), options)
            .result()
            .await;
        assert_eq!(
            message.stop_reason,
            StopReason::Stop,
            "{:?}",
            message.error_message
        );
    }

    let requests = recorded(&captured);
    assert_eq!(
        requests
            .iter()
            .filter(|(path, _)| path == "/v1/oauth/token")
            .count(),
        1,
        "{requests:?}"
    );
    let message_requests: Vec<_> = requests
        .iter()
        .filter(|(path, _)| path == "/v1/messages")
        .collect();
    assert_eq!(message_requests.len(), 3, "{requests:?}");
    for (_, authorization) in message_requests {
        assert_eq!(authorization.as_deref(), Some("Bearer federated-token"));
    }
}

#[tokio::test]
async fn does_not_run_the_sdk_credential_chain_for_header_owned_auth() {
    let (_temp_dir, env) = federation_env();
    let _stubbed = StubbedEnv::stub(&env);
    let (fetch, captured) = federation_fetch();

    let mut options = ProviderStreamOptions::default();
    let mut headers = ProviderHeaders::new();
    headers.insert("Authorization".into(), Some("Bearer auth-token".into()));
    options.stream.request.headers = Some(headers);
    options.stream.request.fetch = Some(fetch);
    let message = stream(&model(&json!({})), &test_context(), options)
        .result()
        .await;

    assert_eq!(
        message.stop_reason,
        StopReason::Stop,
        "{:?}",
        message.error_message
    );
    assert_eq!(
        recorded(&captured),
        [(
            "/v1/messages".to_owned(),
            Some("Bearer auth-token".to_owned())
        )]
    );
}
