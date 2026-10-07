//! Port of `test/responseid.test.ts`: every provider exposes the upstream
//! response id. All cases hit real endpoints; the TS suites are skipped
//! without credentials, here they are `#[ignore]`d. TS `resolveApiKey()`
//! OAuth tokens (read from `~/.pi/agent/oauth.json`) come from the env vars
//! named in the ignore reasons. TS `{ retry: 3 }` is a loop of 3 attempts.

use std::future::Future;

use eukhe_pi_ai::compat::{complete, get_model};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{Context, Model, StopReason};
use serde_json::{json, Value as JsonValue};

fn env_value(name: &str) -> Option<String> {
    std::env::var(name).ok().filter(|value| !value.is_empty())
}

fn require_env(name: &str) -> String {
    env_value(name).unwrap_or_else(|| panic!("Missing {name}; this test needs it set"))
}

fn builtin(provider: &str, id: &str) -> Model {
    get_model(provider, id).unwrap_or_else(|| panic!("unknown model {provider}/{id}"))
}

fn options(api_key: Option<String>, extra: &JsonValue) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = api_key;
    options.extra = serde_json::from_value(extra.clone()).expect("extra options");
    options
}

fn has_azure_openai_credentials() -> bool {
    env_value("AZURE_OPENAI_API_KEY").is_some()
        && (env_value("AZURE_OPENAI_BASE_URL").is_some()
            || env_value("AZURE_OPENAI_RESOURCE_NAME").is_some())
}

/// TS `resolveAzureDeploymentName()`: the last `modelId=deployment` entry of
/// `AZURE_OPENAI_DEPLOYMENT_NAME_MAP` for `model_id`.
fn resolve_azure_deployment_name(model_id: &str) -> Option<String> {
    let map_value = env_value("AZURE_OPENAI_DEPLOYMENT_NAME_MAP")?;
    map_value
        .split(',')
        .filter_map(|entry| {
            let mut parts = entry.trim().split('=');
            let id = parts.next()?.trim();
            let deployment = parts.next()?.trim();
            (!id.is_empty() && !deployment.is_empty()).then_some((id, deployment))
        })
        .rfind(|(id, _)| *id == model_id)
        .map(|(_, deployment)| deployment.to_owned())
}

fn azure_options(model: &Model) -> ProviderStreamOptions {
    match resolve_azure_deployment_name(&model.id) {
        Some(name) => options(None, &json!({ "azureDeploymentName": name })),
        None => options(None, &json!({})),
    }
}

/// TS `{ retry: 3 }`.
async fn with_retries<F, Fut>(mut attempt: F)
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<(), String>>,
{
    let mut failure = String::new();
    for number in 1..=3 {
        match attempt().await {
            Ok(()) => return,
            Err(error) => {
                eprintln!("attempt {number} failed: {error}");
                failure = error;
            }
        }
    }
    panic!("{failure}");
}

async fn expect_response_id(model: &Model, options: ProviderStreamOptions) -> Result<(), String> {
    let context: Context = serde_json::from_value(json!({
        "systemPrompt": "You are a helpful assistant. Be concise.",
        "messages": [{
            "role": "user",
            "content": "Reply with exactly: response id test",
            "timestamp": common_now(),
        }],
    }))
    .expect("context");

    let response = complete(model, context, options)
        .await
        .map_err(|error| format!("{error:?}"))?;

    if response.stop_reason == StopReason::Error {
        return Err(format!(
            "stopReason is \"error\": {:?}",
            response.error_message
        ));
    }
    match response.response_id.as_deref() {
        Some(id) if !id.is_empty() => Ok(()),
        other => Err(format!("responseId is not a non-empty string: {other:?}")),
    }
}

fn common_now() -> u64 {
    u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock after epoch")
            .as_millis(),
    )
    .expect("epoch millis fit u64")
}

async fn run(model: Model, make_options: impl Fn() -> ProviderStreamOptions) {
    with_retries(|| expect_response_id(&model, make_options())).await;
}

#[tokio::test]
#[ignore = "needs GEMINI_API_KEY; run with --ignored"]
async fn google_provider_should_expose_response_id() {
    require_env("GEMINI_API_KEY");
    run(builtin("google", "gemini-2.5-flash"), || {
        options(None, &json!({}))
    })
    .await;
}

#[tokio::test]
#[ignore = "needs GOOGLE_CLOUD_PROJECT (or GCLOUD_PROJECT), GOOGLE_CLOUD_LOCATION and ADC; run with --ignored"]
async fn google_vertex_provider_should_expose_response_id_with_adc() {
    let project = env_value("GOOGLE_CLOUD_PROJECT")
        .or_else(|| env_value("GCLOUD_PROJECT"))
        .expect("Missing GOOGLE_CLOUD_PROJECT or GCLOUD_PROJECT");
    let location = require_env("GOOGLE_CLOUD_LOCATION");
    run(builtin("google-vertex", "gemini-3-flash-preview"), || {
        options(None, &json!({ "project": project, "location": location }))
    })
    .await;
}

#[tokio::test]
#[ignore = "needs GOOGLE_CLOUD_API_KEY; run with --ignored"]
async fn google_vertex_provider_should_expose_response_id_with_api_key() {
    let api_key = require_env("GOOGLE_CLOUD_API_KEY");
    run(builtin("google-vertex", "gemini-3-flash-preview"), || {
        options(Some(api_key.clone()), &json!({}))
    })
    .await;
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_completions_provider_should_expose_response_id() {
    require_env("OPENAI_API_KEY");
    // `{ compat: _compat, ...baseModel }` with `api: "openai-completions"`.
    let model = Model {
        api: "openai-completions".into(),
        compat: None,
        ..builtin("openai", "gpt-4o-mini")
    };
    run(model, || options(None, &json!({}))).await;
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_responses_provider_should_expose_response_id() {
    require_env("OPENAI_API_KEY");
    run(builtin("openai", "gpt-5-mini"), || {
        options(None, &json!({}))
    })
    .await;
}

#[tokio::test]
#[ignore = "needs ANTHROPIC_API_KEY; run with --ignored"]
async fn anthropic_provider_should_expose_response_id() {
    require_env("ANTHROPIC_API_KEY");
    run(builtin("anthropic", "claude-sonnet-4-5"), || {
        options(None, &json!({}))
    })
    .await;
}

#[tokio::test]
#[ignore = "needs AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME; run with --ignored"]
async fn azure_openai_responses_provider_should_expose_response_id() {
    assert!(
        has_azure_openai_credentials(),
        "Missing AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME"
    );
    let model = builtin("azure", "gpt-4o-mini");
    let opts_model = model.clone();
    run(model, || azure_options(&opts_model)).await;
}

#[tokio::test]
#[ignore = "needs MISTRAL_API_KEY; run with --ignored"]
async fn mistral_provider_should_expose_response_id() {
    require_env("MISTRAL_API_KEY");
    run(builtin("mistral", "devstral-medium-latest"), || {
        options(None, &json!({}))
    })
    .await;
}

#[tokio::test]
#[ignore = "needs GITHUB_COPILOT_OAUTH_TOKEN; run with --ignored"]
async fn github_copilot_provider_openai_path_should_expose_response_id() {
    let token = require_env("GITHUB_COPILOT_OAUTH_TOKEN");
    run(builtin("github-copilot", "gpt-5.3-codex"), || {
        options(Some(token.clone()), &json!({}))
    })
    .await;
}

#[tokio::test]
#[ignore = "needs GITHUB_COPILOT_OAUTH_TOKEN; run with --ignored"]
async fn github_copilot_provider_anthropic_path_should_expose_response_id() {
    let token = require_env("GITHUB_COPILOT_OAUTH_TOKEN");
    run(builtin("github-copilot", "claude-sonnet-4.6"), || {
        options(Some(token.clone()), &json!({}))
    })
    .await;
}

#[tokio::test]
#[ignore = "needs OPENAI_CODEX_OAUTH_TOKEN; run with --ignored"]
async fn openai_codex_provider_should_expose_response_id() {
    let token = require_env("OPENAI_CODEX_OAUTH_TOKEN");
    run(builtin("openai-codex", "gpt-5.5"), || {
        options(Some(token.clone()), &json!({}))
    })
    .await;
}
