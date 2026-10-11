//! Port of `test/cloudflare-ai-binding.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::pi_ai::{Context, Model, StopReason};
use serde_json::json;

use super::{create_ai_binding_fetch, AiBinding, CLOUDFLARE_GATEWAY_BINDING_AUTH_SENTINEL};
use crate::api::openai_completions::stream_simple;
use crate::api::system_one_shared::test_fetch::{json_response, response};
use crate::types::{FetchFunction, ProviderRequestOptions, SimpleStreamOptions, StreamOptions};
use crate::utils::transcript::normalize_context;

const BINDING_PREFIX: &str = "https://workers-binding.ai/ai-gateway/gateways/my-gateway";

/// What the fake binding received.
#[derive(Debug, Clone)]
struct Seen {
    url: String,
    method: String,
    headers: Vec<(String, String)>,
    body: String,
}

type Responder = Arc<dyn Fn() -> reqwest::Response + Send + Sync>;

struct FakeBinding {
    requests: Arc<Mutex<Vec<Seen>>>,
    responder: Option<Responder>,
}

impl AiBinding for FakeBinding {
    fn ai_gateway_log_id(&self) -> Option<String> {
        None
    }

    fn fetch(&self) -> Option<FetchFunction> {
        let responder = self.responder.clone()?;
        let requests = Arc::clone(&self.requests);
        Some(Arc::new(move |request: reqwest::Request| {
            let seen = Seen {
                url: request.url().to_string(),
                method: request.method().to_string(),
                headers: request
                    .headers()
                    .iter()
                    .map(|(name, value)| {
                        (
                            name.as_str().to_owned(),
                            value.to_str().unwrap_or_default().to_owned(),
                        )
                    })
                    .collect(),
                body: request
                    .body()
                    .and_then(reqwest::Body::as_bytes)
                    .map(|bytes| String::from_utf8_lossy(bytes).into_owned())
                    .unwrap_or_default(),
            };
            requests
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(seen);
            let response = responder();
            Box::pin(async move { Ok(response) })
        }))
    }
}

fn fake_binding(responder: Responder) -> (FakeBinding, Arc<Mutex<Vec<Seen>>>) {
    let requests: Arc<Mutex<Vec<Seen>>> = Arc::default();
    (
        FakeBinding {
            requests: Arc::clone(&requests),
            responder: Some(responder),
        },
        requests,
    )
}

fn seen(requests: &Arc<Mutex<Vec<Seen>>>) -> Vec<Seen> {
    requests
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
}

#[tokio::test]
async fn passes_requests_to_the_binding_untouched() {
    let (binding, requests) = fake_binding(Arc::new(|| {
        response(
            200,
            &[
                ("content-type", "text/event-stream"),
                ("cf-aig-log-id", "log-1"),
            ],
            "data: {}\n\n".to_owned(),
        )
    }));
    let fetch = create_ai_binding_fetch(&binding).expect("fetch");
    let body =
        json!({ "model": "claude", "messages": [{ "role": "user", "content": "hi" }] }).to_string();
    let url = format!("{BINDING_PREFIX}/anthropic/v1/messages?beta=true");
    let mut request =
        reqwest::Request::new(reqwest::Method::POST, url::Url::parse(&url).expect("url"));
    let sentinel = format!("Bearer {CLOUDFLARE_GATEWAY_BINDING_AUTH_SENTINEL}");
    for (name, value) in [
        ("content-type", "application/json"),
        ("cf-aig-authorization", sentinel.as_str()),
        ("anthropic-version", "2023-06-01"),
    ] {
        request.headers_mut().insert(
            reqwest::header::HeaderName::from_static(name),
            reqwest::header::HeaderValue::from_str(value).expect("value"),
        );
    }
    *request.body_mut() = Some(body.clone().into());

    let response = fetch(request).await.expect("response");

    let requests = seen(&requests);
    assert_eq!(requests[0].url, url);
    assert_eq!(requests[0].method, "POST");
    assert_eq!(
        requests[0].headers,
        [
            ("content-type".to_owned(), "application/json".to_owned()),
            // The gateway recognizes and strips the sentinel itself; nothing here touches headers.
            ("cf-aig-authorization".to_owned(), sentinel.clone()),
            ("anthropic-version".to_owned(), "2023-06-01".to_owned()),
        ]
    );
    assert_eq!(requests[0].body, body);
    assert_eq!(
        response
            .headers()
            .get("cf-aig-log-id")
            .and_then(|value| value.to_str().ok()),
        Some("log-1")
    );
    assert_eq!(response.text().await.expect("text"), "data: {}\n\n");
}

#[test]
fn rejects_a_binding_with_no_fetch_at_construction_not_on_first_request() {
    let binding = FakeBinding {
        requests: Arc::default(),
        responder: None,
    };
    let Err(error) = create_ai_binding_fetch(&binding) else {
        panic!("expected an error");
    };
    assert!(error.to_string().contains("does not expose fetch()"));
}

#[tokio::test]
async fn keeps_sdk_placeholder_auth_off_the_wire_when_paired_with_null_auth_headers() {
    let (binding, requests) = fake_binding(Arc::new(|| {
        json_response(
            400,
            &json!({ "error": { "type": "bad_request", "message": "stubbed" } }),
        )
    }));
    let model: Model = serde_json::from_value(json!({
        "id": "test-model",
        "name": "Test Model",
        "api": "openai-completions",
        "provider": "openai",
        "baseUrl": format!("{BINDING_PREFIX}/openai"),
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 10_000,
        "maxTokens": 1_000,
    }))
    .expect("model");
    let context: Context = serde_json::from_value(json!({
        "messages": [{ "role": "user", "content": "hello", "timestamp": 1 }],
    }))
    .expect("context");
    let options = SimpleStreamOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                headers: Some(
                    [
                        (
                            "cf-aig-authorization".to_owned(),
                            Some(format!("Bearer {CLOUDFLARE_GATEWAY_BINDING_AUTH_SENTINEL}")),
                        ),
                        ("Authorization".to_owned(), None),
                        ("x-api-key".to_owned(), None),
                    ]
                    .into_iter()
                    .collect(),
                ),
                fetch: Some(create_ai_binding_fetch(&binding).expect("fetch")),
                max_retries: Some(0),
                ..ProviderRequestOptions::default()
            },
            ..StreamOptions::default()
        },
        ..SimpleStreamOptions::default()
    };

    let result = stream_simple(&model, &normalize_context(context), options)
        .result()
        .await;

    assert_eq!(result.stop_reason, StopReason::Error);
    let requests = seen(&requests);
    assert_eq!(requests.len(), 1);
    assert_eq!(
        requests[0].url,
        format!("{BINDING_PREFIX}/openai/chat/completions")
    );
    let names: Vec<&str> = requests[0]
        .headers
        .iter()
        .map(|(name, _)| name.as_str())
        .collect();
    assert!(!names.contains(&"authorization"));
    assert!(!names.contains(&"x-api-key"));
}
