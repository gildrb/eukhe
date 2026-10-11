//! Port of `test/github-copilot-oauth.test.ts` (plus the Copilot cases of
//! `test/oauth-auth.test.ts`). `githubCopilotProvider().getModels()` ids come
//! from the same catalog, `GITHUB_COPILOT_MODELS`; the `Models`
//! (`getAvailable`, `models.login`) halves of those cases live with the
//! models port. Fake timers become tokio paused time.

use std::sync::{Arc, Mutex, PoisonError};

use serde_json::{json, Value};
use tokio::time::Instant;

use super::{github_copilot_oauth, js_parse_float};
use crate::auth::errors::js_error;
use crate::auth::oauth::http::{mock, FetchRequest, FetchResponse};
use crate::auth::oauth::test_support::{never_aborted_signal, Events, TestInteraction};
use crate::auth::types::{AuthEvent, AuthPromptKind, ModelAuth, OAuthCredential};
use crate::providers::github_copilot_models::GITHUB_COPILOT_MODELS;
use crate::utils::diagnostics::Thrown;

const TEST_COPILOT_ACCESS_TOKEN: &str =
    "tid=test;exp=9999999999;proxy-ep=proxy.individual.githubcopilot.com;";
const TEST_COPILOT_MODELS_URL: &str = "https://api.individual.githubcopilot.com/models";

fn json_response(body: &Value, status: u16) -> FetchResponse {
    FetchResponse::json_response(body, status)
}

fn with_header(mut response: FetchResponse, name: &str, value: &str) -> FetchResponse {
    response.headers.push((name.to_owned(), value.to_owned()));
    response
}

fn empty_ok() -> FetchResponse {
    FetchResponse {
        status: 200,
        status_text: String::new(),
        headers: Vec::new(),
        body: String::new(),
    }
}

fn require_model_id(index: usize) -> String {
    GITHUB_COPILOT_MODELS
        .keys()
        .nth(index)
        .unwrap_or_else(|| panic!("Expected a GitHub Copilot model at index {index}"))
        .clone()
}

async fn install(
    route: impl Fn(&FetchRequest) -> Result<FetchResponse, Thrown> + Send + Sync + 'static,
) -> mock::FetchMockGuard {
    mock::install(move |request: FetchRequest| {
        let response = route(&request);
        async move { response }
    })
    .await
}

type PolicyFn = Arc<dyn Fn(&str) -> Result<FetchResponse, Thrown> + Send + Sync>;

async fn stub_github_copilot_login_fetch(
    models: impl Fn() -> FetchResponse + Send + Sync + 'static,
    policy: Option<PolicyFn>,
) -> mock::FetchMockGuard {
    install(move |request| {
        let url = request.url.as_str();
        if url.ends_with("/login/device/code") {
            return Ok(json_response(
                &json!({
                    "device_code": "device-code",
                    "user_code": "ABCD-EFGH",
                    "verification_uri": "https://github.com/login/device",
                    "interval": 1,
                    "expires_in": 900,
                }),
                200,
            ));
        }
        if url.ends_with("/login/oauth/access_token") {
            return Ok(json_response(
                &json!({ "access_token": "ghu_refresh_token" }),
                200,
            ));
        }
        if url.contains("/copilot_internal/v2/token") {
            return Ok(json_response(
                &json!({ "token": TEST_COPILOT_ACCESS_TOKEN, "expires_at": 9_999_999_999_i64 }),
                200,
            ));
        }
        if url == TEST_COPILOT_MODELS_URL {
            return Ok(models());
        }
        let prefix = format!("{TEST_COPILOT_MODELS_URL}/");
        if let Some(model_id) = url
            .strip_prefix(&prefix)
            .and_then(|rest| rest.strip_suffix("/policy"))
        {
            let Some(policy) = &policy else {
                return Err(js_error(format!("Unexpected policy request: {url}")));
            };
            return policy(model_id);
        }
        Err(js_error(format!("Unexpected fetch URL: {url}")))
    })
    .await
}

async fn login_github_copilot_for_test(events: Events) -> Result<OAuthCredential, Thrown> {
    let interaction = TestInteraction::provider(
        never_aborted_signal(),
        |prompt| {
            Box::pin(async move {
                match prompt.kind {
                    AuthPromptKind::Text { .. } => Ok(String::new()),
                    other => Err(js_error(format!("Unexpected prompt: {other:?}"))),
                }
            })
        },
        move |event| events.push(event),
    );
    github_copilot_oauth().login(interaction, None).await
}

async fn refresh_github_copilot_models_for_test(data: Value, proxy_host: &str) -> OAuthCredential {
    let access_token = format!("tid=test;exp=9999999999;proxy-ep={proxy_host};");
    let api_host = proxy_host
        .strip_prefix("proxy.")
        .map_or_else(|| proxy_host.to_owned(), |rest| format!("api.{rest}"));
    let models_url = format!("https://{api_host}/models");
    let token = access_token.clone();
    let _guard = install(move |request| {
        if request.url.contains("/copilot_internal/v2/token") {
            return Ok(json_response(
                &json!({ "token": token, "expires_at": 9_999_999_999_i64 }),
                200,
            ));
        }
        if request.url == models_url {
            assert_eq!(
                request.header_value("Authorization"),
                Some(format!("Bearer {token}").as_str())
            );
            return Ok(json_response(&json!({ "data": data }), 200));
        }
        Err(js_error(format!("Unexpected fetch URL: {}", request.url)))
    })
    .await;
    github_copilot_oauth()
        .refresh(
            OAuthCredential::new("ghu_refresh_token", "old-access-token", 0.0),
            never_aborted_signal(),
        )
        .await
        .expect("refresh")
}

fn available(credential: &OAuthCredential) -> Value {
    credential
        .extra
        .get("availableModelIds")
        .cloned()
        .unwrap_or(Value::Null)
}

#[tokio::test]
async fn filters_models_to_the_authenticated_account_picker_catalog() {
    let picker = require_model_id(0);
    let disabled = require_model_id(1);
    let hidden = require_model_id(2);
    let credentials = refresh_github_copilot_models_for_test(
        json!([
            { "id": picker, "model_picker_enabled": true, "capabilities": { "supports": { "tool_calls": true } } },
            { "id": disabled, "model_picker_enabled": true, "policy": { "state": "disabled" }, "capabilities": { "supports": { "tool_calls": true } } },
            { "id": hidden, "model_picker_enabled": false, "policy": { "state": "enabled" }, "capabilities": { "supports": { "tool_calls": true } } },
        ]),
        "proxy.individual.githubcopilot.com",
    )
    .await;
    assert_eq!(available(&credentials), json!([picker]));
}

#[tokio::test]
async fn falls_back_to_explicitly_enabled_policy_models_when_the_picker_catalog_is_empty() {
    let enabled = require_model_id(0);
    let credentials = refresh_github_copilot_models_for_test(
        json!([
            { "id": enabled, "model_picker_enabled": false, "policy": { "state": "enabled" }, "capabilities": { "supports": { "tool_calls": true } } },
            { "id": "policy-disabled-model", "model_picker_enabled": false, "policy": { "state": "disabled" }, "capabilities": { "supports": { "tool_calls": true } } },
            { "id": "unconfigured-model", "model_picker_enabled": false, "capabilities": { "supports": { "tool_calls": true } } },
            { "id": "tool-incapable-model", "model_picker_enabled": false, "policy": { "state": "enabled" }, "capabilities": { "supports": { "tool_calls": false } } },
        ]),
        "proxy.individual.githubcopilot.com",
    )
    .await;
    assert_eq!(available(&credentials), json!([enabled]));
}

#[tokio::test]
async fn does_not_fall_back_to_policy_models_for_non_individual_accounts() {
    let credentials = refresh_github_copilot_models_for_test(
        json!([
            { "id": "gpt-4.1", "model_picker_enabled": false, "policy": { "state": "enabled" }, "capabilities": { "supports": { "tool_calls": true } } },
        ]),
        "proxy.business.githubcopilot.com",
    )
    .await;
    assert_eq!(available(&credentials), json!([]));
}

#[tokio::test]
async fn does_not_retry_model_catalog_throttling_during_credential_refresh() {
    let catalog_request_count = Arc::new(Mutex::new(0));
    let count = Arc::clone(&catalog_request_count);
    let _guard = install(move |request| {
        if request.url.contains("/copilot_internal/v2/token") {
            return Ok(json_response(
                &json!({ "token": TEST_COPILOT_ACCESS_TOKEN, "expires_at": 9_999_999_999_i64 }),
                200,
            ));
        }
        if request.url == TEST_COPILOT_MODELS_URL {
            *count.lock().unwrap_or_else(PoisonError::into_inner) += 1;
            return Ok(with_header(
                json_response(&json!({ "error": "too many requests" }), 429),
                "Retry-After",
                "0",
            ));
        }
        Err(js_error(format!("Unexpected fetch URL: {}", request.url)))
    })
    .await;
    let error = github_copilot_oauth()
        .refresh(
            OAuthCredential::new("ghu_refresh_token", "old-access-token", 0.0),
            never_aborted_signal(),
        )
        .await
        .expect_err("throttled");
    assert!(error.to_string().contains("429"));
    assert_eq!(
        *catalog_request_count
            .lock()
            .unwrap_or_else(PoisonError::into_inner),
        1
    );
}

fn standard_route(
    verification_uri: &'static str,
) -> impl Fn(&FetchRequest) -> Result<FetchResponse, Thrown> + Send + Sync + 'static {
    move |request| {
        let url = request.url.as_str();
        if url.ends_with("/login/device/code") {
            return Ok(json_response(
                &json!({
                    "device_code": "device-code",
                    "user_code": "ABCD-EFGH",
                    "verification_uri": verification_uri,
                    "interval": 1,
                    "expires_in": 900,
                }),
                200,
            ));
        }
        if url.ends_with("/login/oauth/access_token") {
            return Ok(json_response(
                &json!({ "access_token": "ghu_refresh_token" }),
                200,
            ));
        }
        if url.contains("/copilot_internal/v2/token") {
            return Ok(json_response(
                &json!({ "token": TEST_COPILOT_ACCESS_TOKEN, "expires_at": 9_999_999_999_i64 }),
                200,
            ));
        }
        if url.ends_with("/models") {
            return Ok(json_response(&json!({ "data": [] }), 200));
        }
        if url.contains("/models/") && url.ends_with("/policy") {
            return Ok(empty_ok());
        }
        Err(js_error(format!("Unexpected fetch URL: {url}")))
    }
}

fn device_codes(events: &Events) -> Vec<AuthEvent> {
    events
        .all()
        .into_iter()
        .filter(|event| matches!(event, AuthEvent::DeviceCode { .. }))
        .collect()
}

#[tokio::test(start_paused = true)]
async fn reports_device_code_details_through_on_device_code() {
    let _guard = install(standard_route("https://github.com/login/device")).await;
    let events = Events::default();
    login_github_copilot_for_test(events.clone())
        .await
        .expect("login");
    assert_eq!(
        device_codes(&events),
        vec![AuthEvent::DeviceCode {
            user_code: "ABCD-EFGH".to_owned(),
            verification_uri: "https://github.com/login/device".to_owned(),
            interval_seconds: Some(1.0),
            expires_in_seconds: Some(900.0),
        }]
    );
}

fn catalog_entry(id: &str, picker: bool, state: Option<&str>, tool_calls: Option<bool>) -> Value {
    let mut entry = json!({ "id": id, "model_picker_enabled": picker });
    if let Some(state) = state {
        entry["policy"] = json!({ "state": state });
    }
    if let Some(tool_calls) = tool_calls {
        entry["capabilities"] = json!({ "supports": { "tool_calls": tool_calls } });
    }
    entry
}

#[tokio::test(start_paused = true)]
async fn updates_only_known_tool_capable_unconfigured_account_model_policies() {
    let configured = require_model_id(0);
    let unconfigured = require_model_id(1);
    let tool_incapable = require_model_id(2);
    let catalog_request_count = Arc::new(Mutex::new(0));
    let policy_model_ids = Arc::new(Mutex::new(Vec::new()));
    let count = Arc::clone(&catalog_request_count);
    let policies = Arc::clone(&policy_model_ids);
    let data = json!([
        catalog_entry(&configured, true, Some("enabled"), Some(true)),
        catalog_entry(&unconfigured, true, Some("unconfigured"), Some(true)),
        catalog_entry("remote-only-model", true, Some("unconfigured"), Some(true)),
        catalog_entry(&tool_incapable, true, Some("unconfigured"), Some(false)),
    ]);
    let _guard = stub_github_copilot_login_fetch(
        move || {
            *count.lock().unwrap_or_else(PoisonError::into_inner) += 1;
            json_response(&json!({ "data": data }), 200)
        },
        Some(Arc::new(move |model_id: &str| {
            policies
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(model_id.to_owned());
            Ok(empty_ok())
        })),
    )
    .await;
    login_github_copilot_for_test(Events::default())
        .await
        .expect("login");
    assert_eq!(
        *catalog_request_count
            .lock()
            .unwrap_or_else(PoisonError::into_inner),
        1
    );
    assert_eq!(
        *policy_model_ids
            .lock()
            .unwrap_or_else(PoisonError::into_inner),
        vec![unconfigured]
    );
}

#[tokio::test(start_paused = true)]
async fn retries_a_throttled_policy_update_after_retry_after() {
    let model_id = require_model_id(0);
    let start = Instant::now();
    let policy_times = Arc::new(Mutex::new(Vec::new()));
    let times = Arc::clone(&policy_times);
    let data = json!([catalog_entry(&model_id, true, Some("unconfigured"), None)]);
    let _guard = stub_github_copilot_login_fetch(
        move || json_response(&json!({ "data": data }), 200),
        Some(Arc::new(move |_: &str| {
            let mut times = times.lock().unwrap_or_else(PoisonError::into_inner);
            times.push(start.elapsed().as_millis());
            Ok(if times.len() == 1 {
                with_header(
                    json_response(&json!({ "error": "too many requests" }), 429),
                    "Retry-After",
                    "1",
                )
            } else {
                empty_ok()
            })
        })),
    )
    .await;
    login_github_copilot_for_test(Events::default())
        .await
        .expect("login");
    let times = policy_times
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(times.len(), 2);
    assert_eq!(times[1] - times[0], 1000);
}

#[tokio::test(start_paused = true)]
async fn continues_policy_updates_after_a_transport_failure() {
    let model_ids = vec![require_model_id(0), require_model_id(1)];
    let policy_model_ids = Arc::new(Mutex::new(Vec::new()));
    let policies = Arc::clone(&policy_model_ids);
    let data = Value::Array(
        model_ids
            .iter()
            .map(|id| catalog_entry(id, true, Some("unconfigured"), None))
            .collect(),
    );
    let _guard = stub_github_copilot_login_fetch(
        move || json_response(&json!({ "data": data }), 200),
        Some(Arc::new(move |model_id: &str| {
            let mut policies = policies.lock().unwrap_or_else(PoisonError::into_inner);
            policies.push(model_id.to_owned());
            if policies.len() == 1 {
                return Err(js_error("fetch failed"));
            }
            Ok(empty_ok())
        })),
    )
    .await;
    login_github_copilot_for_test(Events::default())
        .await
        .expect("login");
    assert_eq!(
        *policy_model_ids
            .lock()
            .unwrap_or_else(PoisonError::into_inner),
        model_ids
    );
}

#[tokio::test(start_paused = true)]
async fn stops_policy_updates_and_keeps_authentication_when_the_retry_delay_exceeds_the_login_budget(
) {
    let first = require_model_id(0);
    let second = require_model_id(1);
    let policy_model_ids = Arc::new(Mutex::new(Vec::new()));
    let policies = Arc::clone(&policy_model_ids);
    let data = json!([
        catalog_entry(&first, true, Some("unconfigured"), None),
        catalog_entry(&second, true, Some("unconfigured"), None),
    ]);
    let _guard = stub_github_copilot_login_fetch(
        move || json_response(&json!({ "data": data }), 200),
        Some(Arc::new(move |model_id: &str| {
            policies
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(model_id.to_owned());
            Ok(with_header(
                json_response(&json!({ "error": "too many requests" }), 429),
                "Retry-After",
                "5",
            ))
        })),
    )
    .await;
    let credential = login_github_copilot_for_test(Events::default())
        .await
        .expect("login");
    assert_eq!(credential.access, TEST_COPILOT_ACCESS_TOKEN);
    assert_eq!(
        *policy_model_ids
            .lock()
            .unwrap_or_else(PoisonError::into_inner),
        vec![first]
    );
}

#[tokio::test]
async fn rejects_a_non_http_s_verification_uri_before_it_reaches_on_device_code() {
    // A malicious enterprise OAuth server could return a verification_uri that
    // the browser launcher would otherwise hand to the OS.
    let _guard = install(|request| {
        if request.url.ends_with("/login/device/code") {
            return Ok(json_response(
                &json!({
                    "device_code": "device-code",
                    "user_code": "ABCD-EFGH",
                    "verification_uri": "$(id>/tmp/pwned)",
                    "interval": 1,
                    "expires_in": 900,
                }),
                200,
            ));
        }
        Err(js_error(format!("Unexpected fetch URL: {}", request.url)))
    })
    .await;
    let events = Events::default();
    let error = login_github_copilot_for_test(events.clone())
        .await
        .expect_err("untrusted");
    assert!(error.to_string().contains("Untrusted verification_uri"));
    assert!(device_codes(&events).is_empty());
}

#[tokio::test(start_paused = true)]
async fn normalizes_verification_uri_before_it_reaches_on_device_code() {
    const RAW: &str = "https://github.com/login/\x1b]8;;evil";
    let normalized = url::Url::parse(RAW).expect("url").to_string();
    assert_ne!(normalized, RAW);
    let _guard = install(standard_route(RAW)).await;
    let events = Events::default();
    login_github_copilot_for_test(events.clone())
        .await
        .expect("login");
    assert_eq!(
        device_codes(&events),
        vec![AuthEvent::DeviceCode {
            user_code: "ABCD-EFGH".to_owned(),
            verification_uri: normalized,
            interval_seconds: Some(1.0),
            expires_in_seconds: Some(900.0),
        }]
    );
}

#[tokio::test(start_paused = true)]
async fn waits_before_polling_and_increases_the_interval_after_slow_down() {
    let start = Instant::now();
    let poll_times = Arc::new(Mutex::new(Vec::new()));
    let responses = Arc::new(Mutex::new(vec![
        json_response(
            &json!({ "error": "authorization_pending", "error_description": "pending" }),
            200,
        ),
        json_response(
            &json!({ "error": "slow_down", "error_description": "slow down", "interval": 7 }),
            200,
        ),
        json_response(&json!({ "access_token": "ghu_refresh_token" }), 200),
    ]));
    let times = Arc::clone(&poll_times);
    let fallback = standard_route("https://github.com/login/device");
    let _guard = install(move |request| {
        let url = request.url.as_str();
        if url.ends_with("/login/device/code") {
            assert_eq!(request.method, "POST");
            assert_eq!(request.header_value("Accept"), Some("application/json"));
            assert_eq!(
                request.header_value("Content-Type"),
                Some("application/x-www-form-urlencoded")
            );
            let body = request.body.clone().unwrap_or_default();
            assert!(body.contains("client_id="));
            assert!(body.contains("scope=read%3Auser"));
            return Ok(json_response(
                &json!({
                    "device_code": "device-code",
                    "user_code": "ABCD-EFGH",
                    "verification_uri": "https://github.com/login/device",
                    "interval": 5,
                    "expires_in": 900,
                }),
                200,
            ));
        }
        if url.ends_with("/login/oauth/access_token") {
            times
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(start.elapsed().as_millis());
            assert_eq!(request.method, "POST");
            let body = request.body.clone().unwrap_or_default();
            assert!(body.contains("client_id="));
            assert!(body.contains("device_code=device-code"));
            assert!(
                body.contains("grant_type=urn%3Aietf%3Aparams%3Aoauth%3Agrant-type%3Adevice_code")
            );
            let mut responses = responses.lock().unwrap_or_else(PoisonError::into_inner);
            if responses.is_empty() {
                return Err(js_error("Unexpected extra access token poll"));
            }
            return Ok(responses.remove(0));
        }
        fallback(request)
    })
    .await;
    login_github_copilot_for_test(Events::default())
        .await
        .expect("login");
    // slow_down carried a server-provided interval of 7 seconds.
    assert_eq!(
        *poll_times.lock().unwrap_or_else(PoisonError::into_inner),
        vec![5000, 10_000, 17_000]
    );
}

#[tokio::test(start_paused = true)]
async fn times_out_after_repeated_slow_down_responses() {
    let start = Instant::now();
    let poll_times = Arc::new(Mutex::new(Vec::new()));
    let responses = Arc::new(Mutex::new(vec![
        json_response(
            &json!({ "error": "slow_down", "error_description": "slow down" }),
            200,
        ),
        json_response(
            &json!({ "error": "slow_down", "error_description": "still too fast" }),
            200,
        ),
        json_response(
            &json!({ "error": "authorization_pending", "error_description": "pending" }),
            200,
        ),
    ]));
    let times = Arc::clone(&poll_times);
    let _guard = install(move |request| {
        let url = request.url.as_str();
        if url.ends_with("/login/device/code") {
            return Ok(json_response(
                &json!({
                    "device_code": "device-code",
                    "user_code": "ABCD-EFGH",
                    "verification_uri": "https://github.com/login/device",
                    "interval": 5,
                    "expires_in": 25,
                }),
                200,
            ));
        }
        if url.ends_with("/login/oauth/access_token") {
            times
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(start.elapsed().as_millis());
            let mut responses = responses.lock().unwrap_or_else(PoisonError::into_inner);
            if responses.is_empty() {
                return Err(js_error("Unexpected extra access token poll"));
            }
            return Ok(responses.remove(0));
        }
        Err(js_error(format!("Unexpected fetch URL: {url}")))
    })
    .await;
    let error = login_github_copilot_for_test(Events::default())
        .await
        .expect_err("times out");
    assert!(error
        .to_string()
        .contains("Device flow timed out after one or more slow_down responses"));
    assert_eq!(
        *poll_times.lock().unwrap_or_else(PoisonError::into_inner),
        vec![5000, 15_000]
    );
}

// From test/oauth-auth.test.ts.

#[tokio::test]
async fn github_copilot_to_auth_derives_base_url_from_the_token_proxy_endpoint() {
    let access = "tid=abc;exp=123;proxy-ep=proxy.enterprise.example;rest";
    let auth = github_copilot_oauth()
        .to_auth(&OAuthCredential::new("r", access, 0.0))
        .await
        .expect("to_auth");
    assert_eq!(
        auth,
        ModelAuth {
            api_key: Some(access.to_owned()),
            headers: None,
            base_url: Some("https://api.enterprise.example".to_owned()),
        }
    );
}

#[tokio::test]
async fn github_copilot_to_auth_falls_back_to_the_enterprise_domain_then_the_individual_endpoint() {
    let oauth = github_copilot_oauth();
    let enterprise = oauth
        .to_auth(
            &OAuthCredential::new("r", "no-proxy-ep", 0.0)
                .with_extra("enterpriseUrl", json!("https://company.ghe.com")),
        )
        .await
        .expect("to_auth");
    assert_eq!(
        enterprise.base_url.as_deref(),
        Some("https://copilot-api.company.ghe.com")
    );
    let individual = oauth
        .to_auth(&OAuthCredential::new("r", "no-proxy-ep", 0.0))
        .await
        .expect("to_auth");
    assert_eq!(
        individual.base_url.as_deref(),
        Some("https://api.individual.githubcopilot.com")
    );
}

#[tokio::test]
async fn github_copilot_refresh_preserves_the_enterprise_domain() {
    let fetched_urls = Arc::new(Mutex::new(Vec::new()));
    let recorded = Arc::clone(&fetched_urls);
    let _guard = install(move |request| {
        recorded
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(request.url.clone());
        if request.url.ends_with("/models") {
            return Ok(json_response(&json!({ "data": [] }), 200));
        }
        Ok(json_response(
            &json!({ "token": "new-token", "expires_at": 9_999_999_999_i64 }),
            200,
        ))
    })
    .await;
    let refreshed = github_copilot_oauth()
        .refresh(
            OAuthCredential::new("gh-token", "old", 0.0)
                .with_extra("enterpriseUrl", json!("company.ghe.com")),
            never_aborted_signal(),
        )
        .await
        .expect("refresh");
    assert_eq!(refreshed.access, "new-token");
    assert_eq!(
        refreshed.extra_str("enterpriseUrl"),
        Some("company.ghe.com")
    );
    assert!(
        fetched_urls.lock().unwrap_or_else(PoisonError::into_inner)[0]
            .contains("api.company.ghe.com")
    );
}

#[test]
fn parse_float_matches_js() {
    assert!((js_parse_float("1") - 1.0).abs() < f64::EPSILON);
    assert!((js_parse_float(" 2.5s") - 2.5).abs() < f64::EPSILON);
    assert!(js_parse_float("Wed, 21 Oct 2015 07:28:00 GMT").is_nan());
}
