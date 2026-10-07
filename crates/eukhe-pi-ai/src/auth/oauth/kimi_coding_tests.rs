//! Port of `test/kimi-coding-oauth.test.ts`. Fake timers become tokio paused
//! time; the wall-clock `expires` is checked against a window.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::pi_ai::ProviderHeaders;
use serde_json::{json, Value};
use tokio::time::Instant;

use super::kimi_coding_oauth;
use crate::auth::errors::{date_now, js_error};
use crate::auth::oauth::http::{mock, FetchRequest, FetchResponse};
use crate::auth::oauth::test_support::{never_aborted_signal, Events, TestInteraction};
use crate::auth::types::{AuthEvent, ModelAuth, OAuthCredential, ProviderAuthInteraction};
use crate::utils::diagnostics::Thrown;

const CLIENT_ID: &str = "17e5f671-d194-4dfb-9706-5516cb48c098";
const DEVICE_URL: &str = "https://auth.kimi.com/api/oauth/device_authorization";
const TOKEN_URL: &str = "https://auth.kimi.com/api/oauth/token";

fn device_authorization_response(overrides: &Value) -> FetchResponse {
    let mut body = json!({
        "user_code": "ABCD-1234",
        "device_code": "device-code-123",
        "verification_uri": "https://www.kimi.com/code",
        "verification_uri_complete": "https://www.kimi.com/code?user_code=ABCD-1234",
        "interval": 5,
        "expires_in": 600,
    });
    for (key, value) in overrides.as_object().expect("overrides") {
        body[key] = value.clone();
    }
    FetchResponse::json_response(&body, 200)
}

fn form(request: &FetchRequest, name: &str) -> Option<String> {
    request
        .form_fields()
        .into_iter()
        .find(|(key, _)| key == name)
        .map(|(_, value)| value)
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

fn create_interaction(events: Events) -> ProviderAuthInteraction {
    TestInteraction::provider(
        never_aborted_signal(),
        |_| Box::pin(async { Err(js_error("Kimi Code login should not prompt")) }),
        move |event| events.push(event),
    )
}

#[tokio::test(start_paused = true)]
async fn logs_in_with_the_device_authorization_flow() {
    let start = Instant::now();
    let poll_times = Arc::new(Mutex::new(Vec::new()));
    let poll_responses = Arc::new(Mutex::new(vec![
        FetchResponse::json_response(&json!({ "error": "authorization_pending" }), 400),
        FetchResponse::json_response(
            &json!({ "access_token": "access-token", "refresh_token": "refresh-token", "expires_in": 3600 }),
            200,
        ),
    ]));
    let times = Arc::clone(&poll_times);
    let _guard = install(move |request| match request.url.as_str() {
        DEVICE_URL => {
            assert_eq!(request.method, "POST");
            assert_eq!(
                request.header_value("Content-Type"),
                Some("application/x-www-form-urlencoded")
            );
            assert_eq!(request.header_value("Accept"), Some("application/json"));
            assert_eq!(form(request, "client_id").as_deref(), Some(CLIENT_ID));
            Ok(device_authorization_response(&json!({})))
        }
        TOKEN_URL => {
            times
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(start.elapsed().as_millis());
            assert_eq!(
                form(request, "grant_type").as_deref(),
                Some("urn:ietf:params:oauth:grant-type:device_code")
            );
            assert_eq!(form(request, "client_id").as_deref(), Some(CLIENT_ID));
            assert_eq!(
                form(request, "device_code").as_deref(),
                Some("device-code-123")
            );
            let mut responses = poll_responses
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            if responses.is_empty() {
                return Err(js_error("Unexpected extra token poll"));
            }
            Ok(responses.remove(0))
        }
        url => Err(js_error(format!("Unexpected fetch URL: {url}"))),
    })
    .await;

    let events = Events::default();
    let before = date_now();
    let credential = kimi_coding_oauth()
        .login(create_interaction(events.clone()), None)
        .await
        .expect("login");
    let after = date_now();
    assert_eq!(
        events.all(),
        vec![AuthEvent::DeviceCode {
            user_code: "ABCD-1234".to_owned(),
            verification_uri: "https://www.kimi.com/code?user_code=ABCD-1234".to_owned(),
            interval_seconds: Some(5.0),
            expires_in_seconds: Some(600.0),
        }]
    );
    // waitBeforeFirstPoll: first poll happens after the 5s interval.
    assert_eq!(
        *poll_times.lock().unwrap_or_else(PoisonError::into_inner),
        vec![5000, 10_000]
    );
    assert_eq!(credential.access, "access-token");
    assert_eq!(credential.refresh, "refresh-token");
    assert!(credential.extra.is_empty());
    assert!(
        credential.expires >= before + 3_600_000.0 && credential.expires <= after + 3_600_000.0
    );
}

async fn login_with_poll_error(error: &'static str) -> Thrown {
    let _guard = install(move |request| match request.url.as_str() {
        DEVICE_URL => Ok(device_authorization_response(&json!({}))),
        TOKEN_URL => Ok(FetchResponse::json_response(
            &json!({ "error": error }),
            400,
        )),
        url => Err(js_error(format!("Unexpected fetch URL: {url}"))),
    })
    .await;
    kimi_coding_oauth()
        .login(create_interaction(Events::default()), None)
        .await
        .expect_err("fails")
}

#[tokio::test(start_paused = true)]
async fn fails_when_the_device_code_expires() {
    assert!(login_with_poll_error("expired_token")
        .await
        .to_string()
        .contains("expired"));
}

#[tokio::test(start_paused = true)]
async fn fails_when_the_user_denies_the_login() {
    assert!(login_with_poll_error("access_denied")
        .await
        .to_string()
        .contains("denied"));
}

#[tokio::test(start_paused = true)]
async fn honors_the_kimi_code_oauth_host_override() {
    let urls = Arc::new(Mutex::new(Vec::new()));
    let recorded = Arc::clone(&urls);
    let guard = install(move |request| {
        recorded
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(request.url.clone());
        match request.url.as_str() {
            "https://auth.example.com/api/oauth/device_authorization" => {
                Ok(device_authorization_response(&json!({ "interval": 1 })))
            }
            "https://auth.example.com/api/oauth/token" => Ok(FetchResponse::json_response(
                &json!({ "access_token": "a", "refresh_token": "r", "expires_in": 60 }),
                200,
            )),
            url => Err(js_error(format!("Unexpected fetch URL: {url}"))),
        }
    })
    .await;
    let previous = std::env::var("KIMI_CODE_OAUTH_HOST").ok();
    std::env::set_var("KIMI_CODE_OAUTH_HOST", "https://auth.example.com/");
    let result = kimi_coding_oauth()
        .login(create_interaction(Events::default()), None)
        .await;
    match previous {
        Some(value) => std::env::set_var("KIMI_CODE_OAUTH_HOST", value),
        None => std::env::remove_var("KIMI_CODE_OAUTH_HOST"),
    }
    drop(guard);
    let credential = result.expect("login");
    assert_eq!(credential.access, "a");
    assert_eq!(credential.refresh, "r");
    assert_eq!(
        *urls.lock().unwrap_or_else(PoisonError::into_inner),
        vec![
            "https://auth.example.com/api/oauth/device_authorization".to_owned(),
            "https://auth.example.com/api/oauth/token".to_owned(),
        ]
    );
}

#[tokio::test]
async fn refreshes_tokens_and_returns_a_bearer_header_for_requests() {
    let _guard = install(|request| {
        assert_eq!(request.url, TOKEN_URL);
        assert_eq!(form(request, "grant_type").as_deref(), Some("refresh_token"));
        assert_eq!(form(request, "refresh_token").as_deref(), Some("old-refresh"));
        assert_eq!(form(request, "client_id").as_deref(), Some(CLIENT_ID));
        Ok(FetchResponse::json_response(
            &json!({ "access_token": "new-access", "refresh_token": "new-refresh", "expires_in": 3600 }),
            200,
        ))
    })
    .await;

    let before = date_now();
    let oauth = kimi_coding_oauth();
    let credential = oauth
        .refresh(
            OAuthCredential::new("old-refresh", "old-access", before),
            never_aborted_signal(),
        )
        .await
        .expect("refresh");
    assert_eq!(credential.access, "new-access");
    assert_eq!(credential.refresh, "new-refresh");
    assert!(credential.extra.is_empty());
    assert!(credential.expires >= before + 3600.0 * 1000.0);

    let mut headers = ProviderHeaders::new();
    headers.insert(
        "Authorization".to_owned(),
        Some("Bearer new-access".to_owned()),
    );
    assert_eq!(
        oauth.to_auth(&credential).await.expect("to_auth"),
        ModelAuth {
            headers: Some(headers),
            ..ModelAuth::default()
        }
    );
}

#[tokio::test(start_paused = true)]
async fn retries_refresh_on_429_and_fails_unauthorized_on_invalid_grant() {
    // 429 once, then success.
    let calls = Arc::new(Mutex::new(0));
    let count = Arc::clone(&calls);
    let guard = install(move |_| {
        let mut calls = count.lock().unwrap_or_else(PoisonError::into_inner);
        *calls += 1;
        Ok(if *calls == 1 {
            FetchResponse::json_response(&json!({ "error": "temporarily_unavailable" }), 429)
        } else {
            FetchResponse::json_response(
                &json!({ "access_token": "a", "refresh_token": "r", "expires_in": 60 }),
                200,
            )
        })
    })
    .await;
    let oauth = kimi_coding_oauth();
    let credential = oauth
        .refresh(
            OAuthCredential::new("old", "old", 0.0),
            never_aborted_signal(),
        )
        .await
        .expect("refresh");
    assert_eq!(credential.access, "a");
    assert_eq!(*calls.lock().unwrap_or_else(PoisonError::into_inner), 2);
    drop(guard);

    // invalid_grant is not retried.
    let _guard = install(|_| {
        Ok(FetchResponse::json_response(
            &json!({ "error": "invalid_grant" }),
            400,
        ))
    })
    .await;
    let error = oauth
        .refresh(
            OAuthCredential::new("old", "old", 0.0),
            never_aborted_signal(),
        )
        .await
        .expect_err("unauthorized");
    assert!(error.to_string().contains("unauthorized"));
}
