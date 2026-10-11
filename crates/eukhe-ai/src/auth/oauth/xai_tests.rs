//! Port of `test/xai-oauth.test.ts` (plus the xAI case of
//! `test/oauth-auth.test.ts`). Fake timers become tokio paused time; the
//! wall-clock `expires` is checked against a window.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{AbortController, AbortSignal};
use serde_json::{json, Value};
use tokio::time::Instant;

use super::xai_oauth;
use crate::auth::errors::{date_now, js_error};
use crate::auth::oauth::http::{mock, FetchRequest, FetchResponse};
use crate::auth::oauth::test_support::{never_aborted_signal, Events, TestInteraction};
use crate::auth::types::{AuthEvent, ModelAuth, OAuthCredential};
use crate::utils::diagnostics::Thrown;

const DEVICE_CODE_URL: &str = "https://auth.x.ai/oauth2/device/code";
const TOKEN_URL: &str = "https://auth.x.ai/oauth2/token";
const CLIENT_ID: &str = "b1a00492-073a-47ea-816f-4c329264a828";

fn with_overrides(mut base: Value, overrides: &Value) -> Value {
    let object = base.as_object_mut().expect("object");
    for (key, value) in overrides.as_object().expect("overrides").clone() {
        // `undefined` overrides drop the key, as JSON.stringify does.
        if value.is_null() {
            object.shift_remove(&key);
        } else {
            object.insert(key, value);
        }
    }
    base
}

fn device_code_response(overrides: &Value) -> Value {
    with_overrides(
        json!({
            "device_code": "device-code",
            "user_code": "ABCD-1234",
            "verification_uri": "https://accounts.x.ai/oauth2/device",
            "expires_in": 900,
            "interval": 5,
        }),
        overrides,
    )
}

fn token_response(overrides: &Value) -> Value {
    with_overrides(
        json!({
            "access_token": "access-token",
            "refresh_token": "refresh-token",
            "expires_in": 21_600,
            "token_type": "Bearer",
        }),
        overrides,
    )
}

fn json_response(body: &Value, status: u16) -> FetchResponse {
    FetchResponse::json_response(body, status)
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

async fn login_xai_for_test(
    signal: AbortSignal,
    events: Events,
) -> Result<OAuthCredential, Thrown> {
    let interaction = TestInteraction::provider(
        signal,
        |_| Box::pin(async { Err(js_error("Unexpected prompt")) }),
        move |event| events.push(event),
    );
    xai_oauth().login(interaction, None).await
}

async fn refresh_xai_for_test(refresh_token: &str) -> Result<OAuthCredential, Thrown> {
    xai_oauth()
        .refresh(
            OAuthCredential::new(refresh_token, "old-access", 0.0),
            never_aborted_signal(),
        )
        .await
}

fn device_codes(events: &Events) -> Vec<AuthEvent> {
    events
        .all()
        .into_iter()
        .filter(|event| matches!(event, AuthEvent::DeviceCode { .. }))
        .collect()
}

#[tokio::test(start_paused = true)]
async fn uses_the_device_grant_delays_polling_and_handles_pending_and_slow_down() {
    let start = Instant::now();
    let poll_times = Arc::new(Mutex::new(Vec::new()));
    let replies = Arc::new(Mutex::new(vec![
        json_response(&json!({ "error": "authorization_pending" }), 400),
        json_response(&json!({ "error": "slow_down", "interval": 10 }), 400),
        json_response(&token_response(&json!({})), 200),
    ]));
    let times = Arc::clone(&poll_times);
    let _guard = install(move |request| match request.url.as_str() {
        DEVICE_CODE_URL => {
            assert_eq!(form(request, "client_id").as_deref(), Some(CLIENT_ID));
            assert_eq!(
                form(request, "scope").as_deref(),
                Some("openid profile email offline_access grok-cli:access api:access")
            );
            assert_eq!(form(request, "referrer").as_deref(), Some("pi"));
            Ok(json_response(&device_code_response(&json!({})), 200))
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
            assert_eq!(form(request, "device_code").as_deref(), Some("device-code"));
            let mut replies = replies.lock().unwrap_or_else(PoisonError::into_inner);
            if replies.is_empty() {
                return Err(js_error("Unexpected token poll"));
            }
            Ok(replies.remove(0))
        }
        url => Err(js_error(format!("Unexpected request: {url}"))),
    })
    .await;

    let events = Events::default();
    let before = date_now();
    let credentials = login_xai_for_test(never_aborted_signal(), events.clone())
        .await
        .expect("login");
    let after = date_now();
    assert_eq!(
        device_codes(&events),
        vec![AuthEvent::DeviceCode {
            user_code: "ABCD-1234".to_owned(),
            verification_uri: "https://accounts.x.ai/oauth2/device".to_owned(),
            interval_seconds: Some(5.0),
            expires_in_seconds: Some(900.0),
        }]
    );
    // slow_down raised the interval to 10 seconds
    assert_eq!(
        *poll_times.lock().unwrap_or_else(PoisonError::into_inner),
        vec![5000, 10_000, 20_000]
    );
    assert_eq!(credentials.access, "access-token");
    assert_eq!(credentials.refresh, "refresh-token");
    assert!(credentials.extra.is_empty());
    assert!(credentials.expires >= before + 21_600_000.0 - 300_000.0);
    assert!(credentials.expires <= after + 21_600_000.0 - 300_000.0);
}

#[tokio::test(start_paused = true)]
async fn falls_back_to_the_default_poll_interval_when_the_response_reports_interval_0() {
    let start = Instant::now();
    let poll_times = Arc::new(Mutex::new(Vec::new()));
    let times = Arc::clone(&poll_times);
    let _guard = install(move |request| {
        if request.url == DEVICE_CODE_URL {
            return Ok(json_response(
                &device_code_response(&json!({ "interval": 0 })),
                200,
            ));
        }
        times
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(start.elapsed().as_millis());
        Ok(json_response(&token_response(&json!({})), 200))
    })
    .await;
    login_xai_for_test(never_aborted_signal(), Events::default())
        .await
        .expect("login");
    // RFC 8628 default interval is 5 seconds when the server does not require a wait.
    assert_eq!(
        *poll_times.lock().unwrap_or_else(PoisonError::into_inner),
        vec![5000]
    );
}

#[tokio::test(start_paused = true)]
async fn prefers_verification_uri_complete_when_the_server_provides_it() {
    let _guard = install(|request| {
        if request.url == DEVICE_CODE_URL {
            return Ok(json_response(
                &device_code_response(&json!({
                    "verification_uri_complete": "https://accounts.x.ai/oauth2/device?user_code=ABCD-1234",
                })),
                200,
            ));
        }
        Ok(json_response(&token_response(&json!({})), 200))
    })
    .await;
    let events = Events::default();
    login_xai_for_test(never_aborted_signal(), events.clone())
        .await
        .expect("login");
    assert_eq!(
        device_codes(&events),
        vec![AuthEvent::DeviceCode {
            user_code: "ABCD-1234".to_owned(),
            verification_uri: "https://accounts.x.ai/oauth2/device?user_code=ABCD-1234".to_owned(),
            interval_seconds: Some(5.0),
            expires_in_seconds: Some(900.0),
        }]
    );
}

#[tokio::test]
async fn rejects_a_non_https_verification_uri_complete() {
    let _guard = install(|_| {
        Ok(json_response(
            &device_code_response(&json!({
                "verification_uri_complete": "http://accounts.x.ai/oauth2/device?user_code=ABCD-1234",
            })),
            200,
        ))
    })
    .await;
    let error = login_xai_for_test(never_aborted_signal(), Events::default())
        .await
        .expect_err("rejects");
    assert!(error.to_string().contains("Untrusted verification URI"));
}

#[tokio::test]
async fn rejects_a_non_https_verification_uri() {
    for verification_uri in [
        "http://accounts.x.ai/oauth2/device",
        "file:///etc/passwd",
        "not a url",
    ] {
        let _guard = install(move |_| {
            Ok(json_response(
                &device_code_response(&json!({ "verification_uri": verification_uri })),
                200,
            ))
        })
        .await;
        let error = login_xai_for_test(never_aborted_signal(), Events::default())
            .await
            .expect_err("rejects");
        assert!(
            error.to_string().contains("Untrusted verification URI"),
            "{verification_uri}: {error}"
        );
    }
}

#[tokio::test(start_paused = true)]
async fn fails_when_device_authorization_is_denied() {
    for denial in ["access_denied", "authorization_denied"] {
        let request_count = Arc::new(Mutex::new(0));
        let count = Arc::clone(&request_count);
        let _guard = install(move |_| {
            let mut count = count.lock().unwrap_or_else(PoisonError::into_inner);
            *count += 1;
            Ok(if *count == 1 {
                json_response(&device_code_response(&json!({ "interval": 1 })), 200)
            } else {
                json_response(&json!({ "error": denial }), 400)
            })
        })
        .await;
        let error = login_xai_for_test(never_aborted_signal(), Events::default())
            .await
            .expect_err("denied");
        assert!(
            error
                .to_string()
                .contains("xAI device authorization was denied"),
            "{denial}"
        );
    }
}

#[tokio::test(start_paused = true)]
async fn cancels_while_waiting_for_the_first_token_poll() {
    let fetch_count = Arc::new(Mutex::new(0));
    let count = Arc::clone(&fetch_count);
    let _guard = install(move |_| {
        *count.lock().unwrap_or_else(PoisonError::into_inner) += 1;
        Ok(json_response(&device_code_response(&json!({})), 200))
    })
    .await;
    let controller = AbortController::new();
    let abort = controller.clone();
    let interaction = TestInteraction::provider(
        controller.signal(),
        |_| Box::pin(async { Err(js_error("Unexpected prompt")) }),
        move |event| {
            if matches!(event, AuthEvent::DeviceCode { .. }) {
                abort.abort(None);
            }
        },
    );
    let error = xai_oauth()
        .login(interaction, None)
        .await
        .expect_err("cancelled");
    assert!(error.to_string().contains("Login cancelled"));
    assert_eq!(
        *fetch_count.lock().unwrap_or_else(PoisonError::into_inner),
        1
    );
}

#[tokio::test]
async fn refreshes_tokens_and_preserves_an_unrotated_refresh_token() {
    let request_count = Arc::new(Mutex::new(0));
    let count = Arc::clone(&request_count);
    let _guard = install(move |request| {
        assert_eq!(request.url, TOKEN_URL);
        assert_eq!(
            form(request, "grant_type").as_deref(),
            Some("refresh_token")
        );
        assert_eq!(form(request, "client_id").as_deref(), Some(CLIENT_ID));
        let mut count = count.lock().unwrap_or_else(PoisonError::into_inner);
        *count += 1;
        if *count == 1 {
            assert_eq!(
                form(request, "refresh_token").as_deref(),
                Some("old-refresh")
            );
            return Ok(json_response(
                &token_response(
                    &json!({ "access_token": "new-access", "refresh_token": "new-refresh" }),
                ),
                200,
            ));
        }
        assert_eq!(
            form(request, "refresh_token").as_deref(),
            Some("keep-refresh")
        );
        Ok(json_response(
            &token_response(&json!({ "access_token": "newer-access", "refresh_token": null })),
            200,
        ))
    })
    .await;

    let rotated = refresh_xai_for_test("old-refresh").await.expect("rotated");
    let preserved = refresh_xai_for_test("keep-refresh")
        .await
        .expect("preserved");
    assert_eq!(rotated.refresh, "new-refresh");
    assert_eq!(rotated.access, "new-access");
    assert_eq!(preserved.refresh, "keep-refresh");
    assert_eq!(preserved.access, "newer-access");
    let oauth = xai_oauth();
    assert_eq!(oauth.name(), "xAI (Grok/X subscription)");
    assert_eq!(
        oauth.to_auth(&preserved).await.expect("to_auth"),
        ModelAuth {
            api_key: Some("newer-access".to_owned()),
            ..ModelAuth::default()
        }
    );
}

#[tokio::test]
async fn assumes_a_one_hour_lifetime_when_expires_in_is_missing() {
    let _guard = install(|_| {
        Ok(json_response(
            &token_response(&json!({ "expires_in": null })),
            200,
        ))
    })
    .await;
    let before = date_now();
    let credentials = refresh_xai_for_test("old-refresh").await.expect("refresh");
    let after = date_now();
    assert!(credentials.expires >= before + 3_600_000.0 - 300_000.0);
    assert!(credentials.expires <= after + 3_600_000.0 - 300_000.0);
}

#[tokio::test]
async fn rejects_token_responses_with_missing_fields() {
    let _guard = install(|_| {
        Ok(json_response(
            &token_response(&json!({ "access_token": null })),
            200,
        ))
    })
    .await;
    let error = refresh_xai_for_test("old-refresh")
        .await
        .expect_err("rejects");
    assert!(error
        .to_string()
        .contains("Invalid xAI OAuth response field: access_token"));
}

#[tokio::test]
async fn surfaces_the_upstream_error_code_and_description_on_refresh_failure() {
    let _guard = install(|_| {
        Ok(json_response(
            &json!({ "error": "invalid_grant", "error_description": "refresh token revoked" }),
            400,
        ))
    })
    .await;
    let error = refresh_xai_for_test("old-refresh")
        .await
        .expect_err("rejects");
    assert!(error.to_string().contains(
        "xAI OAuth token refresh failed (HTTP 400): invalid_grant: refresh token revoked"
    ));
}
