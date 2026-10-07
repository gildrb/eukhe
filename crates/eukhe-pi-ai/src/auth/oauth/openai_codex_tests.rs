//! Port of `test/openai-codex-oauth.test.ts` (plus the Codex case of
//! `test/oauth-auth.test.ts`). Fake timers become tokio paused time; the
//! wall-clock `expires` is checked against a window because `Date.now()` is
//! not faked in Rust.

use std::sync::{Arc, Mutex, PoisonError};

use base64::Engine as _;
use eukhe_chord::context::{AbortController, AbortSignal};
use serde_json::json;
use tokio::time::Instant;

use super::openai_codex_oauth;
use crate::auth::errors::{date_now, js_error};
use crate::auth::oauth::http::{mock, FetchRequest, FetchResponse};
use crate::auth::oauth::test_support::{never_aborted_signal, url_param, Events, TestInteraction};
use crate::auth::types::{AuthEvent, AuthPromptKind, AuthSelectOption, ModelAuth, OAuthCredential};
use crate::utils::diagnostics::Thrown;

const USER_CODE_URL: &str = "https://auth.openai.com/api/accounts/deviceauth/usercode";
const DEVICE_TOKEN_URL: &str = "https://auth.openai.com/api/accounts/deviceauth/token";
const TOKEN_URL: &str = "https://auth.openai.com/oauth/token";

fn create_access_token(account_id: &str) -> String {
    let engine = base64::engine::general_purpose::STANDARD;
    let header = engine.encode(json!({ "alg": "none" }).to_string());
    let payload = engine.encode(
        json!({ "https://api.openai.com/auth": { "chatgpt_account_id": account_id } }).to_string(),
    );
    format!("{header}.{payload}.signature")
}

fn json_response(body: &serde_json::Value, status: u16) -> FetchResponse {
    FetchResponse::json_response(body, status)
}

fn device_auth_pending_response() -> FetchResponse {
    json_response(
        &json!({
            "error": {
                "message": "Device authorization is pending. Please try again.",
                "type": "invalid_request_error",
                "param": null,
                "code": "deviceauth_authorization_pending",
            }
        }),
        403,
    )
}

fn form_param(request: &FetchRequest, name: &str) -> Option<String> {
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

fn login_device_code(
    signal: AbortSignal,
    events: Events,
) -> impl std::future::Future<Output = Result<OAuthCredential, Thrown>> {
    let interaction = TestInteraction::provider(
        signal,
        |prompt| {
            Box::pin(async move {
                match prompt.kind {
                    AuthPromptKind::Select { .. } => Ok("device_code".to_owned()),
                    other => Err(js_error(format!("Unexpected prompt: {other:?}"))),
                }
            })
        },
        move |event| events.push(event),
    );
    async move { openai_codex_oauth().login(interaction, None).await }
}

fn device_infos(events: &Events) -> Vec<AuthEvent> {
    events
        .all()
        .into_iter()
        .filter(|event| matches!(event, AuthEvent::DeviceCode { .. }))
        .collect()
}

#[tokio::test(start_paused = true)]
async fn logs_in_with_the_openai_codex_device_code_flow() {
    let start = Instant::now();
    let access_token = create_access_token("account-123");
    let poll_times = Arc::new(Mutex::new(Vec::new()));
    let poll_responses = Arc::new(Mutex::new(vec![
        device_auth_pending_response(),
        json_response(
            &json!({
                "authorization_code": "oauth-code",
                "code_challenge": "device-code-challenge",
                "code_verifier": "device-code-verifier",
            }),
            200,
        ),
    ]));
    let times = Arc::clone(&poll_times);
    let token = access_token.clone();
    let _guard = install(move |request| {
        match request.url.as_str() {
            USER_CODE_URL => {
                assert_eq!(request.method, "POST");
                assert_eq!(request.header_value("Content-Type"), Some("application/json"));
                assert_eq!(request.json_body(), json!({ "client_id": "app_EMoamEEZ73f0CkXaXp7hrann" }));
                Ok(json_response(
                    &json!({ "device_auth_id": "device-auth-id", "user_code": "ABCD-1234", "interval": "5" }),
                    200,
                ))
            }
            DEVICE_TOKEN_URL => {
                times
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(start.elapsed().as_millis());
                assert_eq!(request.method, "POST");
                assert_eq!(request.header_value("Content-Type"), Some("application/json"));
                assert_eq!(
                    request.json_body(),
                    json!({ "device_auth_id": "device-auth-id", "user_code": "ABCD-1234" })
                );
                let mut responses = poll_responses.lock().unwrap_or_else(PoisonError::into_inner);
                if responses.is_empty() {
                    return Err(js_error("Unexpected extra device auth poll"));
                }
                Ok(responses.remove(0))
            }
            TOKEN_URL => {
                assert_eq!(request.method, "POST");
                assert_eq!(
                    request.header_value("Content-Type"),
                    Some("application/x-www-form-urlencoded")
                );
                assert_eq!(form_param(request, "grant_type").as_deref(), Some("authorization_code"));
                assert_eq!(form_param(request, "client_id").as_deref(), Some("app_EMoamEEZ73f0CkXaXp7hrann"));
                assert_eq!(form_param(request, "code").as_deref(), Some("oauth-code"));
                assert_eq!(
                    form_param(request, "redirect_uri").as_deref(),
                    Some("https://auth.openai.com/deviceauth/callback")
                );
                assert_eq!(form_param(request, "code_verifier").as_deref(), Some("device-code-verifier"));
                Ok(json_response(
                    &json!({ "access_token": token, "refresh_token": "refresh-token", "expires_in": 3600 }),
                    200,
                ))
            }
            url => Err(js_error(format!("Unexpected fetch URL: {url}"))),
        }
    })
    .await;

    let events = Events::default();
    let before = date_now();
    let credentials = login_device_code(never_aborted_signal(), events.clone())
        .await
        .expect("login");
    let after = date_now();

    assert_eq!(
        device_infos(&events),
        vec![AuthEvent::DeviceCode {
            user_code: "ABCD-1234".to_owned(),
            verification_uri: "https://auth.openai.com/codex/device".to_owned(),
            interval_seconds: Some(5.0),
            expires_in_seconds: Some(900.0),
        }]
    );
    assert_eq!(credentials.access, access_token);
    assert_eq!(credentials.refresh, "refresh-token");
    assert!(credentials.expires >= before + 3600.0 * 1000.0);
    assert!(credentials.expires <= after + 3600.0 * 1000.0);
    assert_eq!(credentials.extra_str("accountId"), Some("account-123"));
    assert_eq!(
        *poll_times.lock().unwrap_or_else(PoisonError::into_inner),
        vec![0, 5000]
    );
}

#[tokio::test]
async fn offers_browser_login_first_and_uses_the_selected_openai_codex_device_code_flow() {
    let access_token = create_access_token("account-456");
    let token = access_token.clone();
    let _guard = install(move |request| match request.url.as_str() {
        USER_CODE_URL => {
            assert_eq!(request.json_body(), json!({ "client_id": "app_EMoamEEZ73f0CkXaXp7hrann" }));
            Ok(json_response(
                &json!({ "device_auth_id": "device-auth-id", "user_code": "WXYZ-7890", "interval": "5" }),
                200,
            ))
        }
        DEVICE_TOKEN_URL => Ok(json_response(
            &json!({
                "authorization_code": "oauth-code",
                "code_challenge": "device-code-challenge",
                "code_verifier": "device-code-verifier",
            }),
            200,
        )),
        TOKEN_URL => Ok(json_response(
            &json!({ "access_token": token, "refresh_token": "refresh-token", "expires_in": 3600 }),
            200,
        )),
        url => Err(js_error(format!("Unexpected fetch URL: {url}"))),
    })
    .await;

    let select_prompts = Arc::new(Mutex::new(Vec::new()));
    let recorded = Arc::clone(&select_prompts);
    let events = Events::default();
    let notify_events = events.clone();
    let interaction = TestInteraction::provider(
        never_aborted_signal(),
        move |prompt| {
            let recorded = Arc::clone(&recorded);
            Box::pin(async move {
                match prompt.kind {
                    kind @ AuthPromptKind::Select { .. } => {
                        recorded
                            .lock()
                            .unwrap_or_else(PoisonError::into_inner)
                            .push(kind);
                        Ok("device_code".to_owned())
                    }
                    _ => Err(js_error("Text prompt should not be used")),
                }
            })
        },
        move |event| {
            assert!(
                !matches!(event, AuthEvent::AuthUrl { .. }),
                "Browser login should not start"
            );
            notify_events.push(event);
        },
    );
    let credential = openai_codex_oauth()
        .login(interaction, None)
        .await
        .expect("login");
    assert_eq!(credential.access, access_token);
    assert_eq!(credential.refresh, "refresh-token");
    assert_eq!(credential.extra_str("accountId"), Some("account-456"));

    assert_eq!(
        *select_prompts
            .lock()
            .unwrap_or_else(PoisonError::into_inner),
        vec![AuthPromptKind::Select {
            message: "Select OpenAI Codex login method:".to_owned(),
            options: vec![
                AuthSelectOption::new("browser", "Browser login (default)"),
                AuthSelectOption::new("device_code", "Device code login (headless)"),
            ],
        }]
    );
    assert_eq!(
        device_infos(&events),
        vec![AuthEvent::DeviceCode {
            user_code: "WXYZ-7890".to_owned(),
            verification_uri: "https://auth.openai.com/codex/device".to_owned(),
            interval_seconds: Some(5.0),
            expires_in_seconds: Some(900.0),
        }]
    );
}

#[tokio::test]
async fn cancels_when_openai_codex_login_method_selection_is_cancelled() {
    let interaction = TestInteraction::provider(
        never_aborted_signal(),
        |_| Box::pin(async { Err(js_error("Login cancelled")) }),
        |_| {},
    );
    let error = openai_codex_oauth()
        .login(interaction, None)
        .await
        .expect_err("cancelled");
    assert!(error.to_string().contains("Login cancelled"));
}

fn pending_route(
    interval: &'static str,
    polls: Arc<Mutex<usize>>,
) -> impl Fn(&FetchRequest) -> Result<FetchResponse, Thrown> + Send + Sync + 'static {
    move |request| match request.url.as_str() {
        USER_CODE_URL => {
            assert_eq!(
                request.json_body(),
                json!({ "client_id": "app_EMoamEEZ73f0CkXaXp7hrann" })
            );
            Ok(json_response(
                &json!({ "device_auth_id": "device-auth-id", "user_code": "ABCD-1234", "interval": interval }),
                200,
            ))
        }
        DEVICE_TOKEN_URL => {
            *polls.lock().unwrap_or_else(PoisonError::into_inner) += 1;
            Ok(device_auth_pending_response())
        }
        url => Err(js_error(format!("Unexpected fetch URL: {url}"))),
    }
}

#[tokio::test(start_paused = true)]
async fn cancels_the_openai_codex_device_code_flow_while_waiting() {
    let polls = Arc::new(Mutex::new(0));
    let _guard = install(pending_route("5", Arc::clone(&polls))).await;
    let controller = AbortController::new();
    let login = tokio::spawn(login_device_code(controller.signal(), Events::default()));
    while *polls.lock().unwrap_or_else(PoisonError::into_inner) == 0 {
        tokio::task::yield_now().await;
    }
    assert_eq!(*polls.lock().unwrap_or_else(PoisonError::into_inner), 1);

    controller.abort(None);
    let error = login.await.expect("join").expect_err("cancelled");
    assert_eq!(error.to_string(), "Login cancelled");
}

#[tokio::test(start_paused = true)]
async fn times_out_the_openai_codex_device_code_flow_after_15_minutes() {
    let polls = Arc::new(Mutex::new(0));
    let _guard = install(pending_route("60", Arc::clone(&polls))).await;
    let error = login_device_code(never_aborted_signal(), Events::default())
        .await
        .expect_err("times out");
    assert_eq!(error.to_string(), "Device flow timed out");
    assert!(*polls.lock().unwrap_or_else(PoisonError::into_inner) >= 1);
}

#[tokio::test(start_paused = true)]
async fn treats_openai_codex_device_auth_403_and_404_responses_as_pending() {
    let access_token = create_access_token("account-403-404");
    let token = access_token.clone();
    let polls = Arc::new(Mutex::new(Vec::new()));
    let recorded = Arc::clone(&polls);
    let _guard = install(move |request| match request.url.as_str() {
        USER_CODE_URL => Ok(json_response(
            &json!({ "device_auth_id": "device-auth-id", "user_code": "ABCD-1234", "interval": "1" }),
            200,
        )),
        DEVICE_TOKEN_URL => {
            let mut polls = recorded.lock().unwrap_or_else(PoisonError::into_inner);
            polls.push(());
            match polls.len() {
                1 => Ok(json_response(&json!({ "error": "access_denied", "error_description": "denied" }), 403)),
                2 => Ok(FetchResponse {
                    status: 404,
                    status_text: String::new(),
                    headers: vec![("content-type".to_owned(), "text/plain".to_owned())],
                    body: "not ready".to_owned(),
                }),
                3 => Ok(json_response(
                    &json!({
                        "authorization_code": "oauth-code",
                        "code_challenge": "device-code-challenge",
                        "code_verifier": "device-code-verifier",
                    }),
                    200,
                )),
                _ => Err(js_error("Unexpected extra device auth poll")),
            }
        }
        TOKEN_URL => Ok(json_response(
            &json!({ "access_token": token, "refresh_token": "refresh-token", "expires_in": 3600 }),
            200,
        )),
        url => Err(js_error(format!("Unexpected fetch URL: {url}"))),
    })
    .await;

    let credential = login_device_code(never_aborted_signal(), Events::default())
        .await
        .expect("login");
    assert_eq!(credential.access, access_token);
    assert_eq!(credential.refresh, "refresh-token");
    assert_eq!(credential.extra_str("accountId"), Some("account-403-404"));
    assert_eq!(
        polls.lock().unwrap_or_else(PoisonError::into_inner).len(),
        3
    );
}

#[tokio::test]
async fn includes_the_response_body_in_openai_codex_device_auth_poll_failures() {
    let _guard = install(|request| match request.url.as_str() {
        USER_CODE_URL => Ok(json_response(
            &json!({ "device_auth_id": "device-auth-id", "user_code": "ABCD-1234", "interval": "5" }),
            200,
        )),
        DEVICE_TOKEN_URL => Ok(json_response(
            &json!({ "error": "server_error", "error_description": "try again later" }),
            500,
        )),
        url => Err(js_error(format!("Unexpected fetch URL: {url}"))),
    })
    .await;
    let error = login_device_code(never_aborted_signal(), Events::default())
        .await
        .expect_err("fails");
    assert!(error.to_string().contains(
        r#"OpenAI Codex device auth failed with status 500: {"error":"server_error","error_description":"try again later"}"#
    ));
}

#[tokio::test]
async fn does_not_write_token_refresh_failures_to_stderr() {
    let _guard = install(|_| {
        Ok(FetchResponse {
            status: 401,
            status_text: "Unauthorized".to_owned(),
            headers: vec![("content-type".to_owned(), "application/json".to_owned())],
            body: json!({
                "error": {
                    "message": "Could not validate your token. Please try signing in again.",
                    "type": "invalid_request_error",
                }
            })
            .to_string(),
        })
    })
    .await;
    let error = openai_codex_oauth()
        .refresh(
            OAuthCredential::new("invalid-refresh-token", "invalid-access-token", 0.0),
            never_aborted_signal(),
        )
        .await
        .expect_err("fails");
    let message = error.to_string();
    assert!(
        message.starts_with("OpenAI Codex token refresh failed (401)"),
        "{message}"
    );
    assert!(
        message.contains("Could not validate your token"),
        "{message}"
    );
}

#[tokio::test]
async fn falls_back_to_the_pasted_redirect_url_when_the_fixed_callback_port_is_taken() {
    let exchange_body: Arc<Mutex<Option<FetchRequest>>> = Arc::default();
    let recorded = Arc::clone(&exchange_body);
    let _guard = install(move |request| {
        assert_eq!(request.url, TOKEN_URL);
        *recorded.lock().unwrap_or_else(PoisonError::into_inner) = Some(request.clone());
        Ok(json_response(
            &json!({ "access_token": create_access_token("acct"), "refresh_token": "refresh", "expires_in": 3600 }),
            200,
        ))
    })
    .await;
    // Port 1455 is registered with OpenAI; the Codex CLI may hold it. Occupy it unless it already is.
    let _blocker = tokio::net::TcpListener::bind("127.0.0.1:1455").await.ok();

    let events = Events::default();
    let prompt_events = events.clone();
    let notify_events = events.clone();
    let interaction = TestInteraction::provider(
        never_aborted_signal(),
        move |prompt| {
            let auth_url = prompt_events.auth_url();
            Box::pin(async move {
                match prompt.kind {
                    AuthPromptKind::Select { .. } => Ok("browser".to_owned()),
                    AuthPromptKind::ManualCode { .. } => {
                        let state = url_param(&auth_url, "state").unwrap_or_default();
                        Ok(format!(
                            "http://localhost:1455/auth/callback?code=pasted-code&state={state}"
                        ))
                    }
                    other => Err(js_error(format!("Unexpected prompt: {other:?}"))),
                }
            })
        },
        move |event| notify_events.push(event),
    );
    let credential = openai_codex_oauth()
        .login(interaction, None)
        .await
        .expect("login");

    assert_eq!(credential.extra_str("accountId"), Some("acct"));
    let request = exchange_body
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("exchanged");
    assert_eq!(form_param(&request, "code").as_deref(), Some("pasted-code"));
    assert_eq!(
        form_param(&request, "redirect_uri").as_deref(),
        Some("http://localhost:1455/auth/callback")
    );
}

// From test/oauth-auth.test.ts.

#[tokio::test]
async fn openai_codex_to_auth_derives_the_api_key_from_the_access_token() {
    let auth = openai_codex_oauth()
        .to_auth(&OAuthCredential::new("r", "token", 0.0))
        .await
        .expect("to_auth");
    assert_eq!(
        auth,
        ModelAuth {
            api_key: Some("token".to_owned()),
            ..ModelAuth::default()
        }
    );
}
