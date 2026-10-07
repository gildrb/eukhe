//! Port of `test/anthropic-oauth.test.ts` (plus the Anthropic cases of
//! `test/oauth-auth.test.ts`).

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::AbortSignal;
use serde_json::json;

use super::anthropic_oauth;
use crate::auth::errors::{date_now, js_error};
use crate::auth::oauth::http::{mock, FetchRequest, FetchResponse};
use crate::auth::oauth::test_support::{
    native_get, never_aborted_signal, url_param, Events, Page, TestInteraction,
};
use crate::auth::types::{AuthEvent, AuthPromptKind, AuthSelectOption, ModelAuth, OAuthCredential};

const TOKEN_URL: &str = "https://platform.claude.com/v1/oauth/token";

type Calls = Arc<Mutex<Vec<FetchRequest>>>;

async fn token_mock(
    check: impl Fn(&FetchRequest) + Send + Sync + 'static,
    body: serde_json::Value,
) -> (mock::FetchMockGuard, Calls) {
    let calls: Calls = Arc::default();
    let recorded = Arc::clone(&calls);
    let guard = mock::install(move |request: FetchRequest| {
        check(&request);
        recorded
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(request);
        let response = FetchResponse::json_response(&body, 200);
        async move { Ok(response) }
    })
    .await;
    (guard, calls)
}

fn call_count(calls: &Calls) -> usize {
    calls.lock().unwrap_or_else(PoisonError::into_inner).len()
}

#[tokio::test]
async fn keeps_the_localhost_redirect_uri_for_manual_callback_login() {
    let (_guard, calls) = token_mock(
        |request| {
            assert_eq!(request.url, TOKEN_URL);
            assert_eq!(request.method, "POST");
            let body = request.json_body();
            assert_eq!(body["grant_type"], "authorization_code");
            assert_eq!(body["code"], "manual-code");
            assert_eq!(body["redirect_uri"], "http://localhost:53692/callback");
        },
        json!({ "access_token": "access-token", "refresh_token": "refresh-token", "expires_in": 3600 }),
    )
    .await;

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
                        let state = url_param(&auth_url, "state").expect("state");
                        let redirect_uri =
                            url_param(&auth_url, "redirect_uri").expect("redirect_uri");
                        Ok(format!("{redirect_uri}?code=manual-code&state={state}"))
                    }
                    other => Err(js_error(format!("Unexpected prompt: {other:?}"))),
                }
            })
        },
        move |event| notify_events.push(event),
    );
    let credentials = anthropic_oauth()
        .login(interaction, None)
        .await
        .expect("login");

    assert_eq!(credentials.access, "access-token");
    assert_eq!(credentials.refresh, "refresh-token");
    assert_eq!(call_count(&calls), 1);
}

#[tokio::test]
async fn offers_browser_login_first_and_uses_the_selected_anthropic_copy_code_flow() {
    let events = Events::default();
    let check_events = events.clone();
    let (_guard, calls) = token_mock(
        move |request| {
            assert_eq!(request.url, TOKEN_URL);
            let body = request.json_body();
            assert_eq!(body["grant_type"], "authorization_code");
            assert_eq!(body["code"], "copied-code");
            assert_eq!(
                body["state"].as_str(),
                url_param(&check_events.auth_url(), "state").as_deref()
            );
            assert_eq!(body["redirect_uri"], "https://platform.claude.com/oauth/code/callback");
        },
        json!({ "access_token": "access-token", "refresh_token": "refresh-token", "expires_in": 3600 }),
    )
    .await;

    let select_prompts = Arc::new(Mutex::new(Vec::new()));
    let recorded = Arc::clone(&select_prompts);
    let prompt_events = events.clone();
    let notify_events = events.clone();
    let interaction = TestInteraction::provider(
        never_aborted_signal(),
        move |prompt| {
            let auth_url = prompt_events.auth_url();
            let recorded = Arc::clone(&recorded);
            Box::pin(async move {
                match prompt.kind {
                    kind @ AuthPromptKind::Select { .. } => {
                        recorded
                            .lock()
                            .unwrap_or_else(PoisonError::into_inner)
                            .push(kind);
                        Ok("copy_code".to_owned())
                    }
                    AuthPromptKind::ManualCode { .. } => Ok(format!(
                        "copied-code#{}",
                        url_param(&auth_url, "state").unwrap_or_default()
                    )),
                    other => Err(js_error(format!("Unexpected prompt: {other:?}"))),
                }
            })
        },
        move |event| notify_events.push(event),
    );
    let credentials = anthropic_oauth()
        .login(interaction, None)
        .await
        .expect("login");

    assert_eq!(credentials.access, "access-token");
    assert_eq!(credentials.refresh, "refresh-token");
    assert_eq!(
        url_param(&events.auth_url(), "redirect_uri").as_deref(),
        Some("https://platform.claude.com/oauth/code/callback")
    );
    assert_eq!(call_count(&calls), 1);
    assert_eq!(
        *select_prompts
            .lock()
            .unwrap_or_else(PoisonError::into_inner),
        vec![AuthPromptKind::Select {
            message: "Select Anthropic login method:".to_owned(),
            options: vec![
                AuthSelectOption::new("browser", "Browser login (default)"),
                AuthSelectOption::new("copy_code", "Copy code login (headless)"),
            ],
        }]
    );
}

#[tokio::test]
async fn cancels_when_anthropic_login_method_selection_is_cancelled() {
    let interaction = TestInteraction::provider(
        never_aborted_signal(),
        |_| Box::pin(async { Err(js_error("Login cancelled")) }),
        |_| {},
    );
    let error = anthropic_oauth()
        .login(interaction, None)
        .await
        .expect_err("cancelled");
    assert!(error.to_string().contains("Login cancelled"));
}

#[tokio::test]
async fn omits_scope_from_refresh_token_requests() {
    let (_guard, calls) = token_mock(
        |request| {
            assert_eq!(request.url, TOKEN_URL);
            assert_eq!(request.method, "POST");
            let body = request.json_body();
            assert_eq!(body["grant_type"], "refresh_token");
            assert!(body["client_id"].as_str().is_some_and(|id| !id.is_empty()));
            assert_eq!(body["refresh_token"], "refresh-token");
            assert!(body.get("scope").is_none());
        },
        json!({ "access_token": "new-access-token", "refresh_token": "new-refresh-token", "expires_in": 3600 }),
    )
    .await;

    let credentials = anthropic_oauth()
        .refresh(
            OAuthCredential::new("refresh-token", "old-access-token", 0.0),
            never_aborted_signal(),
        )
        .await
        .expect("refresh");

    assert_eq!(credentials.access, "new-access-token");
    assert_eq!(credentials.refresh, "new-refresh-token");
    assert_eq!(call_count(&calls), 1);
}

#[tokio::test]
async fn anthropic_oauth_login_resolves_through_the_manual_code_prompt_and_aborts_it_after_settling(
) {
    let (_guard, _calls) = token_mock(
        |request| {
            assert!(
                request.url.contains("/oauth/token"),
                "Unexpected fetch: {}",
                request.url
            );
        },
        json!({ "access_token": "access", "refresh_token": "refresh", "expires_in": 3600 }),
    )
    .await;

    let events = Events::default();
    let notify_events = events.clone();
    let prompts = Arc::new(Mutex::new(Vec::new()));
    let manual_signal: Arc<Mutex<Option<AbortSignal>>> = Arc::default();
    let recorded = Arc::clone(&prompts);
    let manual_slot = Arc::clone(&manual_signal);
    let interaction = TestInteraction::provider(
        never_aborted_signal(),
        move |prompt| {
            recorded
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(prompt.kind.clone());
            let manual_slot = Arc::clone(&manual_slot);
            Box::pin(async move {
                match prompt.kind {
                    AuthPromptKind::Select { .. } => Ok("browser".to_owned()),
                    AuthPromptKind::ManualCode { .. } => {
                        *manual_slot.lock().unwrap_or_else(PoisonError::into_inner) = prompt.signal;
                        Ok("the-code".to_owned())
                    }
                    other => Err(js_error(format!("Unexpected prompt: {other:?}"))),
                }
            })
        },
        move |event| notify_events.push(event),
    );
    let credential = anthropic_oauth()
        .login(interaction, None)
        .await
        .expect("login");

    assert_eq!(credential.access, "access");
    assert!(events
        .all()
        .iter()
        .any(|event| matches!(event, AuthEvent::AuthUrl { .. })));
    assert!(prompts
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .iter()
        .any(|kind| matches!(kind, AuthPromptKind::ManualCode { .. })));
    // the prompt's signal is aborted once login settles, so UIs can dismiss it
    let signal = manual_signal
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("manual prompt signal");
    assert!(signal.aborted());
}

#[tokio::test]
async fn completes_login_through_the_browser_callback_and_shows_the_sign_in_page() {
    let exchanged_code: Arc<Mutex<Option<String>>> = Arc::default();
    let exchanged = Arc::clone(&exchanged_code);
    let _guard = mock::install(move |request: FetchRequest| {
        assert_eq!(request.url, TOKEN_URL);
        *exchanged.lock().unwrap_or_else(PoisonError::into_inner) =
            request.json_body()["code"].as_str().map(str::to_owned);
        let response = FetchResponse::json_response(
            &json!({ "access_token": "access", "refresh_token": "refresh", "expires_in": 3600 }),
            200,
        );
        async move { Ok(response) }
    })
    .await;

    let callback_page: Arc<Mutex<Option<tokio::task::JoinHandle<Page>>>> = Arc::default();
    let page_slot = Arc::clone(&callback_page);
    let interaction = TestInteraction::provider(
        never_aborted_signal(),
        |prompt| {
            Box::pin(async move {
                if let AuthPromptKind::Select { .. } = prompt.kind {
                    return Ok("browser".to_owned());
                }
                if let Some(signal) = prompt.signal {
                    signal.cancelled().await;
                }
                Err(js_error("aborted"))
            })
        },
        move |event| {
            if let AuthEvent::AuthUrl { url, .. } = event {
                let state = url_param(&url, "state").unwrap_or_default();
                let handle = tokio::spawn(async move {
                    native_get(&format!(
                        "http://127.0.0.1:53692/callback?code=browser-code&state={state}"
                    ))
                    .await
                });
                *page_slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(handle);
            }
        },
    );
    let credential = anthropic_oauth()
        .login(interaction, None)
        .await
        .expect("login");

    assert_eq!(credential.access, "access");
    assert_eq!(
        exchanged_code
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .as_deref(),
        Some("browser-code")
    );
    let handle = callback_page
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
        .expect("callback fetched");
    let response = handle.await.expect("join");
    assert_eq!(response.status, 200);
    assert!(response.body.contains("Signed in to Anthropic."));
}

// From test/oauth-auth.test.ts.

#[tokio::test]
async fn anthropic_to_auth_derives_the_api_key_from_the_access_token() {
    let auth = anthropic_oauth()
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

#[tokio::test]
async fn anthropic_refresh_exchanges_the_refresh_token_and_returns_a_typed_credential() {
    let (_guard, _calls) = token_mock(
        |_| {},
        json!({ "access_token": "new-access", "refresh_token": "new-refresh", "expires_in": 3600 }),
    )
    .await;
    let refreshed = anthropic_oauth()
        .refresh(
            OAuthCredential::new("old-r", "old", 0.0),
            never_aborted_signal(),
        )
        .await
        .expect("refresh");
    assert_eq!(refreshed.access, "new-access");
    assert_eq!(refreshed.refresh, "new-refresh");
    assert!(refreshed.expires > date_now());
}
