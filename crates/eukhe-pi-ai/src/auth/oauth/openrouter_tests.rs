//! Port of `test/openrouter-oauth.test.ts` (plus the `OpenRouter` case of
//! `test/oauth-auth.test.ts`). The provider/`Models` cases live with the
//! provider port.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{AbortController, AbortSignal};
use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};
use tokio::sync::oneshot;

use super::{open_router_oauth, MAX_SAFE_INTEGER};
use crate::auth::errors::js_error;
use crate::auth::oauth::http::{mock, FetchRequest, FetchResponse};
use crate::auth::oauth::pkce::base64url_encode;
use crate::auth::oauth::test_support::{
    native_get, never_aborted_signal, url_param, Page, TestInteraction,
};
use crate::auth::types::{
    AuthEvent, AuthPromptKind, ModelAuth, OAuthCredential, ProviderAuthInteraction,
};
use crate::utils::diagnostics::Thrown;

const TOKEN_URL: &str = "https://openrouter.ai/api/v1/auth/keys";

type Bodies = Arc<Mutex<Vec<Value>>>;

async fn stub(response: Value, status: u16) -> (mock::FetchMockGuard, Bodies) {
    let bodies: Bodies = Arc::default();
    let recorded = Arc::clone(&bodies);
    let guard = mock::install(move |request: FetchRequest| {
        assert_eq!(request.url, TOKEN_URL);
        recorded
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(request.json_body());
        let response = FetchResponse::json_response(&response, status);
        async move { Ok(response) }
    })
    .await;
    (guard, bodies)
}

fn calls(bodies: &Bodies) -> Vec<Value> {
    bodies
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
}

fn never_prompt(
    slot: Option<Arc<Mutex<Option<AbortSignal>>>>,
) -> impl Fn(
    crate::auth::types::AuthPrompt,
) -> futures::future::BoxFuture<'static, Result<String, Thrown>>
       + Send
       + Sync
       + 'static {
    move |prompt| {
        if let Some(slot) = &slot {
            *slot.lock().unwrap_or_else(PoisonError::into_inner) = prompt.signal;
        }
        Box::pin(std::future::pending())
    }
}

type PageSlot = Arc<Mutex<Option<tokio::task::JoinHandle<Page>>>>;

/// Notify handler that hits the callback URL with `code` (`nativeFetch`).
fn hit_callback(
    code: &'static str,
    page: PageSlot,
    authorize: Arc<Mutex<Option<String>>>,
) -> impl Fn(AuthEvent) + Send + Sync + 'static {
    move |event| {
        if let AuthEvent::AuthUrl { url, .. } = event {
            let callback = url_param(&url, "callback_url").unwrap_or_default();
            *authorize.lock().unwrap_or_else(PoisonError::into_inner) = Some(url);
            let mut callback_url = url::Url::parse(&callback).expect("callback url");
            callback_url.query_pairs_mut().append_pair("code", code);
            let handle = tokio::spawn(async move { native_get(callback_url.as_str()).await });
            *page.lock().unwrap_or_else(PoisonError::into_inner) = Some(handle);
        }
    }
}

async fn take_page(page: &PageSlot) -> Page {
    let handle = page
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
        .expect("callback fetched");
    handle.await.expect("join")
}

fn expected_credential(access: &str) -> OAuthCredential {
    OAuthCredential::new("", access, MAX_SAFE_INTEGER)
}

#[tokio::test]
async fn runs_pkce_on_a_one_shot_loopback_callback_and_exchanges_the_code_for_a_permanent_api_key()
{
    let (_guard, bodies) = stub(json!({ "key": "sk-or-test" }), 200).await;
    let page: PageSlot = Arc::default();
    let authorize: Arc<Mutex<Option<String>>> = Arc::default();
    let manual_signal: Arc<Mutex<Option<AbortSignal>>> = Arc::default();
    let interaction = TestInteraction::provider(
        never_aborted_signal(),
        never_prompt(Some(Arc::clone(&manual_signal))),
        hit_callback(
            "authorization-code",
            Arc::clone(&page),
            Arc::clone(&authorize),
        ),
    );
    let credential = open_router_oauth()
        .login(interaction, None)
        .await
        .expect("login");

    assert_eq!(credential, expected_credential("sk-or-test"));
    assert_eq!(
        serde_json::to_value(&credential).expect("json")["expires"],
        json!(9_007_199_254_740_991_i64)
    );
    assert_eq!(take_page(&page).await.status, 200);
    assert!(manual_signal
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .as_ref()
        .is_some_and(AbortSignal::aborted));
    let authorize_url = authorize
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("auth url");
    let parsed = url::Url::parse(&authorize_url).expect("url");
    assert_eq!(
        parsed.origin().ascii_serialization(),
        "https://openrouter.ai"
    );
    assert_eq!(parsed.path(), "/auth");
    assert_eq!(
        url_param(&authorize_url, "code_challenge_method").as_deref(),
        Some("S256")
    );

    let callback_url =
        url::Url::parse(&url_param(&authorize_url, "callback_url").unwrap_or_default())
            .expect("callback");
    assert_eq!(callback_url.host_str(), Some("127.0.0.1"));
    let path = callback_url.path();
    let suffix = path
        .strip_prefix("/oauth/callback/")
        .expect("callback path");
    assert!(
        !suffix.is_empty()
            && suffix
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit() || byte == b'-')
    );

    let bodies = calls(&bodies);
    assert_eq!(bodies.len(), 1);
    assert_eq!(bodies[0]["code"], "authorization-code");
    assert_eq!(bodies[0]["code_challenge_method"], "S256");
    let verifier = bodies[0]["code_verifier"].as_str().expect("verifier");
    assert_eq!(
        url_param(&authorize_url, "code_challenge"),
        Some(base64url_encode(&Sha256::digest(verifier.as_bytes())))
    );
}

#[tokio::test]
async fn reports_token_exchange_failures_through_both_the_callback_page_and_login() {
    let (_guard, _bodies) = stub(json!({ "error": { "message": "invalid code" } }), 403).await;
    let page: PageSlot = Arc::default();
    let interaction = TestInteraction::provider(
        never_aborted_signal(),
        never_prompt(None),
        hit_callback("bad-code", Arc::clone(&page), Arc::default()),
    );
    let error = open_router_oauth()
        .login(interaction, None)
        .await
        .expect_err("fails");
    assert!(error
        .to_string()
        .contains("OpenRouter OAuth key exchange failed (HTTP 403): invalid code"));
    assert_eq!(take_page(&page).await.status, 502);
}

#[tokio::test]
async fn allows_only_one_token_exchange_for_a_callback() {
    let (started_tx, started_rx) = oneshot::channel::<oneshot::Sender<FetchResponse>>();
    let started_tx = Arc::new(Mutex::new(Some(started_tx)));
    let fetch_count = Arc::new(Mutex::new(0_usize));
    let count = Arc::clone(&fetch_count);
    let _guard = mock::install(move |_request: FetchRequest| {
        *count.lock().unwrap_or_else(PoisonError::into_inner) += 1;
        let (response_tx, response_rx) = oneshot::channel();
        if let Some(sender) = started_tx
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take()
        {
            let _ = sender.send(response_tx);
        }
        async move {
            response_rx
                .await
                .map_err(|error| js_error(error.to_string()))
        }
    })
    .await;

    let page: PageSlot = Arc::default();
    let authorize: Arc<Mutex<Option<String>>> = Arc::default();
    let interaction = TestInteraction::provider(
        never_aborted_signal(),
        never_prompt(None),
        hit_callback(
            "authorization-code",
            Arc::clone(&page),
            Arc::clone(&authorize),
        ),
    );
    let login = tokio::spawn(async move { open_router_oauth().login(interaction, None).await });

    let complete_exchange = started_rx.await.expect("token exchange started");
    let authorize_url = authorize
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("OpenRouter did not provide a callback URL");
    let mut callback_url =
        url::Url::parse(&url_param(&authorize_url, "callback_url").unwrap_or_default())
            .expect("url");
    callback_url
        .query_pairs_mut()
        .append_pair("code", "authorization-code");
    assert_eq!(native_get(callback_url.as_str()).await.status, 409);
    assert_eq!(
        *fetch_count.lock().unwrap_or_else(PoisonError::into_inner),
        1
    );
    complete_exchange
        .send(FetchResponse::json_response(
            &json!({ "key": "sk-or-test" }),
            200,
        ))
        .expect("send");

    let credential = login.await.expect("join").expect("login");
    assert_eq!(credential.access, "sk-or-test");
    assert_eq!(take_page(&page).await.status, 200);
}

#[tokio::test]
async fn rejects_a_successful_response_that_does_not_contain_a_key() {
    let (_guard, _bodies) = stub(json!({ "user_id": "user-1" }), 200).await;
    let page: PageSlot = Arc::default();
    let interaction = TestInteraction::provider(
        never_aborted_signal(),
        never_prompt(None),
        hit_callback("code-without-key", Arc::clone(&page), Arc::default()),
    );
    let error = open_router_oauth()
        .login(interaction, None)
        .await
        .expect_err("fails");
    assert!(error
        .to_string()
        .contains("OpenRouter OAuth response carries no \"key\""));
    assert_eq!(take_page(&page).await.status, 502);
}

fn manual_interaction(
    answer: impl Fn(Option<String>) -> Result<String, Thrown> + Send + Sync + 'static,
) -> ProviderAuthInteraction {
    let callback_url: Arc<Mutex<Option<String>>> = Arc::default();
    let prompt_slot = Arc::clone(&callback_url);
    let answer = Arc::new(answer);
    TestInteraction::provider(
        never_aborted_signal(),
        move |prompt| {
            let callback = prompt_slot
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .clone();
            let result = if matches!(prompt.kind, AuthPromptKind::ManualCode { .. }) {
                answer(callback)
            } else {
                Err(js_error(format!("Unexpected prompt: {:?}", prompt.kind)))
            };
            Box::pin(async move { result })
        },
        move |event| {
            if let AuthEvent::AuthUrl { url, .. } = event {
                *callback_url.lock().unwrap_or_else(PoisonError::into_inner) =
                    url_param(&url, "callback_url");
            }
        },
    )
}

#[tokio::test]
async fn mints_a_key_from_a_pasted_redirect_url_when_the_loopback_callback_never_arrives() {
    let (_guard, bodies) = stub(json!({ "key": "sk-or-manual" }), 200).await;
    let interaction = manual_interaction(|callback| {
        Ok(format!("{}?code=manual-code", callback.unwrap_or_default()))
    });
    let credential = open_router_oauth()
        .login(interaction, None)
        .await
        .expect("login");
    assert_eq!(credential, expected_credential("sk-or-manual"));
    let bodies = calls(&bodies);
    assert_eq!(bodies.len(), 1);
    assert_eq!(bodies[0]["code"], "manual-code");
    assert_eq!(bodies[0]["code_challenge_method"], "S256");
}

#[tokio::test]
async fn accepts_a_bare_authorization_code_from_the_manual_prompt() {
    let (_guard, bodies) = stub(json!({ "key": "sk-or-manual" }), 200).await;
    let interaction = manual_interaction(|_| Ok("  manual-code  ".to_owned()));
    let credential = open_router_oauth()
        .login(interaction, None)
        .await
        .expect("login");
    assert_eq!(credential.access, "sk-or-manual");
    assert_eq!(calls(&bodies)[0]["code"], "manual-code");
}

#[tokio::test]
async fn fails_login_when_the_manual_prompt_is_cancelled() {
    let (_guard, bodies) = stub(json!({ "key": "sk-or-unexpected" }), 200).await;
    let interaction = manual_interaction(|_| Err(js_error("Login cancelled")));
    let error = open_router_oauth()
        .login(interaction, None)
        .await
        .expect_err("fails");
    assert!(error.to_string().contains("Login cancelled"));
    assert!(calls(&bodies).is_empty());
}

#[tokio::test]
async fn rejects_empty_manual_input_without_exchanging_a_code() {
    let (_guard, bodies) = stub(json!({ "key": "sk-or-unexpected" }), 200).await;
    let interaction = manual_interaction(|_| Ok("   ".to_owned()));
    let error = open_router_oauth()
        .login(interaction, None)
        .await
        .expect_err("fails");
    assert!(error.to_string().contains("Missing authorization code"));
    assert!(calls(&bodies).is_empty());
}

fn aborting_interaction(
    controller: &AbortController,
    callback_url: Arc<Mutex<Option<String>>>,
) -> ProviderAuthInteraction {
    let abort = controller.clone();
    TestInteraction::provider(controller.signal(), never_prompt(None), move |event| {
        if let AuthEvent::AuthUrl { url, .. } = event {
            *callback_url.lock().unwrap_or_else(PoisonError::into_inner) =
                url_param(&url, "callback_url");
            abort.abort(None);
        }
    })
}

#[tokio::test]
async fn closes_the_pending_callback_when_login_is_cancelled() {
    let _serial = mock::serial().await;
    let controller = AbortController::new();
    let callback_url: Arc<Mutex<Option<String>>> = Arc::default();
    let interaction = aborting_interaction(&controller, Arc::clone(&callback_url));
    let error = open_router_oauth()
        .login(interaction, None)
        .await
        .expect_err("cancelled");
    assert!(error.to_string().contains("Login cancelled"));
    let callback_url = callback_url
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("callback url");
    let response = reqwest::get(callback_url).await;
    assert!(response.is_err(), "{response:?}");
}

#[tokio::test]
async fn rejects_before_opening_a_callback_server_when_login_is_already_cancelled() {
    let _serial = mock::serial().await;
    let controller = AbortController::new();
    controller.abort(None);
    let interaction = TestInteraction::provider(
        controller.signal(),
        |_| Box::pin(async { Ok(String::new()) }),
        |_| panic!("Cancelled login must not emit events"),
    );
    let error = open_router_oauth()
        .login(interaction, None)
        .await
        .expect_err("cancelled");
    assert!(error.to_string().contains("Login cancelled"));
}

#[tokio::test]
async fn uses_the_configured_oauth_callback_host() {
    let _serial = mock::serial().await;
    let previous = std::env::var("PI_OAUTH_CALLBACK_HOST").ok();
    std::env::set_var("PI_OAUTH_CALLBACK_HOST", "localhost");
    let controller = AbortController::new();
    let callback_url: Arc<Mutex<Option<String>>> = Arc::default();
    let interaction = aborting_interaction(&controller, Arc::clone(&callback_url));
    let result = open_router_oauth().login(interaction, None).await;
    match previous {
        Some(value) => std::env::set_var("PI_OAUTH_CALLBACK_HOST", value),
        None => std::env::remove_var("PI_OAUTH_CALLBACK_HOST"),
    }
    let error = result.expect_err("cancelled");
    assert!(error.to_string().contains("Login cancelled"));
    let callback_url = callback_url
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("callback url");
    assert_eq!(
        url::Url::parse(&callback_url).expect("url").host_str(),
        Some("localhost")
    );
}

// From test/oauth-auth.test.ts.

#[tokio::test]
async fn openrouter_derives_the_api_key_and_keeps_the_permanent_credential_on_refresh() {
    let credential = OAuthCredential::new("", "token", MAX_SAFE_INTEGER);
    let oauth = open_router_oauth();
    assert_eq!(
        oauth.to_auth(&credential).await.expect("to_auth"),
        ModelAuth {
            api_key: Some("token".to_owned()),
            ..ModelAuth::default()
        }
    );
    assert_eq!(
        oauth
            .refresh(credential.clone(), never_aborted_signal())
            .await
            .expect("refresh"),
        credential
    );
}
