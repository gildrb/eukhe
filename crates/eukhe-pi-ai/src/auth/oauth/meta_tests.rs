//! Port of `test/meta-oauth.test.ts`. The wall-clock `expires` is checked
//! against a window because `Date.now()` is not faked in Rust.

use std::sync::{Arc, Mutex, PoisonError};

use serde_json::json;

use super::meta_oauth;
use crate::auth::errors::{date_now, js_error};
use crate::auth::oauth::http::{mock, FetchRequest, FetchResponse};
use crate::auth::oauth::test_support::{never_aborted_signal, Events, TestInteraction};
use crate::auth::types::{AuthEvent, ModelAuth, OAuthCredential, ProviderAuthInteraction};
use crate::utils::diagnostics::Thrown;

const CLIENT_ID: &str = "1031625952748946";
const DEVICE_AUTHORIZATION_URL: &str = "https://auth.meta.com/oidc/device/authorization/";
const DEVICE_TOKEN_URL: &str = "https://auth.meta.com/oidc/device/token/";
const MINT_URL: &str = "https://api.meta.ai/muse-code/key";
const DAY_MS: f64 = 24.0 * 60.0 * 60.0 * 1000.0;

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
        |_| Box::pin(async { Err(js_error("Meta login should not prompt")) }),
        move |event| events.push(event),
    )
}

#[tokio::test(start_paused = true)]
async fn logs_in_with_the_device_flow_and_mints_a_model_api_key() {
    let poll_responses = Arc::new(Mutex::new(vec![
        FetchResponse::json_response(&json!({ "error": "authorization_pending" }), 400),
        FetchResponse::json_response(
            &json!({ "access_token": "identity-token", "token_type": "Bearer" }),
            200,
        ),
    ]));
    let _guard = install(move |request| match request.url.as_str() {
        DEVICE_AUTHORIZATION_URL => {
            assert_eq!(request.method, "POST");
            assert_eq!(form(request, "client_id").as_deref(), Some(CLIENT_ID));
            Ok(FetchResponse::json_response(
                &json!({
                    "device_code": "device-code-123",
                    "user_code": "ABCD-1234",
                    "verification_uri": "https://auth.meta.com/oauth/device/",
                    "verification_uri_complete": "https://auth.meta.com/oauth/device/?code=ABCD-1234",
                    "interval": 5,
                    "expires_in": 600,
                }),
                200,
            ))
        }
        DEVICE_TOKEN_URL => {
            assert_eq!(
                form(request, "grant_type").as_deref(),
                Some("urn:ietf:params:oauth:grant-type:device_code")
            );
            assert_eq!(form(request, "client_id").as_deref(), Some(CLIENT_ID));
            assert_eq!(form(request, "device_code").as_deref(), Some("device-code-123"));
            let mut responses = poll_responses.lock().unwrap_or_else(PoisonError::into_inner);
            if responses.is_empty() {
                return Err(js_error("Unexpected extra token poll"));
            }
            Ok(responses.remove(0))
        }
        MINT_URL => {
            assert_eq!(request.method, "POST");
            assert_eq!(request.header_value("Authorization"), Some("Bearer identity-token"));
            Ok(FetchResponse::json_response(&json!({ "api_key": "LLM|minted-key" }), 200))
        }
        url => Err(js_error(format!("Unexpected fetch URL: {url}"))),
    })
    .await;

    let events = Events::default();
    let before = date_now();
    let credential = meta_oauth()
        .login(create_interaction(events.clone()), None)
        .await
        .expect("login");
    let after = date_now();
    assert_eq!(
        events.all()[0],
        AuthEvent::DeviceCode {
            user_code: "ABCD-1234".to_owned(),
            verification_uri: "https://auth.meta.com/oauth/device/?code=ABCD-1234".to_owned(),
            interval_seconds: Some(5.0),
            expires_in_seconds: Some(600.0),
        }
    );
    assert_eq!(credential.refresh, "identity-token");
    assert_eq!(credential.access, "LLM|minted-key");
    assert!(credential.extra.is_empty());
    assert!(credential.expires >= before + DAY_MS && credential.expires <= after + DAY_MS);
}

#[tokio::test]
async fn re_mints_the_api_key_from_the_stored_identity_token_on_refresh() {
    let _guard = install(|request| {
        assert_eq!(request.url, MINT_URL);
        assert_eq!(
            request.header_value("Authorization"),
            Some("Bearer identity-token")
        );
        Ok(FetchResponse::json_response(
            &json!({ "api_key": "LLM|fresh-key" }),
            200,
        ))
    })
    .await;
    let before = date_now();
    let credential = meta_oauth()
        .refresh(
            OAuthCredential::new("identity-token", "LLM|old-key", 1.0),
            never_aborted_signal(),
        )
        .await
        .expect("refresh");
    let after = date_now();
    assert_eq!(credential.refresh, "identity-token");
    assert_eq!(credential.access, "LLM|fresh-key");
    assert!(credential.expires >= before + DAY_MS && credential.expires <= after + DAY_MS);
}

#[tokio::test]
async fn reports_the_setup_url_when_meta_issues_no_key() {
    let _guard = install(|_| {
        Ok(FetchResponse::json_response(
            &json!({ "require_payment": true, "action_url": "https://dev.meta.ai/billing" }),
            200,
        ))
    })
    .await;
    let error = meta_oauth()
        .refresh(
            OAuthCredential::new("identity-token", "", 1.0),
            never_aborted_signal(),
        )
        .await
        .expect_err("no key");
    assert!(error
        .to_string()
        .contains("Complete setup at https://dev.meta.ai/billing"));
}

#[tokio::test]
async fn uses_the_minted_key_as_the_request_api_key() {
    let auth = meta_oauth()
        .to_auth(&OAuthCredential::new("identity-token", "LLM|key", 1.0))
        .await
        .expect("to_auth");
    assert_eq!(
        auth,
        ModelAuth {
            api_key: Some("LLM|key".to_owned()),
            ..ModelAuth::default()
        }
    );
}
