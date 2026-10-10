//! Port of `test/openai-chatgpt-oauth.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};

use serde_json::{json, Value};

use super::openai_chatgpt_oauth;
use crate::auth::errors::{date_now, js_error};
use crate::auth::oauth::http::{mock, FetchRequest, FetchResponse};
use crate::auth::oauth::test_support::{never_aborted_signal, url_param, Events, TestInteraction};
use crate::auth::types::{
    AuthEvent, AuthPromptKind, LoginOptions, OAuthCredential, ProviderAuthInteraction,
};

const TOKEN_URL: &str = "https://auth.openai.com/api/accounts/oauth/token";
const REQUIRED_SCOPE: &str =
    "openid profile email offline_access resource.invoke chatgpt.tokens.use.direct";
const DEVICE_ID: &str = "e61bbe28-07ef-466d-8e5d-a344f94ab305";

fn token_response(scope: &str) -> Value {
    json!({
        "access_token": "access-token",
        "refresh_token": "refresh-token",
        "expires_in": 3600,
        "id_token": "id-token",
        "scope": scope,
    })
}

type Bodies = Arc<Mutex<Vec<Vec<(String, String)>>>>;

async fn stub_token_endpoint(response: Value) -> (mock::FetchMockGuard, Bodies) {
    let bodies: Bodies = Arc::default();
    let recorded = Arc::clone(&bodies);
    let guard = mock::install(move |request: FetchRequest| {
        assert_eq!(request.url, TOKEN_URL);
        recorded
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(request.form_fields());
        let response = FetchResponse::json_response(&response, 200);
        async move { Ok(response) }
    })
    .await;
    (guard, bodies)
}

fn param(body: &[(String, String)], name: &str) -> Option<String> {
    body.iter()
        .find(|(key, _)| key == name)
        .map(|(_, value)| value.clone())
}

fn login_interaction(
    callback_client_id: Option<&'static str>,
    events: Events,
) -> ProviderAuthInteraction {
    let prompt_events = events.clone();
    TestInteraction::provider(
        never_aborted_signal(),
        move |prompt| {
            let authorize_url = prompt_events.auth_url();
            Box::pin(async move {
                if !matches!(prompt.kind, AuthPromptKind::ManualCode { .. }) {
                    return Err(js_error(format!("Unexpected prompt: {:?}", prompt.kind)));
                }
                if authorize_url.is_empty() {
                    return Err(js_error(
                        "Authorization URL was not emitted before the callback prompt",
                    ));
                }
                let mut callback =
                    url::Url::parse(&url_param(&authorize_url, "redirect_uri").unwrap_or_default())
                        .map_err(|error| js_error(error.to_string()))?;
                {
                    let mut query = callback.query_pairs_mut();
                    query.append_pair("code", "authorization-code");
                    query.append_pair(
                        "state",
                        &url_param(&authorize_url, "state").unwrap_or_default(),
                    );
                    if let Some(client_id) = callback_client_id {
                        query.append_pair("client_id", client_id);
                    }
                }
                Ok(callback.to_string())
            })
        },
        move |event| events.push(event),
    )
}

fn device_id_options(device_id: &'static str) -> LoginOptions {
    LoginOptions {
        get_device_id: Some(Arc::new(move || device_id.to_owned())),
        agent_name: None,
    }
}

fn connected_credential() -> OAuthCredential {
    OAuthCredential::new("old-refresh", "old-access", 0.0)
        .with_extra("clientId", json!("oaiapp_existing"))
        .with_extra(
            "scopes",
            json!(REQUIRED_SCOPE.split(' ').collect::<Vec<_>>()),
        )
}

#[tokio::test]
async fn registers_a_user_owned_client_and_stores_its_issued_id_and_granted_scopes() {
    let (_guard, bodies) = stub_token_endpoint(token_response(REQUIRED_SCOPE)).await;
    let events = Events::default();
    let credential = openai_chatgpt_oauth()
        .login(
            login_interaction(Some("oaiapp_issued"), events.clone()),
            Some(device_id_options(DEVICE_ID)),
        )
        .await
        .expect("login");

    let authorize_url = events.auth_url();
    let get = |name| url_param(&authorize_url, name);
    assert_eq!(get("client_id").as_deref(), Some("dynamic_agent_client"));
    assert_eq!(get("agent_name_hint").as_deref(), Some("Pi"));
    assert_eq!(
        get("ext_agent_host_id"),
        Some(format!("urn:uuid:{DEVICE_ID}"))
    );
    assert_eq!(get("scope").as_deref(), Some(REQUIRED_SCOPE));
    assert_eq!(
        get("redirect_uri").as_deref(),
        Some("http://127.0.0.1:1455/auth/callback")
    );
    assert_eq!(
        get("resource").as_deref(),
        Some("https://api.openai.com/v1")
    );
    assert_eq!(get("code_challenge_method").as_deref(), Some("S256"));
    let body = bodies.lock().unwrap_or_else(PoisonError::into_inner)[0].clone();
    assert_eq!(param(&body, "client_id").as_deref(), Some("oaiapp_issued"));
    assert_eq!(param(&body, "code").as_deref(), Some("authorization-code"));
    assert_eq!(
        param(&body, "resource").as_deref(),
        Some("https://api.openai.com/v1")
    );
    assert!(param(&body, "code_verifier").is_some_and(|verifier| !verifier.is_empty()));
    assert_eq!(credential.access, "access-token");
    assert_eq!(credential.refresh, "refresh-token");
    assert_eq!(credential.extra_str("clientId"), Some("oaiapp_issued"));
    assert_eq!(
        credential.extra.get("scopes"),
        Some(&json!(REQUIRED_SCOPE.split(' ').collect::<Vec<_>>()))
    );
}

#[tokio::test]
async fn uses_the_apps_agent_name_as_the_name_hint() {
    let (_guard, _bodies) = stub_token_endpoint(token_response(REQUIRED_SCOPE)).await;
    let events = Events::default();
    openai_chatgpt_oauth()
        .login(
            login_interaction(Some("oaiapp_issued"), events.clone()),
            Some(LoginOptions {
                agent_name: Some("my-app".to_owned()),
                ..device_id_options(DEVICE_ID)
            }),
        )
        .await
        .expect("login");

    assert_eq!(
        url_param(&events.auth_url(), "agent_name_hint").as_deref(),
        Some("my-app")
    );
}

#[tokio::test]
async fn rejects_registration_without_an_issued_client_id() {
    let (_guard, bodies) = stub_token_endpoint(token_response(REQUIRED_SCOPE)).await;
    let error = openai_chatgpt_oauth()
        .login(
            login_interaction(None, Events::default()),
            Some(device_id_options(DEVICE_ID)),
        )
        .await
        .expect_err("rejects");
    assert!(error
        .to_string()
        .contains("registration callback did not contain an issued client ID"));
    assert!(bodies
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .is_empty());
}

#[tokio::test]
async fn rejects_a_token_response_that_did_not_grant_direct_token_use() {
    let (_guard, _bodies) = stub_token_endpoint(token_response(
        "openid profile email offline_access resource.invoke",
    ))
    .await;
    let error = openai_chatgpt_oauth()
        .login(
            login_interaction(Some("oaiapp_issued"), Events::default()),
            Some(device_id_options(DEVICE_ID)),
        )
        .await
        .expect_err("rejects");
    assert!(error
        .to_string()
        .contains("grant did not include chatgpt.tokens.use.direct"));
}

#[tokio::test]
async fn requires_a_device_id_before_starting_authorization() {
    let events = Events::default();
    let error = openai_chatgpt_oauth()
        .login(login_interaction(None, events.clone()), None)
        .await
        .expect_err("no device id");
    assert!(error.to_string().contains("requires a device ID"));
    let error = openai_chatgpt_oauth()
        .login(
            login_interaction(None, events.clone()),
            Some(device_id_options("not-a-uuid")),
        )
        .await
        .expect_err("bad device id");
    assert!(error.to_string().contains("requires a device ID"));
    assert!(!events
        .all()
        .iter()
        .any(|event| matches!(event, AuthEvent::AuthUrl { .. })));
}

#[tokio::test]
async fn requires_refresh_responses_to_rotate_the_refresh_token() {
    let mut response = token_response(REQUIRED_SCOPE);
    response
        .as_object_mut()
        .expect("object")
        .shift_remove("refresh_token");
    let (_guard, _bodies) = stub_token_endpoint(response).await;
    let error = openai_chatgpt_oauth()
        .refresh(connected_credential(), never_aborted_signal())
        .await
        .expect_err("rejects");
    assert!(error
        .to_string()
        .contains("token response has invalid refresh_token"));
}

#[tokio::test]
async fn refreshes_with_the_credentials_issued_client_id_and_stores_replacement_scopes() {
    let mut response = token_response(REQUIRED_SCOPE);
    response["access_token"] = json!("new-access");
    response["refresh_token"] = json!("new-refresh");
    let (_guard, bodies) = stub_token_endpoint(response).await;

    let before = date_now();
    let credential = openai_chatgpt_oauth()
        .refresh(connected_credential(), never_aborted_signal())
        .await
        .expect("refresh");

    // expires_in is 3600 seconds; the credential expires 3 minutes early so it is refreshed in time.
    assert!(credential.expires >= before + (3600.0 - 180.0) * 1000.0);
    assert!(credential.expires <= date_now() + (3600.0 - 180.0) * 1000.0);

    let body = bodies.lock().unwrap_or_else(PoisonError::into_inner)[0].clone();
    assert_eq!(param(&body, "grant_type").as_deref(), Some("refresh_token"));
    assert_eq!(
        param(&body, "client_id").as_deref(),
        Some("oaiapp_existing")
    );
    assert_eq!(
        param(&body, "refresh_token").as_deref(),
        Some("old-refresh")
    );
    assert_eq!(
        param(&body, "resource").as_deref(),
        Some("https://api.openai.com/v1")
    );
    assert!(param(&body, "scope").is_none());
    assert_eq!(credential.access, "new-access");
    assert_eq!(credential.refresh, "new-refresh");
    assert_eq!(credential.extra_str("clientId"), Some("oaiapp_existing"));
    assert_eq!(
        credential.extra.get("scopes"),
        Some(&json!(REQUIRED_SCOPE.split(' ').collect::<Vec<_>>()))
    );
}
