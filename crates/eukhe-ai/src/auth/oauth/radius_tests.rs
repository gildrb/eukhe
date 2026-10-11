//! Port of `test/radius-oauth.test.ts`. The wall-clock `expires` is checked
//! against a window because `Date.now()` is not faked in Rust.

use std::sync::{Arc, Mutex, PoisonError};

use serde_json::json;

use super::{create_radius_oauth, RadiusOAuthOptions};
use crate::auth::errors::{date_now, js_error};
use crate::auth::oauth::http::{mock, FetchRequest, FetchResponse};
use crate::auth::oauth::test_support::{
    native_get, never_aborted_signal, url_param, Events, Page, TestInteraction,
};
use crate::auth::types::{AuthEvent, OAuthCredential, ProviderAuthInteraction};
use crate::utils::diagnostics::Thrown;

const GATEWAY: &str = "https://radius.example";

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

fn interaction(login_method: &'static str, events: Events) -> ProviderAuthInteraction {
    TestInteraction::provider(
        never_aborted_signal(),
        move |_| Box::pin(async move { Ok(login_method.to_owned()) }),
        move |event| events.push(event),
    )
}

fn radius() -> std::sync::Arc<dyn crate::auth::types::OAuthAuth> {
    create_radius_oauth(&RadiusOAuthOptions {
        name: "Radius".to_owned(),
        gateway: GATEWAY.to_owned(),
    })
}

#[tokio::test(start_paused = true)]
async fn uses_gateway_endpoints_directly_for_device_login() {
    let urls = Arc::new(Mutex::new(Vec::new()));
    let recorded = Arc::clone(&urls);
    let _guard = install(move |request| {
        recorded
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(request.url.clone());
        match request.url.as_str() {
            "https://radius.example/v1/oauth/device" => {
                assert_eq!(form(request, "client_id").as_deref(), Some("pi-gateway"));
                assert_eq!(
                    form(request, "scope").as_deref(),
                    Some("gateway offline_access")
                );
                Ok(FetchResponse::json_response(
                    &json!({
                        "device_code": "device-code",
                        "user_code": "ABCD-1234",
                        "verification_uri": "https://radius-ui.example/pair",
                        "expires_in": 600,
                        "interval": 5,
                    }),
                    200,
                ))
            }
            "https://radius.example/v1/oauth/token" => {
                assert_eq!(
                    form(request, "grant_type").as_deref(),
                    Some("urn:ietf:params:oauth:grant-type:device_code")
                );
                assert_eq!(form(request, "client_id").as_deref(), Some("pi-gateway"));
                assert_eq!(form(request, "device_code").as_deref(), Some("device-code"));
                Ok(FetchResponse::json_response(
                    &json!({
                        "access_token": "access-token",
                        "refresh_token": "refresh-token",
                        "expires_in": 3600,
                        "scope": "gateway offline_access",
                    }),
                    200,
                ))
            }
            url => Err(js_error(format!("Unexpected request: {url}"))),
        }
    })
    .await;

    let events = Events::default();
    let before = date_now();
    let credential = radius()
        .login(interaction("device-code", events.clone()), None)
        .await
        .expect("login");
    let after = date_now();
    let expected_offset = 3600.0 * 1000.0 - 60_000.0;
    assert!(
        credential.expires >= before + expected_offset
            && credential.expires <= after + expected_offset
    );
    assert_eq!(
        credential,
        OAuthCredential::new("refresh-token", "access-token", credential.expires)
            .with_extra("scope", json!("gateway offline_access"))
    );
    assert_eq!(
        events.all(),
        vec![AuthEvent::DeviceCode {
            user_code: "ABCD-1234".to_owned(),
            verification_uri: "https://radius-ui.example/pair".to_owned(),
            interval_seconds: Some(5.0),
            expires_in_seconds: Some(600.0),
        }]
    );
    assert_eq!(
        *urls.lock().unwrap_or_else(PoisonError::into_inner),
        vec![
            format!("{GATEWAY}/v1/oauth/device"),
            format!("{GATEWAY}/v1/oauth/token")
        ]
    );
}

#[tokio::test]
async fn refreshes_directly_through_the_gateway_without_discovery() {
    let calls = Arc::new(Mutex::new(0));
    let count = Arc::clone(&calls);
    let _guard = install(move |request| {
        *count.lock().unwrap_or_else(PoisonError::into_inner) += 1;
        assert_eq!(request.url, format!("{GATEWAY}/v1/oauth/token"));
        assert_eq!(form(request, "grant_type").as_deref(), Some("refresh_token"));
        assert_eq!(form(request, "client_id").as_deref(), Some("pi-gateway"));
        assert_eq!(form(request, "refresh_token").as_deref(), Some("old-refresh"));
        Ok(FetchResponse::json_response(
            &json!({ "access_token": "new-access", "refresh_token": "new-refresh", "expires_in": 3600 }),
            200,
        ))
    })
    .await;
    let credential = radius()
        .refresh(
            OAuthCredential::new("old-refresh", "old-access", 0.0),
            never_aborted_signal(),
        )
        .await
        .expect("refresh");
    assert_eq!(credential.access, "new-access");
    assert_eq!(credential.refresh, "new-refresh");
    assert_eq!(*calls.lock().unwrap_or_else(PoisonError::into_inner), 1);
}

#[tokio::test]
async fn discovers_only_the_interactive_browser_authorization_endpoint() {
    let calls = Arc::new(Mutex::new(0));
    let count = Arc::clone(&calls);
    let _guard = install(move |request| {
        *count.lock().unwrap_or_else(PoisonError::into_inner) += 1;
        assert_eq!(request.url, format!("{GATEWAY}/v1/oauth"));
        Ok(FetchResponse::json_response(
            &json!({ "issuer": "https://radius-ui.example" }),
            200,
        ))
    })
    .await;
    let error = radius()
        .login(interaction("browser", Events::default()), None)
        .await
        .expect_err("invalid config");
    assert!(error
        .to_string()
        .contains(&format!("Invalid Radius OAuth config from {GATEWAY}")));
    assert_eq!(*calls.lock().unwrap_or_else(PoisonError::into_inner), 1);
}

type PageSlot = Arc<Mutex<Option<tokio::task::JoinHandle<Page>>>>;

async fn browser_login() -> (Result<OAuthCredential, Thrown>, Page) {
    let page: PageSlot = Arc::default();
    let slot = Arc::clone(&page);
    let interaction = TestInteraction::provider(
        never_aborted_signal(),
        |_| Box::pin(async { Ok("browser".to_owned()) }),
        move |event| {
            if let AuthEvent::AuthUrl { url, .. } = event {
                let redirect = url_param(&url, "redirect_uri").unwrap_or_default();
                let state = url_param(&url, "state").unwrap_or_default();
                let mut callback = url::Url::parse(&redirect).expect("redirect");
                callback
                    .query_pairs_mut()
                    .append_pair("code", "browser-code")
                    .append_pair("state", &state);
                let handle = tokio::spawn(async move { native_get(callback.as_str()).await });
                *slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(handle);
            }
        },
    );
    let result = radius().login(interaction, None).await;
    let handle = page
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
        .expect("callback fetched");
    (result, handle.await.expect("join"))
}

#[tokio::test]
async fn exchanges_the_browser_callback_code_before_showing_the_sign_in_page() {
    let token_status = Arc::new(Mutex::new(400_u16));
    let status = Arc::clone(&token_status);
    let _guard = install(move |request| {
        if request.url == format!("{GATEWAY}/v1/oauth") {
            return Ok(FetchResponse::json_response(
                &json!({ "authorizationEndpoint": format!("{GATEWAY}/authorize") }),
                200,
            ));
        }
        if request.url == format!("{GATEWAY}/v1/oauth/token") {
            assert_eq!(form(request, "code").as_deref(), Some("browser-code"));
            let status = *status.lock().unwrap_or_else(PoisonError::into_inner);
            return Ok(if status == 200 {
                FetchResponse::json_response(
                    &json!({ "access_token": "access", "refresh_token": "refresh", "expires_in": 3600 }),
                    200,
                )
            } else {
                FetchResponse::json_response(
                    &json!({ "error": "invalid_grant", "error_description": "code expired" }),
                    status,
                )
            });
        }
        Err(js_error(format!("Unexpected request: {}", request.url)))
    })
    .await;

    let (failed, page) = browser_login().await;
    assert!(failed
        .expect_err("fails")
        .to_string()
        .contains("invalid_grant: code expired"));
    assert_eq!(page.status, 502);
    assert!(page.body.contains("code expired"));

    *token_status.lock().unwrap_or_else(PoisonError::into_inner) = 200;
    let (succeeded, page) = browser_login().await;
    assert_eq!(succeeded.expect("login").access, "access");
    assert_eq!(page.status, 200);
    assert!(page.body.contains("Signed in to Radius."));
}
