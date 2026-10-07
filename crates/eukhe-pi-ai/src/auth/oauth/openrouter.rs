//! `OpenRouter` OAuth PKCE flow. Port of `auth/oauth/openrouter.ts`.
//!
//! `OpenRouter` exchanges an authorization code for a permanent, user-controlled
//! API key rather than an expiring access/refresh token pair. The callback is
//! handled by a one-shot loopback server on an ephemeral port, raced against a
//! manual prompt so remote/headless sessions can paste the redirect URL when
//! the browser cannot reach the loopback server.

use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use futures::future::BoxFuture;
use serde_json::Value;

use super::callback_server::{
    start_oauth_callback_server, wait_for_callback_or_manual_input, CallbackOrManual,
    OAuthCallbackServerOptions,
};
use super::http::{fetch, form_urlencode, FetchRequest};
use super::pkce::generate_pkce;
use super::{api_key_auth, first_param, query_pairs, shared};
use crate::auth::errors::{js_error, timeout_signal};
use crate::auth::types::{
    AuthEvent, LoginOptions, ModelAuth, OAuthAuth, OAuthCredential, ProviderAuthInteraction,
};
use crate::utils::diagnostics::Thrown;
use crate::utils::provider_env::get_provider_env_value;

const AUTHORIZE_URL: &str = "https://openrouter.ai/auth";
const TOKEN_URL: &str = "https://openrouter.ai/api/v1/auth/keys";
const LOGIN_TIMEOUT_MS: u64 = 5 * 60 * 1000;
const TOKEN_EXCHANGE_TIMEOUT_MS: u64 = 30_000;
/// `Number.MAX_SAFE_INTEGER`: the key never expires.
const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;

fn get_callback_host() -> String {
    get_provider_env_value("PI_OAUTH_CALLBACK_HOST", None).unwrap_or_else(|| "127.0.0.1".to_owned())
}

fn parse_authorization_input(input: &str) -> Option<String> {
    let value = input.trim();
    if value.is_empty() {
        return None;
    }

    if let Ok(url) = url::Url::parse(value) {
        return super::callback_server::query_param(&url, "code");
    }

    if value.contains("code=") {
        return first_param(&query_pairs(value), "code");
    }

    Some(value.to_owned())
}

fn error_detail(body: &Value) -> Option<String> {
    for key in ["error_description", "message", "error"] {
        if let Some(Value::String(value)) = body.get(key) {
            return Some(value.clone());
        }
    }
    body.get("error")
        .and_then(Value::as_object)
        .and_then(|error| error.get("message"))
        .and_then(Value::as_str)
        .map(str::to_owned)
}

async fn exchange_authorization_code(
    code: &str,
    verifier: &str,
    signal: &AbortSignal,
) -> Result<OAuthCredential, Thrown> {
    if signal.aborted() {
        return Err(js_error("Login cancelled"));
    }
    let timeout = timeout_signal(TOKEN_EXCHANGE_TIMEOUT_MS);
    let request_signal = AbortSignal::any(&[signal.clone(), timeout.clone()]);

    let exchange = async {
        let response = fetch(
            FetchRequest::post(TOKEN_URL)
                .header("accept", "application/json")
                .header("content-type", "application/json")
                .body(
                    serde_json::json!({
                        "code": code,
                        "code_verifier": verifier,
                        "code_challenge_method": "S256",
                    })
                    .to_string(),
                ),
            Some(&request_signal),
        )
        .await?;
        let body = match response.json() {
            Ok(parsed) if parsed.is_object() => parsed,
            Err(_) if response.ok() => {
                return Err(js_error("OpenRouter OAuth returned invalid JSON"))
            }
            Ok(_) | Err(_) => Value::Object(serde_json::Map::new()),
        };
        Ok((response, body))
    };
    let (response, body) = exchange.await.map_err(|error| {
        if signal.aborted() {
            js_error("Login cancelled")
        } else if timeout.aborted() {
            js_error("OpenRouter OAuth token exchange timed out")
        } else {
            error
        }
    })?;

    if !response.ok() {
        let detail = error_detail(&body)
            .filter(|detail| !detail.is_empty())
            .map(|detail| format!(": {detail}"))
            .unwrap_or_default();
        return Err(js_error(format!(
            "OpenRouter OAuth key exchange failed (HTTP {}){detail}",
            response.status
        )));
    }

    match body.get("key").and_then(Value::as_str) {
        Some(key) if !key.is_empty() => Ok(OAuthCredential::new("", key, MAX_SAFE_INTEGER)),
        _ => Err(js_error("OpenRouter OAuth response carries no \"key\"")),
    }
}

async fn login_open_router(
    interaction: &ProviderAuthInteraction,
) -> Result<OAuthCredential, Thrown> {
    let pkce = generate_pkce()?;
    let verifier = pkce.verifier.clone();
    let complete_signal = interaction.signal.clone();
    // OpenRouter sends no `state`; the random path keeps stray requests from completing the sign-in.
    let callback = start_oauth_callback_server(OAuthCallbackServerOptions {
        provider_name: "OpenRouter".to_owned(),
        host: get_callback_host(),
        port: 0,
        path: format!("/oauth/callback/{}", uuid::Uuid::new_v4()),
        redirect_host: None,
        state: None,
        complete: Arc::new(move |code| {
            let verifier = verifier.clone();
            let signal = complete_signal.clone();
            Box::pin(async move { exchange_authorization_code(&code, &verifier, &signal).await })
        }),
        signal: Some(interaction.signal.clone()),
        timeout_ms: Some(LOGIN_TIMEOUT_MS),
    })
    .await?;

    let result = async {
        let query = form_urlencode(&[
            ("callback_url", &callback.redirect_uri),
            ("code_challenge", &pkce.challenge),
            ("code_challenge_method", "S256"),
        ]);

        interaction.notify(AuthEvent::Progress {
            message: format!(
                "Listening for OpenRouter OAuth callback on {}",
                callback.redirect_uri
            ),
        });
        interaction.notify(AuthEvent::AuthUrl {
            url: format!("{AUTHORIZE_URL}?{query}"),
            instructions: Some("Complete sign-in in your browser. If the browser is on another machine, paste the final redirect URL here.".to_owned()),
        });

        let result = wait_for_callback_or_manual_input(
            interaction,
            Some(&callback),
            "Complete sign-in in your browser, or paste the authorization code / redirect URL here:",
            &callback.redirect_uri,
        )
        .await?;
        let input = match result {
            CallbackOrManual::Callback { value } => return Ok(value),
            CallbackOrManual::Manual { input } => input,
        };
        let Some(code) = parse_authorization_input(&input).filter(|code| !code.is_empty()) else {
            return Err(js_error("Missing authorization code"));
        };
        interaction.notify(AuthEvent::Progress {
            message: "Exchanging authorization code for an API key...".to_owned(),
        });
        exchange_authorization_code(&code, &pkce.verifier, &interaction.signal).await
    }
    .await;
    callback.close();
    result
}

struct OpenRouterOAuth;

impl OAuthAuth for OpenRouterOAuth {
    fn name(&self) -> &'static str {
        "OpenRouter OAuth"
    }

    fn login_label(&self) -> Option<&'static str> {
        Some("Sign in with OpenRouter")
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        _options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { login_open_router(&interaction).await })
    }

    fn refresh(
        &self,
        credential: OAuthCredential,
        _signal: AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { Ok(credential) })
    }

    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        Box::pin(async move { Ok(api_key_auth(&credential.access)) })
    }
}

/// The `OpenRouter` OAuth flow (`openRouterOAuth`).
#[must_use]
pub fn open_router_oauth() -> Arc<dyn OAuthAuth> {
    shared(OpenRouterOAuth)
}

#[cfg(test)]
#[path = "openrouter_tests.rs"]
mod tests;
