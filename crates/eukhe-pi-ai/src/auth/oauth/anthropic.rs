//! Anthropic OAuth flow (Claude Pro/Max). Port of `auth/oauth/anthropic.ts`.

use std::sync::{Arc, LazyLock};

use base64::Engine as _;
use eukhe_chord::context::AbortSignal;
use futures::future::BoxFuture;
use serde::Deserialize;

use super::callback_server::{
    start_oauth_callback_server, wait_for_callback_or_manual_input, CallbackOrManual,
    OAuthCallbackServerOptions,
};
use super::http::{fetch, FetchRequest};
use super::pkce::generate_pkce;
use super::{api_key_auth, error_name, parse_authorization_input, shared};
use crate::auth::errors::{date_now, js_error, timeout_signal};
use crate::auth::types::{
    AuthEvent, AuthPrompt, AuthPromptKind, AuthSelectOption, LoginOptions, ModelAuth, OAuthAuth,
    OAuthCredential, ProviderAuthInteraction,
};
use crate::utils::diagnostics::Thrown;
use crate::utils::provider_env::get_provider_env_value;

fn decode(value: &str) -> String {
    let bytes = base64::engine::general_purpose::STANDARD
        .decode(value)
        .unwrap_or_default();
    String::from_utf8(bytes).unwrap_or_default()
}

static CLIENT_ID: LazyLock<String> =
    LazyLock::new(|| decode("OWQxYzI1MGEtZTYxYi00NGQ5LTg4ZWQtNTk0NGQxOTYyZjVl"));
const AUTHORIZE_URL: &str = "https://claude.ai/oauth/authorize";
const TOKEN_URL: &str = "https://platform.claude.com/v1/oauth/token";
static CALLBACK_HOST: LazyLock<String> = LazyLock::new(|| {
    get_provider_env_value("PI_OAUTH_CALLBACK_HOST", None).unwrap_or_else(|| "127.0.0.1".to_owned())
});
const CALLBACK_PORT: u16 = 53692;
const CALLBACK_PATH: &str = "/callback";
const REDIRECT_URI: &str = "http://localhost:53692/callback";
const COPY_CODE_REDIRECT_URI: &str = "https://platform.claude.com/oauth/code/callback";
const ANTHROPIC_BROWSER_LOGIN_METHOD: &str = "browser";
const ANTHROPIC_COPY_CODE_LOGIN_METHOD: &str = "copy_code";
const SCOPES: &str = "org:create_api_key user:profile user:inference user:sessions:claude_code user:mcp_servers user:file_upload";

/// `name: message; cause=…` for a thrown value. JS stacks have no Rust
/// equivalent and are omitted.
fn format_error_details(error: &(dyn std::error::Error + 'static), name: &str) -> String {
    let mut details = vec![format!("{name}: {error}")];
    if let Some(io) = error.downcast_ref::<std::io::Error>() {
        if let Some(errno) = io.raw_os_error() {
            details.push(format!("errno={errno}"));
        }
    }
    if let Some(cause) = error.source() {
        details.push(format!("cause={}", format_error_details(cause, "Error")));
    }
    details.join("; ")
}

fn thrown_details(error: &Thrown) -> String {
    format_error_details(error.as_ref(), &error_name(error))
}

async fn post_json(
    url: &str,
    body: &serde_json::Value,
    signal: &AbortSignal,
) -> Result<String, Thrown> {
    let request_signal = AbortSignal::any(&[signal.clone(), timeout_signal(30_000)]);
    let response = fetch(
        FetchRequest::post(url)
            .header("Content-Type", "application/json")
            .header("Accept", "application/json")
            .body(body.to_string()),
        Some(&request_signal),
    )
    .await?;

    if !response.ok() {
        return Err(js_error(format!(
            "HTTP request failed. status={}; url={url}; body={}",
            response.status, response.body
        )));
    }
    Ok(response.body)
}

#[derive(Deserialize)]
struct TokenData {
    access_token: String,
    refresh_token: String,
    expires_in: f64,
}

fn credential_from(data: &TokenData) -> OAuthCredential {
    OAuthCredential::new(
        data.refresh_token.clone(),
        data.access_token.clone(),
        date_now() + data.expires_in * 1000.0 - 5.0 * 60.0 * 1000.0,
    )
}

async fn exchange_authorization_code(
    code: &str,
    state: &str,
    verifier: &str,
    redirect_uri: &str,
    signal: &AbortSignal,
) -> Result<OAuthCredential, Thrown> {
    let body = serde_json::json!({
        "grant_type": "authorization_code",
        "client_id": *CLIENT_ID,
        "code": code,
        "state": state,
        "redirect_uri": redirect_uri,
        "code_verifier": verifier,
    });
    let response_body = post_json(TOKEN_URL, &body, signal).await.map_err(|error| {
        js_error(format!(
            "Token exchange request failed. url={TOKEN_URL}; redirect_uri={redirect_uri}; response_type=authorization_code; details={}",
            thrown_details(&error)
        ))
    })?;

    let token_data: TokenData = serde_json::from_str(&response_body).map_err(|error| {
        js_error(format!(
            "Token exchange returned invalid JSON. url={TOKEN_URL}; body={response_body}; details=SyntaxError: {error}"
        ))
    })?;
    Ok(credential_from(&token_data))
}

fn authorize_url(challenge: &str, verifier: &str, redirect_uri: &str) -> String {
    let params = super::http::form_urlencode(&[
        ("code", "true"),
        ("client_id", &CLIENT_ID),
        ("response_type", "code"),
        ("redirect_uri", redirect_uri),
        ("scope", SCOPES),
        ("code_challenge", challenge),
        ("code_challenge_method", "S256"),
        ("state", verifier),
    ]);
    format!("{AUTHORIZE_URL}?{params}")
}

async fn login_anthropic(interaction: &ProviderAuthInteraction) -> Result<OAuthCredential, Thrown> {
    let pkce = generate_pkce()?;
    let callback = start_oauth_callback_server(OAuthCallbackServerOptions {
        provider_name: "Anthropic".to_owned(),
        host: CALLBACK_HOST.clone(),
        port: CALLBACK_PORT,
        path: CALLBACK_PATH.to_owned(),
        redirect_host: None,
        state: Some(pkce.verifier.clone()),
        complete: Arc::new(|code| Box::pin(async move { Ok(code) })),
        signal: Some(interaction.signal.clone()),
        timeout_ms: None,
    })
    .await
    .ok();

    let result = async {
        interaction.notify(AuthEvent::AuthUrl {
            url: authorize_url(&pkce.challenge, &pkce.verifier, REDIRECT_URI),
            instructions: Some("Complete login in your browser. If the browser is on another machine, paste the final redirect URL here.".to_owned()),
        });

        let result = wait_for_callback_or_manual_input(
            interaction,
            callback.as_ref(),
            "Complete login in your browser, or paste the authorization code / redirect URL here:",
            REDIRECT_URI,
        )
        .await?;
        let mut state = pkce.verifier.clone();
        let code = match result {
            CallbackOrManual::Callback { value } => Some(value),
            CallbackOrManual::Manual { input } => {
                let parsed = parse_authorization_input(&input);
                if parsed.state.as_ref().is_some_and(|parsed_state| {
                    !parsed_state.is_empty() && *parsed_state != pkce.verifier
                }) {
                    return Err(js_error("OAuth state mismatch"));
                }
                if let Some(parsed_state) = parsed.state {
                    state = parsed_state;
                }
                parsed.code
            }
        };

        let Some(code) = code.filter(|code| !code.is_empty()) else {
            return Err(js_error("Missing authorization code"));
        };
        interaction.notify(AuthEvent::Progress {
            message: "Exchanging authorization code for tokens...".to_owned(),
        });
        exchange_authorization_code(&code, &state, &pkce.verifier, REDIRECT_URI, &interaction.signal).await
    }
    .await;
    if let Some(callback) = &callback {
        callback.close();
    }
    result
}

async fn login_anthropic_copy_code(
    interaction: &ProviderAuthInteraction,
) -> Result<OAuthCredential, Thrown> {
    let pkce = generate_pkce()?;
    interaction.notify(AuthEvent::AuthUrl {
        url: authorize_url(&pkce.challenge, &pkce.verifier, COPY_CODE_REDIRECT_URI),
        instructions: Some(
            "Complete login in your browser, then copy the code Anthropic shows and paste it here."
                .to_owned(),
        ),
    });

    let input = interaction
        .prompt(AuthPrompt {
            signal: Some(interaction.signal.clone()),
            kind: AuthPromptKind::ManualCode {
                message: "Paste the code Anthropic shows after you sign in:".to_owned(),
                placeholder: Some("code#state".to_owned()),
            },
        })
        .await?;
    let parsed = parse_authorization_input(&input);
    if parsed
        .state
        .as_ref()
        .is_some_and(|state| !state.is_empty() && *state != pkce.verifier)
    {
        return Err(js_error("OAuth state mismatch"));
    }
    let Some(code) = parsed.code.filter(|code| !code.is_empty()) else {
        return Err(js_error("Missing authorization code"));
    };
    interaction.notify(AuthEvent::Progress {
        message: "Exchanging authorization code for tokens...".to_owned(),
    });
    let state = parsed.state.unwrap_or_else(|| pkce.verifier.clone());
    exchange_authorization_code(
        &code,
        &state,
        &pkce.verifier,
        COPY_CODE_REDIRECT_URI,
        &interaction.signal,
    )
    .await
}

/// Refresh Anthropic OAuth token.
async fn refresh_anthropic_token(
    refresh_token: &str,
    signal: &AbortSignal,
) -> Result<OAuthCredential, Thrown> {
    let body = serde_json::json!({
        "grant_type": "refresh_token",
        "client_id": *CLIENT_ID,
        "refresh_token": refresh_token,
    });
    let response_body = post_json(TOKEN_URL, &body, signal).await.map_err(|error| {
        js_error(format!(
            "Anthropic token refresh request failed. url={TOKEN_URL}; details={}",
            thrown_details(&error)
        ))
    })?;

    let data: TokenData = serde_json::from_str(&response_body).map_err(|error| {
        js_error(format!(
            "Anthropic token refresh returned invalid JSON. url={TOKEN_URL}; body={response_body}; details=SyntaxError: {error}"
        ))
    })?;
    Ok(credential_from(&data))
}

struct AnthropicOAuth;

impl OAuthAuth for AnthropicOAuth {
    fn name(&self) -> &'static str {
        "Anthropic (Claude Pro/Max)"
    }

    fn is_subscription(&self) -> Option<bool> {
        Some(true)
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        _options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move {
            let method = interaction
                .prompt(AuthPrompt::new(AuthPromptKind::Select {
                    message: "Select Anthropic login method:".to_owned(),
                    options: vec![
                        AuthSelectOption::new(
                            ANTHROPIC_BROWSER_LOGIN_METHOD,
                            "Browser login (default)",
                        ),
                        AuthSelectOption::new(
                            ANTHROPIC_COPY_CODE_LOGIN_METHOD,
                            "Copy code login (headless)",
                        ),
                    ],
                }))
                .await?;

            if method == ANTHROPIC_COPY_CODE_LOGIN_METHOD {
                return login_anthropic_copy_code(&interaction).await;
            }
            if method != ANTHROPIC_BROWSER_LOGIN_METHOD {
                return Err(js_error(format!(
                    "Unknown Anthropic login method: {method}"
                )));
            }
            login_anthropic(&interaction).await
        })
    }

    fn refresh(
        &self,
        credential: OAuthCredential,
        signal: AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { refresh_anthropic_token(&credential.refresh, &signal).await })
    }

    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        Box::pin(async move { Ok(api_key_auth(&credential.access)) })
    }
}

/// The Anthropic (Claude Pro/Max) OAuth flow (`anthropicOAuth`).
#[must_use]
pub fn anthropic_oauth() -> Arc<dyn OAuthAuth> {
    shared(AnthropicOAuth)
}

#[cfg(test)]
#[path = "anthropic_tests.rs"]
mod tests;
