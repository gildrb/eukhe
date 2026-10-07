//! `OpenAI` Responses API token sharing through Sign in with `ChatGPT`. Port of
//! `auth/oauth/openai-chatgpt.ts`.
//!
//! This public-client flow uses no client secret and sends the resulting user
//! access token directly to api.openai.com.

use std::sync::{Arc, LazyLock};

use eukhe_chord::context::{AbortController, AbortSignal};
use futures::future::BoxFuture;
use serde_json::Value;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::watch;
use tokio_util::sync::CancellationToken;

use super::callback_server::{query_param, read_request_head, send_html, ClosableListener};
use super::http::{fetch, form_urlencode, FetchRequest};
use super::pkce::{base64url_encode, generate_pkce, random_bytes};
use super::{api_key_auth, shared};
use crate::auth::errors::{date_now, js_error};
use crate::auth::types::{
    AuthEvent, AuthPrompt, AuthPromptKind, LoginOptions, ModelAuth, OAuthAuth, OAuthCredential,
    ProviderAuthInteraction,
};
use crate::utils::diagnostics::Thrown;
use crate::utils::oauth_page::{oauth_error_html, oauth_success_html};
use crate::utils::provider_env::get_provider_env_value;

/// Every login registers a new client with this ID; `OpenAI` returns the issued
/// client ID in the callback.
const DYNAMIC_CLIENT_ID: &str = "dynamic_agent_client";
const AGENT_NAME_HINT: &str = "Pi";
const AUTHORIZE_URL: &str = "https://auth.openai.com/api/accounts/authorize";
const TOKEN_URL: &str = "https://auth.openai.com/api/accounts/oauth/token";
const RESOURCE: &str = "https://api.openai.com/v1";
static CALLBACK_HOST: LazyLock<String> = LazyLock::new(|| {
    get_provider_env_value("PI_OAUTH_CALLBACK_HOST", None).unwrap_or_else(|| "127.0.0.1".to_owned())
});
const CALLBACK_PORT: u16 = 1455;
const CALLBACK_PATH: &str = "/auth/callback";
const REDIRECT_URI: &str = "http://127.0.0.1:1455/auth/callback";
const DIRECT_TOKEN_SCOPE: &str = "chatgpt.tokens.use.direct";
const SCOPE: &str = "openid profile email offline_access resource.invoke chatgpt.tokens.use.direct";
/// Refresh this long before the real expiry so a request never starts with a
/// token about to expire.
const EXPIRY_MARGIN_MS: f64 = 3.0 * 60.0 * 1000.0;

#[derive(Debug, Clone)]
struct AuthorizationResult {
    code: String,
    client_id: String,
}

type CallbackResult = Option<Result<AuthorizationResult, Thrown>>;

struct CallbackServer {
    result: watch::Receiver<CallbackResult>,
    /// Drops every open connection (`closeAllConnections()`).
    shutdown: CancellationToken,
    listener: Arc<ClosableListener>,
}

impl CallbackServer {
    async fn result(&mut self) -> Result<AuthorizationResult, Thrown> {
        loop {
            if let Some(result) = self.result.borrow_and_update().clone() {
                return result;
            }
            if self.result.changed().await.is_err() {
                return Err(js_error("OAuth callback server closed"));
            }
        }
    }
}

fn random_value() -> Result<String, Thrown> {
    Ok(base64url_encode(&random_bytes::<32>()?))
}

fn authorization_result_from_callback(
    url: &url::Url,
    expected_state: &str,
) -> Result<AuthorizationResult, Thrown> {
    let Some(code) = query_param(url, "code").filter(|code| !code.is_empty()) else {
        return Err(js_error("Missing authorization code"));
    };
    let Some(state) = query_param(url, "state").filter(|state| !state.is_empty()) else {
        return Err(js_error("Missing OAuth state"));
    };
    if state != expected_state {
        return Err(js_error("OAuth state mismatch"));
    }
    let client_id = query_param(url, "client_id")
        .map(|client_id| client_id.trim().to_owned())
        .filter(|client_id| !client_id.is_empty())
        .ok_or_else(|| {
            js_error("OpenAI OAuth registration callback did not contain an issued client ID")
        })?;
    Ok(AuthorizationResult { code, client_id })
}

fn authorization_result_from_manual_input(
    input: &str,
    expected_state: &str,
) -> Result<AuthorizationResult, Thrown> {
    let url = url::Url::parse(input.trim())
        .map_err(|_| js_error("Paste the full callback URL from the browser"))?;
    let expected = url::Url::parse(REDIRECT_URI).map_err(|error| js_error(error.to_string()))?;
    if url.origin() != expected.origin() || url.path() != expected.path() {
        return Err(js_error(format!(
            "The pasted callback URL must start with {REDIRECT_URI}"
        )));
    }
    if let Some(error) = query_param(&url, "error").filter(|error| !error.is_empty()) {
        return Err(js_error(format!("ChatGPT authorization failed: {error}")));
    }
    authorization_result_from_callback(&url, expected_state)
}

async fn send_page(stream: &mut TcpStream, status: u16, body: &str) {
    send_html(
        stream,
        status,
        &[("Content-Type", "text/html; charset=utf-8")],
        body,
    )
    .await;
}

fn settle(sender: &watch::Sender<CallbackResult>, result: Result<AuthorizationResult, Thrown>) {
    sender.send_if_modified(|current| {
        if current.is_some() {
            return false;
        }
        *current = Some(result);
        true
    });
}

async fn handle_connection(
    mut stream: TcpStream,
    expected_state: Arc<str>,
    sender: watch::Sender<CallbackResult>,
) {
    let Some(head) = read_request_head(&mut stream).await else {
        return;
    };
    let Ok(url) = url::Url::parse(REDIRECT_URI).and_then(|base| base.join(&head.target)) else {
        send_page(
            &mut stream,
            500,
            &oauth_error_html("Internal error while processing the callback.", None),
        )
        .await;
        return;
    };
    if url.path() != CALLBACK_PATH {
        send_page(
            &mut stream,
            404,
            &oauth_error_html("Callback route not found.", None),
        )
        .await;
        return;
    }

    if let Some(error) = query_param(&url, "error").filter(|error| !error.is_empty()) {
        send_page(
            &mut stream,
            400,
            &oauth_error_html(
                "ChatGPT was not connected.",
                Some(&format!("Error: {error}")),
            ),
        )
        .await;
        settle(
            &sender,
            Err(js_error(format!("ChatGPT authorization failed: {error}"))),
        );
        return;
    }

    match authorization_result_from_callback(&url, &expected_state) {
        Ok(result) => {
            send_page(
                &mut stream,
                200,
                &oauth_success_html("ChatGPT authentication completed. You can close this window."),
            )
            .await;
            settle(&sender, Ok(result));
        }
        Err(error) => {
            send_page(
                &mut stream,
                400,
                &oauth_error_html(&error.to_string(), None),
            )
            .await;
        }
    }
}

async fn start_callback_server(expected_state: &str) -> Result<CallbackServer, Thrown> {
    let listener = TcpListener::bind((CALLBACK_HOST.as_str(), CALLBACK_PORT))
        .await
        .map_err(|error| -> Thrown { Arc::new(error) })?;
    let listener = Arc::new(ClosableListener::new(listener));
    let (sender, result) = watch::channel(None);
    let shutdown = CancellationToken::new();
    let accept_listener = Arc::clone(&listener);
    let expected_state: Arc<str> = Arc::from(expected_state);
    let accept_shutdown = shutdown.clone();
    tokio::spawn(async move {
        loop {
            tokio::select! {
                () = accept_shutdown.cancelled() => return,
                accepted = accept_listener.accept() => match accepted {
                    None => return,
                    Some(Ok(stream)) => {
                        let connection_shutdown = accept_shutdown.clone();
                        let state = Arc::clone(&expected_state);
                        let sender = sender.clone();
                        tokio::spawn(async move {
                            tokio::select! {
                                () = connection_shutdown.cancelled() => {}
                                () = handle_connection(stream, state, sender) => {}
                            }
                        });
                    }
                    Some(Err(error)) => settle(&sender, Err(Arc::new(error))),
                },
            }
        }
    });
    Ok(CallbackServer {
        result,
        shutdown,
        listener,
    })
}

async fn request_token(fields: &[(&str, &str)], signal: &AbortSignal) -> Result<Value, Thrown> {
    let response = fetch(
        FetchRequest::post(TOKEN_URL)
            .header("accept", "application/json")
            .header("content-type", "application/x-www-form-urlencoded")
            .form(fields),
        Some(signal),
    )
    .await?;
    if !response.ok() {
        let text = if response.body.is_empty() {
            &response.status_text
        } else {
            &response.body
        };
        return Err(js_error(format!(
            "OpenAI OAuth token request failed ({}): {text}",
            response.status
        )));
    }
    let data = response.json()?;
    if !data.is_object() {
        return Err(js_error("OpenAI OAuth token response must be an object"));
    }
    Ok(data)
}

fn require_token_string<'a>(token: &'a Value, field: &str) -> Result<&'a str, Thrown> {
    token
        .get(field)
        .and_then(Value::as_str)
        .filter(|value| !value.trim().is_empty())
        .ok_or_else(|| js_error(format!("OpenAI OAuth token response has invalid {field}")))
}

fn credential_from_token_response(
    token: &Value,
    client_id: &str,
) -> Result<OAuthCredential, Thrown> {
    let access = require_token_string(token, "access_token")?;
    let refresh = require_token_string(token, "refresh_token")?;
    let scope = require_token_string(token, "scope")?;
    let expires_in = token
        .get("expires_in")
        .and_then(Value::as_f64)
        .filter(|value| value.is_finite() && *value > 0.0)
        .ok_or_else(|| js_error("OpenAI OAuth token response has invalid expires_in"))?;
    let scopes: Vec<Value> = scope
        .split_whitespace()
        .map(|scope| Value::String(scope.to_owned()))
        .collect();
    if !scopes.iter().any(|scope| scope == DIRECT_TOKEN_SCOPE) {
        return Err(js_error(format!(
            "OpenAI OAuth grant did not include {DIRECT_TOKEN_SCOPE}"
        )));
    }
    Ok(OAuthCredential::new(
        refresh,
        access,
        date_now() + expires_in * 1000.0 - EXPIRY_MARGIN_MS,
    )
    .with_extra("clientId", Value::String(client_id.to_owned()))
    .with_extra("scopes", Value::Array(scopes)))
}

async fn exchange_authorization_code(
    code: &str,
    verifier: &str,
    client_id: &str,
    signal: &AbortSignal,
) -> Result<OAuthCredential, Thrown> {
    let token = request_token(
        &[
            ("grant_type", "authorization_code"),
            ("client_id", client_id),
            ("code", code),
            ("code_verifier", verifier),
            ("redirect_uri", REDIRECT_URI),
            ("resource", RESOURCE),
        ],
        signal,
    )
    .await?;
    // Pi does not use the ID token to identify the user or read profile data.
    // Keep the presence check as part of the token-response contract.
    let has_id_token = token
        .get("id_token")
        .and_then(Value::as_str)
        .is_some_and(|id_token| !id_token.trim().is_empty());
    if !has_id_token {
        return Err(js_error(
            "OpenAI OAuth token response did not contain an ID token",
        ));
    }
    credential_from_token_response(&token, client_id)
}

async fn refresh_access_token(
    credential: &OAuthCredential,
    signal: &AbortSignal,
) -> Result<OAuthCredential, Thrown> {
    let client_id = credential
        .extra_str("clientId")
        .filter(|client_id| !client_id.trim().is_empty())
        .ok_or_else(|| {
            js_error(
                "Stored OpenAI OAuth credential does not contain an issued client ID; reconnect ChatGPT",
            )
        })?;
    let token = request_token(
        &[
            ("grant_type", "refresh_token"),
            ("client_id", client_id),
            ("refresh_token", &credential.refresh),
            ("resource", RESOURCE),
        ],
        signal,
    )
    .await?;
    credential_from_token_response(&token, client_id)
}

/// `/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i`.
fn is_uuid(value: &str) -> bool {
    let groups: Vec<&str> = value.split('-').collect();
    groups.len() == 5
        && groups.iter().zip([8, 4, 4, 4, 12]).all(|(group, len)| {
            group.len() == len && group.bytes().all(|byte| byte.is_ascii_hexdigit())
        })
}

/// `OpenAI` identifies each installation ("agent host") by a stable URI such as
/// `urn:uuid:<uuid>`.
fn agent_host_id(device_id: Option<String>) -> Result<String, Thrown> {
    match device_id {
        Some(device_id) if is_uuid(&device_id) => {
            Ok(format!("urn:uuid:{}", device_id.to_lowercase()))
        }
        _ => Err(js_error(
            "Sign in with ChatGPT requires a device ID (UUID) for this installation",
        )),
    }
}

async fn login_openai_chatgpt(
    interaction: &ProviderAuthInteraction,
    options: Option<LoginOptions>,
) -> Result<OAuthCredential, Thrown> {
    let device_id = options
        .and_then(|options| options.get_device_id)
        .map(|get_device_id| get_device_id());
    let host_id = agent_host_id(device_id)?;
    let pkce = generate_pkce()?;
    let state = random_value()?;
    let nonce = random_value()?;
    // Without this server, the browser's callback would reach whatever else holds the port (another
    // pending login or the Codex CLI), which rejects it as a state mismatch. Fail with a clear error instead.
    let mut callback = start_callback_server(&state).await.map_err(|error| {
        let in_use = error
            .downcast_ref::<std::io::Error>()
            .is_some_and(|io| io.kind() == std::io::ErrorKind::AddrInUse);
        if in_use {
            js_error(format!("Port {CALLBACK_PORT} is in use, probably by an unfinished login in another pi session or by the Codex CLI. Cancel that login and try again."))
        } else {
            error
        }
    })?;

    let query = form_urlencode(&[
        ("client_id", DYNAMIC_CLIENT_ID),
        ("agent_name_hint", AGENT_NAME_HINT),
        ("ext_agent_host_id", &host_id),
        ("response_type", "code"),
        ("redirect_uri", REDIRECT_URI),
        ("resource", RESOURCE),
        ("scope", SCOPE),
        ("state", &state),
        ("code_challenge", &pkce.challenge),
        ("code_challenge_method", "S256"),
        ("nonce", &nonce),
    ]);
    interaction.notify(AuthEvent::AuthUrl {
        url: format!("{AUTHORIZE_URL}?{query}"),
        instructions: Some("Complete sign-in in your browser. If the callback does not complete, paste the final redirect URL here.".to_owned()),
    });

    let manual_abort = AbortController::new();
    let manual_code = async {
        let input = interaction
            .prompt(AuthPrompt {
                signal: Some(AbortSignal::any(&[
                    manual_abort.signal(),
                    interaction.signal.clone(),
                ])),
                kind: AuthPromptKind::ManualCode {
                    message:
                        "Complete login in your browser, or paste the final redirect URL here:"
                            .to_owned(),
                    placeholder: Some(REDIRECT_URI.to_owned()),
                },
            })
            .await?;
        authorization_result_from_manual_input(&input, &state)
    };

    let result = async {
        let result = tokio::select! {
            result = callback.result() => result,
            result = manual_code => result,
        }?;
        interaction.notify(AuthEvent::Progress {
            message: "Exchanging authorization code for tokens...".to_owned(),
        });
        exchange_authorization_code(
            &result.code,
            &pkce.verifier,
            &result.client_id,
            &interaction.signal,
        )
        .await
    }
    .await;

    manual_abort.abort(None);
    // Close the listener and every open connection: browsers open spare
    // connections ahead of time, and a later login's callback could otherwise
    // arrive on one still attached to this server and be rejected with
    // "OAuth state mismatch".
    callback.listener.close();
    callback.shutdown.cancel();
    result.map_err(|error| {
        if interaction.signal.aborted() {
            js_error("Login cancelled")
        } else {
            error
        }
    })
}

struct OpenAIChatGPTOAuth;

impl OAuthAuth for OpenAIChatGPTOAuth {
    fn name(&self) -> &'static str {
        "OpenAI (ChatGPT subscription)"
    }

    fn is_subscription(&self) -> Option<bool> {
        Some(true)
    }

    fn login_label(&self) -> Option<&'static str> {
        Some("Sign in with ChatGPT")
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { login_openai_chatgpt(&interaction, options).await })
    }

    fn refresh(
        &self,
        credential: OAuthCredential,
        signal: AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { refresh_access_token(&credential, &signal).await })
    }

    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        Box::pin(async move { Ok(api_key_auth(&credential.access)) })
    }
}

/// The Sign in with `ChatGPT` flow (`openaiChatGPTOAuth`).
#[must_use]
pub fn openai_chatgpt_oauth() -> Arc<dyn OAuthAuth> {
    shared(OpenAIChatGPTOAuth)
}

#[cfg(test)]
#[path = "openai_chatgpt_tests.rs"]
mod tests;
