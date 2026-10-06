//! The Anthropic (Claude Pro/Max) OAuth flow — the port of
//! `packages/ai/src/utils/oauth/anthropic.ts` (+ `pkce.ts`): the PKCE
//! authorization request against the client registration, the
//! localhost callback server raced against the manual paste, the
//! JSON token exchange, and the token refresh. The credentials the
//! flow returns carry the TS shape (`access`, `refresh`, `expires`)
//! and persist under the provider id `anthropic`.
//!
//! The TS flow doubles its PKCE verifier as the OAuth `state` (the
//! redirect echoes the verifier and the exchange posts it back) —
//! kept verbatim for wire parity.
//!
//! Cancellation follows the fleet's cooperative pattern (#2770): the
//! driving surface marks a shared flag when it exits; the flow
//! checks it between the race's poll steps and before its network
//! steps, so an exited surface never receives a completed login.
//!
//! Remote logins: the browser on another machine lands on a failing
//! localhost page whose address the user pastes. A rejected paste or a
//! failed exchange re-prompts on the same panel with the same verifier
//! while the callback server keeps waiting; only a cancel ends the
//! login. A busy callback port leaves the paste as the only path.

use std::pin::pin;
use std::time::Duration;

use serde_json::json;
use url::Url;

use super::anthropic_callback::{
    AnthropicCallbackServer, CallbackCode, CALLBACK_PORT, REDIRECT_URI,
};
use super::pkce::generate_pkce;
use super::provider_http::{ProviderHttp, ProviderHttpMethod, ProviderHttpRequest};
use super::redirect_input::{exchange_retry_notice, parse_redirect_input, port_busy_line};
use super::response_snippet::response_snippet;
use super::types::{OAuthLoginUi, OAuthPrompt};

/// The client registration the TS flow ships (TS stores the id
/// base64-encoded; the decoded value is the wire value).
pub const ANTHROPIC_CLIENT_ID: &str = "9d1c250a-e61b-44d9-88ed-5944d1962f5e";
/// TS `AUTHORIZE_URL`.
const AUTHORIZE_URL: &str = "https://claude.ai/oauth/authorize";
/// TS `TOKEN_URL`.
const TOKEN_URL: &str = "https://platform.claude.com/v1/oauth/token";
/// `EUKHE_ANTHROPIC_TOKEN_URL`: the token endpoint override end-to-end
/// tests point at a local stub; unset or empty means [`TOKEN_URL`]. The
/// authorization-code exchange and the refresh both read it.
const TOKEN_URL_ENV: &str = "EUKHE_ANTHROPIC_TOKEN_URL";
/// TS `SCOPES`.
const SCOPES: &str = "org:create_api_key user:profile user:inference user:sessions:claude_code user:mcp_servers user:file_upload";
/// One token request's bound (TS `AbortSignal.timeout(30_000)`).
pub const DEFAULT_TOKEN_TIMEOUT_MS: u64 = 30_000;
/// The credential's expiry skew (TS `5 * 60 * 1000`).
const EXPIRY_SKEW_MS: i64 = 5 * 60 * 1000;
/// The refresh grant's request bound: the refresh runs under the auth
/// store's file lock, which a peer declares stale after 10 seconds — the
/// request must fit inside that window so a slow endpoint fails the
/// refresh (kept for a retry) instead of holding the lock past its
/// staleness.
pub const REFRESH_TIMEOUT_MS: u64 = 8_000;
/// The `onAuth` instructions line: the remote-login steps spelled out (a
/// browser on another machine cannot reach the localhost callback).
const AUTH_INSTRUCTIONS: &str = "Complete login in your browser. On another machine, the browser ends on a localhost page that fails to load: copy that page's full address and paste it below.";
/// TS the `onPrompt` fallback line.
const PROMPT_MESSAGE: &str = "Paste the authorization code or full redirect URL:";
/// The cancel error the driving surface maps to the silent cancelled
/// outcome (TS the dialog throws the same text; `auth-flows.ts`
/// matches it).
pub const LOGIN_CANCELLED: &str = "Login cancelled";
/// The race's poll step: how often the loop re-checks the cooperative
/// cancel flag (#2770 — the flag is checked between poll steps).
const CANCEL_POLL_INTERVAL: Duration = Duration::from_millis(250);

/// The credentials the flow returns and persists (TS
/// `OAuthCredentials` for the Anthropic provider).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnthropicCredentials {
    pub access: String,
    pub refresh: String,
    /// Wall-clock epoch milliseconds (TS `Date.now() + expires_in *
    /// 1000 - 5 * 60 * 1000`).
    pub expires: i64,
}

/// Run the login (TS `loginAnthropic`): build the PKCE request, start
/// the callback server, present the URL, race the browser callback
/// against the manual paste, exchange the code, and return the
/// credentials to persist. The exchange always posts the registered
/// redirect (TS `redirectUriForExchange` is `REDIRECT_URI` on every
/// path).
///
/// With a paste surface, a rejected paste (no code, another login's
/// state, an OAuth error) and a failed exchange are reported through
/// [`OAuthLoginUi::on_input_rejected`] and the paste is asked again;
/// the browser callback can still win meanwhile.
///
/// # Errors
///
/// Returns an error when the surface cancelled the login
/// ([`LOGIN_CANCELLED`]); without a paste surface also when the prompt
/// answer is rejected or the token exchange fails.
pub async fn login_anthropic(
    http: &dyn ProviderHttp,
    ui: &dyn OAuthLoginUi,
) -> Result<AnthropicCredentials, String> {
    // An exited surface never starts: no callback port bind, no browser
    // launch (the #2770 flag is the seam).
    if ui.is_cancelled() {
        return Err(LOGIN_CANCELLED.to_string());
    }
    let (verifier, challenge) = generate_pkce();
    let server = AnthropicCallbackServer::start(&verifier);
    ui.on_auth(
        &authorization_url(&challenge, &verifier),
        Some(AUTH_INSTRUCTIONS),
    );
    let server = server
        .inspect_err(|detail| ui.on_progress(&port_busy_line(CALLBACK_PORT, detail)))
        .ok();
    let mut callback_live = server.is_some();
    let wait_once = || async {
        match &server {
            Some(server) => server.wait_for_code().await,
            None => None,
        }
    };
    let mut wait = pin!(wait_once());
    let mut manual = ui.on_manual_code_input();
    let paste_surface = manual.is_some();
    let mut tick = tokio::time::interval(CANCEL_POLL_INTERVAL);
    loop {
        let code = loop {
            if ui.is_cancelled() {
                return Err(LOGIN_CANCELLED.to_string());
            }
            if !callback_live && manual.is_none() {
                // The fallback prompt (TS `onPrompt`): no browser hand-back
                // and no paste surface.
                let answer = ui
                    .on_prompt(&OAuthPrompt {
                        message: PROMPT_MESSAGE.to_string(),
                        placeholder: Some(REDIRECT_URI.to_string()),
                        allow_empty: false,
                    })
                    .await;
                let input = answer.ok_or_else(|| LOGIN_CANCELLED.to_string())?;
                let accepted = parse_redirect_input(&input)
                    .and_then(|pasted| pasted.verify_state(&verifier))
                    .map_err(|rejected| rejected.to_string())?;
                break CallbackCode {
                    code: accepted.code,
                    state: accepted.state,
                };
            }
            let step = tokio::select! {
                _ = tick.tick() => RaceStep::Tick,
                settled = &mut wait, if callback_live => RaceStep::Callback(settled),
                answer = async {
                    match manual.as_mut() {
                        Some(field) => field.await,
                        None => std::future::pending().await,
                    }
                }, if manual.is_some() => RaceStep::Paste(answer),
            };
            match step {
                RaceStep::Tick => {}
                // A settled callback (the server validated the state); the
                // wait re-arms for a later redirect.
                RaceStep::Callback(Some(code)) => {
                    wait.set(wait_once());
                    break code;
                }
                // A settled-empty wait (a cancelled one): the paste goes on.
                RaceStep::Callback(None) => callback_live = false,
                RaceStep::Paste(None) => return Err(LOGIN_CANCELLED.to_string()),
                RaceStep::Paste(Some(input)) => {
                    match parse_redirect_input(&input)
                        .and_then(|pasted| pasted.verify_state(&verifier))
                    {
                        Ok(accepted) => {
                            break CallbackCode {
                                code: accepted.code,
                                state: accepted.state,
                            };
                        }
                        Err(rejected) => {
                            ui.on_input_rejected(&rejected.to_string());
                            manual = ui.on_manual_code_input();
                        }
                    }
                }
            }
        };
        // The callback won: the pending paste prompt goes away.
        drop(manual.take());
        if ui.is_cancelled() {
            return Err(LOGIN_CANCELLED.to_string());
        }
        ui.on_progress("Exchanging authorization code for tokens...");
        match exchange_authorization_code(http, &code, &verifier).await {
            Ok(credentials) => return Ok(credentials),
            Err(error) if paste_surface => {
                ui.on_input_rejected(&exchange_retry_notice(&error));
                manual = ui.on_manual_code_input();
            }
            Err(error) => return Err(error),
        }
    }
}

/// One step of the race: the cancel tick, the browser callback, or the
/// paste answer.
enum RaceStep {
    Tick,
    /// The callback wait settled: the code, or `None` when it settled
    /// empty (a cancelled wait).
    Callback(Option<CallbackCode>),
    /// The paste answered: the input, or `None` when cancelled.
    Paste(Option<String>),
}

/// Refresh an expired credential (TS `refreshAnthropicToken`).
///
/// # Errors
///
/// Returns an error when the token refresh fails.
pub async fn refresh_anthropic_token(
    http: &dyn ProviderHttp,
    refresh_token: &str,
) -> Result<AnthropicCredentials, String> {
    let body = json!({
        "grant_type": "refresh_token",
        "client_id": ANTHROPIC_CLIENT_ID,
        "refresh_token": refresh_token,
    })
    .to_string();
    // The refresh runs under the auth store's lock: the request fits
    // inside the lock's staleness window (REFRESH_TIMEOUT_MS).
    let token = json_token_request(
        http,
        &token_url(),
        &body,
        "Anthropic token refresh",
        REFRESH_TIMEOUT_MS,
        "",
    )
    .await?;
    Ok(credentials_from(token))
}

/// The authorization URL (TS the `authParams` block in TS order: the
/// code flag, the registration, the challenge, and the state — which
/// is the PKCE verifier).
fn authorization_url(challenge: &str, verifier: &str) -> String {
    let mut url = Url::parse(AUTHORIZE_URL).expect("the authorize url parses");
    for (name, value) in [
        ("code", "true"),
        ("client_id", ANTHROPIC_CLIENT_ID),
        ("response_type", "code"),
        ("redirect_uri", REDIRECT_URI),
        ("scope", SCOPES),
        ("code_challenge", challenge),
        ("code_challenge_method", "S256"),
        ("state", verifier),
    ] {
        url.query_pairs_mut().append_pair(name, value);
    }
    url.to_string()
}

/// The token endpoint: the [`TOKEN_URL_ENV`] override when set and
/// non-empty, else [`TOKEN_URL`].
fn token_url() -> String {
    std::env::var(TOKEN_URL_ENV)
        .ok()
        .filter(|url| !url.is_empty())
        .unwrap_or_else(|| TOKEN_URL.to_string())
}

/// One token response (TS the `tokenData` shape of the exchange and
/// the refresh).
struct TokenResponse {
    access: String,
    refresh: String,
    expires_in: i64,
}

/// The credential the response builds (TS the expires arithmetic).
fn credentials_from(token: TokenResponse) -> AnthropicCredentials {
    // Saturating: a hostile `expires_in` must not overflow the sum (the
    // NaN/inf gate already answered the missing-fields error).
    AnthropicCredentials {
        access: token.access,
        refresh: token.refresh,
        expires: now_ms()
            .saturating_add(token.expires_in.saturating_mul(1000))
            .saturating_sub(EXPIRY_SKEW_MS),
    }
}

/// Wall-clock milliseconds since the epoch (the `expires` convention).
// Epoch millis fit i64 for ~292 million years; the u128 duration's millis are the i64 convention here.
#[allow(clippy::cast_possible_truncation)]
fn now_ms() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(i64::MAX, |elapsed| elapsed.as_millis() as i64)
}

/// TS `exchangeAuthorizationCode`: the authorization-code grant with
/// the PKCE verifier, the echoed state, and the registered redirect —
/// a JSON body (the Anthropic endpoint's shape, unlike the form
/// bodies the other providers use).
async fn exchange_authorization_code(
    http: &dyn ProviderHttp,
    code: &CallbackCode,
    verifier: &str,
) -> Result<AnthropicCredentials, String> {
    let body = json!({
        "grant_type": "authorization_code",
        "client_id": ANTHROPIC_CLIENT_ID,
        "code": code.code,
        "state": code.state,
        "redirect_uri": REDIRECT_URI,
        "code_verifier": verifier,
    })
    .to_string();
    let token = json_token_request(
        http,
        &token_url(),
        &body,
        "Token exchange",
        DEFAULT_TOKEN_TIMEOUT_MS,
        &format!(" redirect_uri={REDIRECT_URI}; response_type=authorization_code;"),
    )
    .await?;
    Ok(credentials_from(token))
}

/// One JSON token POST through the TS error wrappers: the transport
/// failure and the failed status wrap the request error (`TS
/// formatErrorDetails`' `Error: <message>` head), the failed JSON
/// parse wraps the invalid-JSON error, and a missing field is this
/// port's explicit error where TS would persist an unusable
/// credential. The two TS call sites differ only in the wrapper
/// prefix (`Anthropic token refresh …` vs `Token exchange …`).
async fn json_token_request(
    http: &dyn ProviderHttp,
    url: &str,
    body: &str,
    label: &str,
    timeout_ms: u64,
    wire_context: &str,
) -> Result<TokenResponse, String> {
    let response = post_json(http, url, body, timeout_ms)
        .await
        .map_err(|message| {
            format!("{label} request failed. url={url};{wire_context} details={message}")
        })?;
    if !response.ok() {
        // TS `postJson` throws and the caller wraps the thrown error
        // (`formatErrorDetails` prints the Error head + message); the
        // body is bounded to one line.
        return Err(format!(
            "{label} request failed. url={url};{wire_context} details=Error: HTTP request failed. status={}; url={url}; body={}",
            response.status,
            response_snippet(&response.body)
        ));
    }
    let json: serde_json::Value = serde_json::from_str(&response.body).map_err(|error| {
        format!(
            "{label} returned invalid JSON. url={url}; status={}; body={}; details=Error: {error}",
            response.status,
            response_snippet(&response.body)
        )
    })?;
    let missing_fields = || {
        format!(
            "{label} response missing fields: {}",
            response_snippet(&json.to_string())
        )
    };
    let access = json
        .get("access_token")
        .and_then(serde_json::Value::as_str)
        .filter(|token| !token.is_empty())
        .ok_or_else(missing_fields)?
        .to_string();
    let refresh = json
        .get("refresh_token")
        .and_then(serde_json::Value::as_str)
        .filter(|token| !token.is_empty())
        .ok_or_else(missing_fields)?
        .to_string();
    let expires_in = json
        .get("expires_in")
        .and_then(serde_json::Value::as_f64)
        .filter(|seconds| seconds.is_finite() && *seconds > 0.0)
        .ok_or_else(missing_fields)?;
    // The wire's expires_in is an integer second count read through JSON f64; the i64 truncation is the port's convention.
    #[allow(clippy::cast_possible_truncation)]
    let expires_in_seconds = expires_in as i64;
    Ok(TokenResponse {
        access,
        refresh,
        expires_in: expires_in_seconds,
    })
}

/// TS `postJson`: the JSON-body POST with the request timeout bound.
async fn post_json(
    http: &dyn ProviderHttp,
    url: &str,
    body: &str,
    timeout_ms: u64,
) -> Result<super::provider_http::ProviderHttpResponse, String> {
    http.request(
        ProviderHttpRequest {
            method: ProviderHttpMethod::Post,
            url: url.to_string(),
            headers: vec![
                ("Content-Type".to_string(), "application/json".to_string()),
                ("Accept".to_string(), "application/json".to_string()),
            ],
            body: Some(body.to_string()),
            follow_redirects: true,
        },
        timeout_ms,
    )
    .await
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oauth::redirect_input::RedirectInputError;
    use crate::oauth::ProviderHttpResponse;
    use std::collections::{HashMap, VecDeque};
    use std::future::Future;
    use std::pin::Pin;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::{Arc, Mutex};
    use tokio::io::AsyncWriteExt as _;

    use super::super::anthropic_callback::{registered_port_stages, CALLBACK_PORT_LOCK};

    /// A scripted transport: url -> queued responses (the last one
    /// repeats), recording every posted body. Unknown urls fail the
    /// request (the TS suite throws on unexpected fetches).
    struct ScriptedHttp {
        responses: Mutex<HashMap<String, VecDeque<ProviderHttpResponse>>>,
        requests: Mutex<Vec<(String, String)>>,
    }

    impl ScriptedHttp {
        fn new(responses: Vec<(&str, u16, &str)>) -> Self {
            let mut queued: HashMap<String, VecDeque<ProviderHttpResponse>> = HashMap::new();
            for (url, status, body) in responses {
                queued
                    .entry(url.to_string())
                    .or_default()
                    .push_back(ProviderHttpResponse {
                        status,
                        body: body.to_string(),
                    });
            }
            ScriptedHttp {
                responses: Mutex::new(queued),
                requests: Mutex::new(Vec::new()),
            }
        }

        fn bodies(&self, url: &str) -> Vec<serde_json::Value> {
            self.requests
                .lock()
                .unwrap()
                .iter()
                .filter(|(seen, _)| seen == url)
                .map(|(_, body)| serde_json::from_str(body).expect("a JSON body"))
                .collect()
        }
    }

    impl ProviderHttp for ScriptedHttp {
        fn request(
            &self,
            request: ProviderHttpRequest,
            _timeout_ms: u64,
        ) -> Pin<Box<dyn Future<Output = Result<ProviderHttpResponse, String>> + Send + '_>>
        {
            self.requests.lock().unwrap().push((
                request.url.clone(),
                request.body.clone().unwrap_or_default(),
            ));
            let response = self
                .responses
                .lock()
                .unwrap()
                .get_mut(&request.url)
                .and_then(|queue| {
                    if queue.len() > 1 {
                        queue.pop_front()
                    } else {
                        queue.front().cloned()
                    }
                });
            Box::pin(
                async move { response.ok_or_else(|| format!("{} was not scripted", request.url)) },
            )
        }
    }

    /// One scripted paste or prompt answer: an immediate value
    /// (`Some`), an immediate cancel (`None`), a never-resolving field
    /// (its drop is counted: the flow dropped the prompt), or a paste
    /// built from the state the presented authorization URL carries
    /// (the address a remote browser lands on).
    enum ScriptedAnswer {
        Once(Option<String>),
        Pending,
        Redirect(fn(&str) -> String),
    }

    impl ScriptedAnswer {
        fn ready() -> Self {
            ScriptedAnswer::Once(None)
        }

        fn value(text: &str) -> Self {
            ScriptedAnswer::Once(Some(text.to_string()))
        }
    }

    /// Counts a dropped pending field.
    struct DropCounter(Arc<AtomicUsize>);

    impl Drop for DropCounter {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    /// The scripted login surface: the captured authorization URL, the
    /// queued pastes (one per mounted field; an exhausted queue cancels),
    /// the fallback prompt, the rejections, and the progress lines.
    struct ScriptedUi {
        auth_url: Mutex<Option<String>>,
        progress: Mutex<Vec<String>>,
        rejections: Mutex<Vec<String>>,
        pastes: Option<Mutex<VecDeque<ScriptedAnswer>>>,
        prompt: Option<ScriptedAnswer>,
        dropped_fields: Arc<AtomicUsize>,
        cancelled: Arc<AtomicBool>,
        cancel_on_auth: bool,
    }

    impl ScriptedUi {
        fn with_pastes(pastes: Vec<ScriptedAnswer>) -> Self {
            ScriptedUi {
                auth_url: Mutex::new(None),
                progress: Mutex::new(Vec::new()),
                rejections: Mutex::new(Vec::new()),
                pastes: Some(Mutex::new(pastes.into_iter().collect())),
                prompt: None,
                dropped_fields: Arc::new(AtomicUsize::new(0)),
                cancelled: Arc::new(AtomicBool::new(false)),
                cancel_on_auth: false,
            }
        }

        fn without_paste(prompt: ScriptedAnswer) -> Self {
            ScriptedUi {
                pastes: None,
                prompt: Some(prompt),
                ..ScriptedUi::with_pastes(Vec::new())
            }
        }

        fn rejections(&self) -> Vec<String> {
            self.rejections.lock().unwrap().clone()
        }

        fn has_progress(&self, prefix: &str) -> bool {
            self.progress
                .lock()
                .unwrap()
                .iter()
                .any(|line| line.starts_with(prefix))
        }

        /// The presented state (the PKCE verifier).
        fn state(&self) -> String {
            state_of(
                self.auth_url
                    .lock()
                    .unwrap()
                    .as_deref()
                    .expect("the url shows first"),
            )
        }

        /// The captured authorization URL (waits for the flow's
        /// `onAuth`).
        async fn captured_url(&self) -> String {
            let deadline = std::time::Instant::now() + Duration::from_secs(5);
            loop {
                if let Some(url) = self.auth_url.lock().unwrap().clone() {
                    return url;
                }
                assert!(
                    std::time::Instant::now() < deadline,
                    "the flow never presented its url"
                );
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        }

        fn future(
            &self,
            answer: &ScriptedAnswer,
        ) -> Pin<Box<dyn Future<Output = Option<String>> + Send>> {
            match answer {
                ScriptedAnswer::Once(value) => Box::pin(std::future::ready(value.clone())),
                ScriptedAnswer::Pending => {
                    let counter = DropCounter(Arc::clone(&self.dropped_fields));
                    Box::pin(async move {
                        let _counter = counter;
                        std::future::pending::<Option<String>>().await
                    })
                }
                ScriptedAnswer::Redirect(build) => {
                    Box::pin(std::future::ready(Some(build(&self.state()))))
                }
            }
        }
    }

    fn state_of(url: &str) -> String {
        url::Url::parse(url)
            .unwrap()
            .query_pairs()
            .find(|(key, _)| key == "state")
            .map(|(_, value)| value.to_string())
            .expect("the url carries a state")
    }

    impl OAuthLoginUi for ScriptedUi {
        fn on_auth(&self, url: &str, instructions: Option<&str>) {
            assert_eq!(
                instructions,
                Some(AUTH_INSTRUCTIONS),
                "the TS instructions line rides the auth url"
            );
            *self.auth_url.lock().unwrap() = Some(url.to_string());
            if self.cancel_on_auth {
                self.cancelled.store(true, Ordering::Relaxed);
            }
        }

        fn on_prompt(
            &self,
            prompt: &OAuthPrompt,
        ) -> Pin<Box<dyn Future<Output = Option<String>> + Send + '_>> {
            assert_eq!(prompt.message, PROMPT_MESSAGE);
            assert_eq!(prompt.placeholder.as_deref(), Some(REDIRECT_URI));
            match &self.prompt {
                Some(answer) => self.future(answer),
                None => Box::pin(std::future::pending()),
            }
        }

        fn on_progress(&self, message: &str) {
            self.progress.lock().unwrap().push(message.to_string());
        }

        fn on_manual_code_input(
            &self,
        ) -> Option<Pin<Box<dyn Future<Output = Option<String>> + Send + '_>>> {
            let pastes = self.pastes.as_ref()?;
            let answer = pastes
                .lock()
                .unwrap()
                .pop_front()
                .unwrap_or_else(ScriptedAnswer::ready);
            Some(self.future(&answer))
        }

        fn on_input_rejected(&self, reason: &str) {
            self.rejections.lock().unwrap().push(reason.to_string());
        }

        fn is_cancelled(&self) -> bool {
            self.cancelled.load(Ordering::Relaxed)
        }
    }

    const HAPPY_TOKEN: &str =
        r#"{"access_token":"the-access","refresh_token":"the-refresh","expires_in":3600}"#;

    /// The token endpoint answering one happy credential (3600s).
    fn token_http() -> ScriptedHttp {
        ScriptedHttp::new(vec![(TOKEN_URL, 200, HAPPY_TOKEN)])
    }

    /// The exchange body a login with `state` posts for `code`.
    fn grant(code: &str, state: &str) -> serde_json::Value {
        serde_json::json!({
            "grant_type": "authorization_code",
            "client_id": ANTHROPIC_CLIENT_ID,
            "code": code,
            "state": state,
            "redirect_uri": REDIRECT_URI,
            "code_verifier": state,
        })
    }

    /// The callback address a remote browser lands on.
    fn landed(state: &str) -> String {
        format!("http://localhost:53692/callback?code=the-code&state={state}")
    }

    /// Hold the registered port so the flow's own bind fails (`None`:
    /// the port is busy outside this test binary and cannot be staged).
    fn hold_registered_port() -> Option<std::net::TcpListener> {
        std::net::TcpListener::bind(("127.0.0.1", CALLBACK_PORT)).ok()
    }

    /// Drive the browser redirect into the flow's callback server.
    async fn browser_redirect(code: &str, state: &str) {
        let mut stream = tokio::net::TcpStream::connect(("127.0.0.1", CALLBACK_PORT))
            .await
            .expect("the flow's callback server accepts the redirect");
        stream
            .write_all(
                format!(
                    "GET /callback?code={code}&state={state} HTTP/1.1\r\nHost: localhost\r\n\r\n"
                )
                .as_bytes(),
            )
            .await
            .expect("the redirect writes");
    }

    #[tokio::test]
    async fn the_authorization_url_carries_the_ts_parameters() {
        let url = authorization_url("the-challenge", "the-verifier");
        let parsed = url::Url::parse(&url).unwrap();
        assert_eq!(parsed.host_str(), Some("claude.ai"));
        assert_eq!(parsed.path(), "/oauth/authorize");
        let param = |name: &str| {
            parsed
                .query_pairs()
                .find(|(key, _)| key == name)
                .map(|(_, value)| value.to_string())
                .unwrap_or_default()
        };
        assert_eq!(param("code"), "true");
        assert_eq!(param("client_id"), ANTHROPIC_CLIENT_ID);
        assert_eq!(param("response_type"), "code");
        assert_eq!(param("redirect_uri"), REDIRECT_URI);
        assert_eq!(param("scope"), SCOPES);
        assert_eq!(param("code_challenge"), "the-challenge");
        assert_eq!(param("code_challenge_method"), "S256");
        // TS doubles the PKCE verifier as the state.
        assert_eq!(param("state"), "the-verifier");
    }

    #[tokio::test]
    async fn the_exchange_body_matches_the_ts_grant() {
        let _port = CALLBACK_PORT_LOCK.lock().await;
        if !registered_port_stages() {
            return; // the registered port is busy: this run cannot stage it.
        }
        let http = token_http();
        let ui = ScriptedUi::with_pastes(vec![ScriptedAnswer::value("the-code")]);
        let credentials = login_anthropic(&http, &ui).await.unwrap();
        assert_eq!(credentials.access, "the-access");
        assert_eq!(credentials.refresh, "the-refresh");
        // TS: expires = now + expires_in * 1000 - 5 minutes.
        // Epoch millis fit i64; the assertion's tolerance covers the cast convention.
        #[allow(clippy::cast_possible_truncation)]
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_millis() as i64;
        let skew = (credentials.expires - now - (3600 * 1000 - EXPIRY_SKEW_MS)).abs();
        assert!(skew < 10_000, "the expiry arithmetic: {skew}");
        // The bare-code paste takes the verifier as its state.
        assert_eq!(http.bodies(TOKEN_URL), vec![grant("the-code", &ui.state())]);
        // The exchange is narrated (TS `onProgress`).
        assert!(ui.has_progress("Exchanging authorization code for tokens..."));
    }

    /// A failed exchange keeps the login open: the real reason (status
    /// and body) lands as the notice, the same paste retries with the
    /// same verifier, and the second exchange logs in.
    #[tokio::test]
    async fn a_failed_exchange_re_prompts_and_the_retry_logs_in() {
        let _port = CALLBACK_PORT_LOCK.lock().await;
        if !registered_port_stages() {
            return; // the registered port is busy: this run cannot stage it.
        }
        let http = ScriptedHttp::new(vec![
            (TOKEN_URL, 400, "no grant"),
            (TOKEN_URL, 200, HAPPY_TOKEN),
        ]);
        let ui = ScriptedUi::with_pastes(vec![
            ScriptedAnswer::Redirect(landed),
            ScriptedAnswer::Redirect(landed),
        ]);
        let credentials = login_anthropic(&http, &ui).await.unwrap();
        assert_eq!(credentials.access, "the-access");
        assert_eq!(
            ui.rejections(),
            vec![exchange_retry_notice(&format!(
                "Token exchange request failed. url={TOKEN_URL}; redirect_uri={REDIRECT_URI}; response_type=authorization_code; details=Error: HTTP request failed. status=400; url={TOKEN_URL}; body=no grant"
            ))]
        );
        let state = ui.state();
        assert_eq!(
            http.bodies(TOKEN_URL),
            vec![grant("the-code", &state), grant("the-code", &state)]
        );
    }

    #[tokio::test]
    async fn a_missing_field_exchange_names_the_response() {
        let _port = CALLBACK_PORT_LOCK.lock().await;
        if !registered_port_stages() {
            return; // the registered port is busy: this run cannot stage it.
        }
        let http = ScriptedHttp::new(vec![(TOKEN_URL, 200, r#"{"access_token":"a"}"#)]);
        // One paste, then the user cancels the re-prompt.
        let ui = ScriptedUi::with_pastes(vec![ScriptedAnswer::value("the-code")]);
        let error = login_anthropic(&http, &ui).await.unwrap_err();
        assert_eq!(error, LOGIN_CANCELLED);
        assert_eq!(
            ui.rejections(),
            vec![exchange_retry_notice(
                r#"Token exchange response missing fields: {"access_token":"a"}"#
            )]
        );
    }

    #[tokio::test]
    async fn a_failed_refresh_surfaces_the_ts_message() {
        let http = ScriptedHttp::new(vec![(TOKEN_URL, 401, "expired")]);
        let error = refresh_anthropic_token(&http, "r-old").await.unwrap_err();
        assert_eq!(
            error,
            format!(
                "Anthropic token refresh request failed. url={TOKEN_URL}; details=Error: HTTP request failed. status=401; url={TOKEN_URL}; body=expired"
            )
        );
    }

    #[tokio::test]
    async fn an_unreachable_token_endpoint_surfaces_the_transport_error() {
        // Nothing scripted: the transport fails the request.
        let http = ScriptedHttp::new(Vec::new());
        let error = refresh_anthropic_token(&http, "r-old").await.unwrap_err();
        assert_eq!(
            error,
            format!(
                "Anthropic token refresh request failed. url={TOKEN_URL}; details={TOKEN_URL} was not scripted"
            )
        );
    }

    /// The wrong-tab regression: a paste from another login attempt is
    /// a notice and a fresh field, never a failed login; the right paste
    /// then exchanges exactly once with this login's verifier.
    #[tokio::test]
    async fn a_wrong_state_paste_re_prompts_then_the_right_one_logs_in() {
        let _port = CALLBACK_PORT_LOCK.lock().await;
        if !registered_port_stages() {
            return; // the registered port is busy: this run cannot stage it.
        }
        let http = token_http();
        let ui = ScriptedUi::with_pastes(vec![
            ScriptedAnswer::value("http://localhost:53692/callback?code=abc&state=wrong"),
            ScriptedAnswer::Redirect(landed),
        ]);
        let credentials = login_anthropic(&http, &ui).await.unwrap();
        assert_eq!(credentials.access, "the-access");
        assert_eq!(
            ui.rejections(),
            vec![RedirectInputError::StateMismatch.to_string()]
        );
        assert_eq!(http.bodies(TOKEN_URL), vec![grant("the-code", &ui.state())]);
    }

    /// The remote-browser path: the address of the failed localhost page
    /// (as copied: wrapped, quoted, line-broken, or its `code#state`
    /// form) is pasted, and the exchange posts that code with the echoed
    /// state and the registered redirect. Consecutive logins rebind the
    /// registered port (the dropped server released it).
    #[tokio::test]
    async fn a_pasted_redirect_exchanges_its_code_and_state() {
        let _port = CALLBACK_PORT_LOCK.lock().await;
        if !registered_port_stages() {
            return; // the registered port is busy: this run cannot stage it.
        }
        let pastes: [fn(&str) -> String; 3] = [
            landed,
            |state| {
                format!("  \"http://localhost:53692/call\nback?code=the-code&state={state}\"\n")
            },
            |state| format!("the-code#{state}"),
        ];
        for paste in pastes {
            let http = token_http();
            let ui = ScriptedUi::with_pastes(vec![ScriptedAnswer::Redirect(paste)]);
            let credentials = login_anthropic(&http, &ui).await.unwrap();
            assert_eq!(credentials.access, "the-access");
            assert!(
                !ui.has_progress("Port 53692 is busy"),
                "the previous login released the port"
            );
            assert_eq!(http.bodies(TOKEN_URL), vec![grant("the-code", &ui.state())]);
        }
    }

    #[tokio::test]
    async fn a_paste_without_a_code_re_prompts() {
        let _port = CALLBACK_PORT_LOCK.lock().await;
        if !registered_port_stages() {
            return; // the registered port is busy: this run cannot stage it.
        }
        let http = token_http();
        let ui = ScriptedUi::with_pastes(vec![
            ScriptedAnswer::value("http://localhost:53692/callback?state=x"),
            ScriptedAnswer::value("the-pasted-code"),
        ]);
        login_anthropic(&http, &ui).await.unwrap();
        assert_eq!(
            ui.rejections(),
            vec![RedirectInputError::MissingCode.to_string()]
        );
        assert_eq!(
            http.bodies(TOKEN_URL),
            vec![grant("the-pasted-code", &ui.state())]
        );
    }

    #[tokio::test]
    async fn an_oauth_error_paste_re_prompts_with_its_description() {
        let _port = CALLBACK_PORT_LOCK.lock().await;
        if !registered_port_stages() {
            return; // the registered port is busy: this run cannot stage it.
        }
        let http = token_http();
        let ui = ScriptedUi::with_pastes(vec![ScriptedAnswer::value(
            "http://localhost:53692/callback?error=access_denied&error_description=denied+by+user",
        )]);
        assert_eq!(
            login_anthropic(&http, &ui).await.unwrap_err(),
            LOGIN_CANCELLED
        );
        assert_eq!(
            ui.rejections(),
            vec![RedirectInputError::Provider {
                error: "access_denied".to_string(),
                description: Some("denied by user".to_string()),
            }
            .to_string()]
        );
        assert!(http.bodies(TOKEN_URL).is_empty());
    }

    #[tokio::test]
    async fn a_cancelled_paste_ends_the_login() {
        let _port = CALLBACK_PORT_LOCK.lock().await;
        if !registered_port_stages() {
            return; // the registered port is busy: this run cannot stage it.
        }
        let http = token_http();
        let ui = ScriptedUi::with_pastes(vec![ScriptedAnswer::ready()]);
        let error = login_anthropic(&http, &ui).await.unwrap_err();
        assert_eq!(error, LOGIN_CANCELLED);
        assert!(http.bodies(TOKEN_URL).is_empty());
    }

    /// The busy-port regression: another process holds 53692, so the
    /// login cannot bind its callback -- it says so and the paste still
    /// logs in (the bind error used to fail the login).
    #[tokio::test]
    async fn a_busy_port_leaves_the_paste_path_that_still_logs_in() {
        let _port = CALLBACK_PORT_LOCK.lock().await;
        let Some(held) = hold_registered_port() else {
            return; // the registered port is busy: this run cannot stage it.
        };
        let http = token_http();
        let ui = ScriptedUi::with_pastes(vec![ScriptedAnswer::Redirect(landed)]);
        let credentials = login_anthropic(&http, &ui).await.unwrap();
        assert_eq!(credentials.access, "the-access");
        assert!(ui.has_progress(
            "Port 53692 is busy, so the browser cannot hand the login back automatically"
        ));
        assert_eq!(http.bodies(TOKEN_URL), vec![grant("the-code", &ui.state())]);
        drop(held);
    }

    /// Without a paste surface a busy port leaves the prompt fallback;
    /// its rejected answer is the error (no re-prompt surface).
    #[tokio::test]
    async fn a_busy_port_without_a_paste_surface_falls_to_the_prompt() {
        let _port = CALLBACK_PORT_LOCK.lock().await;
        let Some(held) = hold_registered_port() else {
            return; // the registered port is busy: this run cannot stage it.
        };
        let http = token_http();
        let ui = ScriptedUi::without_paste(ScriptedAnswer::Redirect(landed));
        login_anthropic(&http, &ui).await.unwrap();
        assert_eq!(http.bodies(TOKEN_URL), vec![grant("the-code", &ui.state())]);
        let ui = ScriptedUi::without_paste(ScriptedAnswer::value("code=abc&state=wrong"));
        assert_eq!(
            login_anthropic(&http, &ui).await.unwrap_err(),
            RedirectInputError::StateMismatch.to_string()
        );
        let ui = ScriptedUi::without_paste(ScriptedAnswer::ready());
        assert_eq!(
            login_anthropic(&http, &ui).await.unwrap_err(),
            LOGIN_CANCELLED
        );
        assert!(ui.rejections().is_empty());
        drop(held);
    }

    #[tokio::test]
    async fn a_cancelled_surface_ends_the_login_between_polls() {
        let _port = CALLBACK_PORT_LOCK.lock().await;
        if !registered_port_stages() {
            return; // the registered port is busy: this run cannot stage it.
        }
        // The flag flips when the url lands: the race loop's first
        // poll-step check ends the flow before any code arrives.
        let http = token_http();
        let mut ui = ScriptedUi::with_pastes(vec![ScriptedAnswer::Pending]);
        ui.cancel_on_auth = true;
        let error = login_anthropic(&http, &ui).await.unwrap_err();
        assert_eq!(error, LOGIN_CANCELLED);
        // No token request ever posted.
        assert!(http.bodies(TOKEN_URL).is_empty());
    }

    /// The browser callback wins over a pending paste: the flow drops
    /// the paste field (the panel stops showing it) and exchanges the
    /// redirect's code.
    #[tokio::test]
    async fn the_browser_callback_wins_the_race_and_drops_the_paste() {
        let _port = CALLBACK_PORT_LOCK.lock().await;
        // The real registered port: the flow binds its callback server
        // and the browser redirect settles the code.
        if !registered_port_stages() {
            return; // the registered port is busy: this run cannot stage it.
        }
        let http = Arc::new(token_http());
        let ui = Arc::new(ScriptedUi::with_pastes(vec![ScriptedAnswer::Pending]));
        let flow = {
            let (flow_http, flow_ui) = (Arc::clone(&http), Arc::clone(&ui));
            tokio::spawn(async move { login_anthropic(flow_http.as_ref(), flow_ui.as_ref()).await })
        };
        let state = state_of(&ui.captured_url().await);
        browser_redirect("live-code", &state).await;
        let credentials = tokio::time::timeout(Duration::from_secs(10), flow)
            .await
            .expect("the flow settles once the redirect lands")
            .unwrap()
            .unwrap();
        assert_eq!(credentials.access, "the-access");
        assert_eq!(http.bodies(TOKEN_URL), vec![grant("live-code", &state)]);
        assert_eq!(ui.dropped_fields.load(Ordering::SeqCst), 1);
    }

    /// A rejected paste does not end the race: the browser callback that
    /// lands afterwards still logs in.
    #[tokio::test]
    async fn the_browser_callback_still_wins_after_a_rejected_paste() {
        let _port = CALLBACK_PORT_LOCK.lock().await;
        if !registered_port_stages() {
            return; // the registered port is busy: this run cannot stage it.
        }
        let http = Arc::new(token_http());
        let ui = Arc::new(ScriptedUi::with_pastes(vec![
            ScriptedAnswer::value("code=abc&state=wrong"),
            ScriptedAnswer::Pending,
        ]));
        let flow = {
            let (flow_http, flow_ui) = (Arc::clone(&http), Arc::clone(&ui));
            tokio::spawn(async move { login_anthropic(flow_http.as_ref(), flow_ui.as_ref()).await })
        };
        let state = state_of(&ui.captured_url().await);
        browser_redirect("live-code", &state).await;
        tokio::time::timeout(Duration::from_secs(10), flow)
            .await
            .expect("the flow settles once the redirect lands")
            .unwrap()
            .unwrap();
        assert_eq!(
            ui.rejections(),
            vec![RedirectInputError::StateMismatch.to_string()]
        );
        assert_eq!(http.bodies(TOKEN_URL), vec![grant("live-code", &state)]);
    }
}
