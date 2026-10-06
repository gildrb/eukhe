//! The `ChatGPT` Plus/Pro (Codex Subscription) OAuth flow — the port of
//! `packages/ai/src/utils/oauth/openai-codex.ts` (+ `pkce.ts`): the PKCE
//! authorization request against the app registration, the localhost
//! callback server raced against the manual paste, the token exchange,
//! the JWT account-id claim, and the token refresh. The credentials the
//! flow returns carry the TS shape (`access`, `refresh`, `expires`,
//! `accountId`) and persist under the provider id `openai-codex`.
//!
//! Cancellation follows the fleet's cooperative pattern (#2770): the
//! driving surface marks a shared flag when it exits; the flow checks it
//! between the race's poll steps and before its network steps, so an
//! exited surface never receives a completed login (a task abort cannot
//! reach a started blocking body).
//!
//! Remote logins: a rejected paste or a failed exchange re-prompts on the
//! same panel with the same verifier and state while the callback server
//! keeps waiting; only a cancel ends the login. A busy callback port
//! leaves the paste as the only path.

use std::fmt::Write as _;
use std::future::Future;
use std::pin::{pin, Pin};
use std::time::Duration;

use base64::Engine as _;
use rand::Rng;
use sha2::{Digest, Sha256};
use url::Url;

use super::callback::{CodexCallbackServer, CALLBACK_PORT};
use super::redirect_input::{exchange_retry_notice, parse_redirect_input, port_busy_line};
use super::response_snippet::response_snippet;
use super::CodexHttp;

/// The app registration the TS flow ships (TS `CLIENT_ID`).
pub const OPENAI_CODEX_CLIENT_ID: &str = "app_EMoamEEZ73f0CkXaXp7hrann";
/// TS `AUTHORIZE_URL`.
const AUTHORIZE_URL: &str = "https://auth.openai.com/oauth/authorize";
/// TS `TOKEN_URL`.
const TOKEN_URL: &str = "https://auth.openai.com/oauth/token";
/// The registered redirect (TS `REDIRECT_URI`): the callback server's
/// own address.
const REDIRECT_URI: &str = "http://localhost:1455/auth/callback";
/// TS `SCOPE`.
const SCOPE: &str = "openid profile email offline_access";
/// The TS flow's default originator.
pub const DEFAULT_ORIGINATOR: &str = "pi";
/// One token request's bound (the port's request-timeout norm).
pub const DEFAULT_TOKEN_TIMEOUT_MS: u64 = 30_000;
/// The refresh grant's tighter bound: the auth storage runs it under its
/// file lock, which a peer declares stale after 10 seconds — the request
/// must fit inside that window so a slow endpoint fails the refresh
/// (kept for a retry) instead of holding the lock past its staleness.
pub const REFRESH_TIMEOUT_MS: u64 = 8_000;
/// The `onAuth` instructions line: the remote-login steps spelled out (a
/// browser on another machine cannot reach the localhost callback).
const AUTH_INSTRUCTIONS: &str = "A browser window should open. Complete login to finish. On another machine, the browser ends on a localhost page that fails to load: copy that page's full address and paste it below.";
/// TS the `onPrompt` fallback line.
const PROMPT_MESSAGE: &str = "Paste the authorization code (or full redirect URL):";
/// The cancel error the driving surface maps to the silent cancelled
/// outcome (TS the dialog throws the same text; `auth-flows.ts` matches
/// it).
pub const LOGIN_CANCELLED: &str = "Login cancelled";
/// The race's poll step: how often the loop re-checks the cooperative
/// cancel flag (the #2770 pattern — the flag is checked between poll
/// steps).
const CANCEL_POLL_INTERVAL: Duration = Duration::from_millis(250);

/// The credentials the flow returns and persists (TS `OAuthCredentials`
/// plus the codex provider's `accountId`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OAuthCredentials {
    pub access: String,
    pub refresh: String,
    /// Wall-clock epoch milliseconds (TS `Date.now() + expires_in * 1000`).
    pub expires: i64,
    pub account_id: String,
}

/// The login's UI surface (TS `OAuthLoginCallbacks`): the browser URL
/// block, the manual paste racing the browser callback, and the
/// fallback prompt. Implementations render the inline auth panel (the
/// TUI) or script the flow (tests).
pub trait CodexLoginUi: Send + Sync {
    /// TS `onAuth`: the authorization URL to open, plus the flow's
    /// instructions line.
    fn on_auth(&self, url: &str, instructions: &str);
    /// TS `onManualCodeInput`: the paste racing the browser callback;
    /// `None` when the surface offers none. Resolving `None` cancels
    /// the login. The flow asks again after a rejected paste or a failed
    /// exchange, so each call mounts a fresh paste field.
    fn on_manual_code_input(&self) -> Option<Pin<Box<dyn Future<Output = Option<String>> + Send>>>;
    /// A paste or an exchange failed (or the callback port is busy) but
    /// the login goes on: show `reason` where the next paste field
    /// appears. Only flows with a paste surface call it; the panel shows
    /// a warning row that clears on the next submit.
    fn on_input_rejected(&self, reason: &str);
    /// TS `onPrompt`: the fallback prompt when neither the callback
    /// nor the paste produced a code. Resolving `None` cancels the
    /// login.
    fn on_prompt(&self, message: &str) -> Pin<Box<dyn Future<Output = Option<String>> + Send>>;
    /// The driving surface's cooperative cancel state: `true` once the
    /// pane that mounted the login exited. The flow checks it between
    /// the race's poll steps and before its network steps — a task
    /// abort cannot reach a started blocking body, so the pane marks
    /// this instead (#2770). The default (`false`) serves the surfaces
    /// that never cancel mid-flow.
    fn is_cancelled(&self) -> bool {
        false
    }
}

/// Run the login (TS `loginOpenAICodex`): build the PKCE request, start
/// the callback server, present the URL, race the browser callback
/// against the manual paste, exchange the code, and return the
/// credentials to persist.
///
/// With a paste surface, a rejected paste (no code, another login's
/// state, an OAuth error) and a failed exchange are reported through
/// [`CodexLoginUi::on_input_rejected`] and the paste is asked again;
/// the browser callback can still win meanwhile.
///
/// # Errors
///
/// Returns an error when the surface cancelled the login
/// ([`LOGIN_CANCELLED`]) or the access token carries no account id;
/// without a paste surface also when the prompt answer is rejected or
/// the token exchange fails.
// One race loop reads top to bottom: the callback, the paste, the retries,
// the cancel ticks, and the exchange share its state; splitting scatters it.
#[allow(clippy::too_many_lines)]
pub async fn login_openai_codex(
    http: &dyn CodexHttp,
    ui: &dyn CodexLoginUi,
    originator: &str,
) -> Result<OAuthCredentials, String> {
    // The surface exited before the flow started: no server, no
    // browser launch -- the exit ends the flow (the first of the
    // between-poll cancel checks, #2770).
    if ui.is_cancelled() {
        return Err(LOGIN_CANCELLED.to_string());
    }
    let (verifier, challenge) = generate_pkce();
    let state = create_state();
    let url = authorization_url(&challenge, &state, originator);
    let server = CodexCallbackServer::start(&state).await;
    ui.on_auth(&url, AUTH_INSTRUCTIONS);
    let mut manual = ui.on_manual_code_input();
    let paste_surface = manual.is_some();
    let server = server
        .inspect_err(|detail| {
            if paste_surface {
                ui.on_input_rejected(&port_busy_line(CALLBACK_PORT, detail));
            }
        })
        .ok();
    let mut callback_live = server.is_some();
    let wait_once = || async {
        match &server {
            Some(server) => server.wait_for_code().await,
            None => None,
        }
    };
    let mut wait = pin!(wait_once());
    let mut tick = tokio::time::interval(CANCEL_POLL_INTERVAL);
    loop {
        let code = loop {
            if ui.is_cancelled() {
                return Err(LOGIN_CANCELLED.to_string());
            }
            if !callback_live && manual.is_none() {
                // The fallback prompt (TS `onPrompt`): no browser hand-back
                // and no paste surface.
                // The pending prompt must not hold a cancelled flow: the
                // tick re-checks the cooperative cancel while it waits.
                let mut prompt = ui.on_prompt(PROMPT_MESSAGE);
                let answer = loop {
                    if ui.is_cancelled() {
                        return Err(LOGIN_CANCELLED.to_string());
                    }
                    tokio::select! {
                        _ = tick.tick() => {}
                        answer = &mut prompt => break answer,
                    }
                };
                let input = answer.ok_or_else(|| LOGIN_CANCELLED.to_string())?;
                break parse_redirect_input(&input)
                    .and_then(|pasted| pasted.verify_state(&state))
                    .map_err(|rejected| rejected.to_string())?
                    .code;
            }
            let step = tokio::select! {
                _ = tick.tick() => RaceStep::Tick,
                settled = &mut wait, if callback_live => RaceStep::Callback(settled.map(|settled| settled.code)),
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
                        .and_then(|pasted| pasted.verify_state(&state))
                    {
                        Ok(accepted) => break accepted.code,
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
        // The pane exited while the login waited: no exchange, no
        // credential -- the exit ends the flow (TS the dialog's abort
        // signal; #2770: the flag is the seam).
        if ui.is_cancelled() {
            return Err(LOGIN_CANCELLED.to_string());
        }
        match exchange_authorization_code(http, &code, &verifier).await {
            Ok(token) => {
                let account_id = account_id_of(&token.access)?;
                return Ok(OAuthCredentials {
                    access: token.access,
                    refresh: token.refresh,
                    expires: token.expires,
                    account_id,
                });
            }
            Err(error) if paste_surface => {
                ui.on_input_rejected(&exchange_retry_notice(&error));
                manual = ui.on_manual_code_input();
            }
            Err(error) => return Err(error),
        }
    }
}

/// Refresh an expired credential (TS `refreshOpenAICodexToken`).
///
/// # Errors
///
/// Returns an error when the token refresh fails or the fresh access
/// token carries no account id.
pub async fn refresh_openai_codex_token(
    http: &dyn CodexHttp,
    refresh_token: &str,
) -> Result<OAuthCredentials, String> {
    let token = refresh_access_token(http, refresh_token).await?;
    let account_id = account_id_of(&token.access)?;
    Ok(OAuthCredentials {
        access: token.access,
        refresh: token.refresh,
        expires: token.expires,
        account_id,
    })
}

/// One token response (TS `TokenSuccess`).
struct TokenSuccess {
    access: String,
    refresh: String,
    expires: i64,
}

/// One step of the race: the cancel tick, the browser callback, or the
/// paste answer.
enum RaceStep {
    Tick,
    /// The callback wait settled: the code, or `None` when it settled
    /// empty (a cancelled wait).
    Callback(Option<String>),
    /// The paste answered: the input, or `None` when cancelled.
    Paste(Option<String>),
}

/// A PKCE pair (TS `generatePKCE`): the verifier is the token-exchange
/// secret, the challenge travels in the authorization URL.
fn generate_pkce() -> (String, String) {
    let verifier = base64url(&random_bytes(32));
    let challenge = base64url(Sha256::digest(verifier.as_bytes()).as_slice());
    (verifier, challenge)
}

/// A random, hex CSRF `state` (TS `createState`: 16 random bytes as
/// hex).
fn create_state() -> String {
    let mut state = String::with_capacity(32);
    for byte in random_bytes(16) {
        let _ = write!(state, "{byte:02x}");
    }
    state
}

fn random_bytes(len: usize) -> Vec<u8> {
    let mut bytes = vec![0u8; len];
    rand::thread_rng().fill(&mut bytes[..]);
    bytes
}

fn base64url(bytes: &[u8]) -> String {
    base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(bytes)
}

/// The authorization URL (TS `createAuthorizationFlow`'s URL: the
/// challenge, the CSRF state, the registration's redirect and scope,
/// the simplified-flow flags, and the originator).
fn authorization_url(challenge: &str, state: &str, originator: &str) -> String {
    let mut url = Url::parse(AUTHORIZE_URL).expect("the authorize url parses");
    for (name, value) in [
        ("response_type", "code"),
        ("client_id", OPENAI_CODEX_CLIENT_ID),
        ("redirect_uri", REDIRECT_URI),
        ("scope", SCOPE),
        ("code_challenge", challenge),
        ("code_challenge_method", "S256"),
        ("state", state),
        ("id_token_add_organizations", "true"),
        ("codex_cli_simplified_flow", "true"),
        ("originator", originator),
    ] {
        url.query_pairs_mut().append_pair(name, value);
    }
    url.to_string()
}

/// The account id the access token carries (TS `getAccountId`: the
/// `chatgpt_account_id` claim under the JWT auth claim path — the
/// provider's own extraction is the one owner).
fn account_id_of(access_token: &str) -> Result<String, String> {
    crate::providers::openai_codex_responses::request::extract_account_id(access_token)
        .map_err(|_| "Failed to extract accountId from token".to_string())
}

/// One token POST's outcome validation (TS `exchangeAuthorizationCode` /
/// `refreshAccessToken` share the shape): a 2xx answer with the three
/// fields the flow requires.
/// One token POST with an explicit request bound (the login keeps the
/// port's default; the refresh runs under the storage lock and takes the
/// tighter one).
async fn token_post_bounded(
    http: &dyn CodexHttp,
    params: &[(&str, &str)],
    label: &str,
    timeout_ms: u64,
) -> Result<TokenSuccess, String> {
    let body = url::form_urlencoded::Serializer::new(String::new())
        .extend_pairs(params.iter().map(|(key, value)| (*key, *value)))
        .finish();
    let response = http
        .post_form(TOKEN_URL, &body, timeout_ms)
        .await
        .map_err(|message| format!("OpenAI Codex token {label} error: {message}"))?;
    if !response.ok() {
        // TS falls back to `response.statusText` when the body is empty.
        let text = if response.body.trim().is_empty() {
            format!("HTTP {}", response.status)
        } else {
            response_snippet(&response.body)
        };
        return Err(format!(
            "OpenAI Codex token {label} failed ({}): {text}",
            response.status
        ));
    }
    let json: serde_json::Value = serde_json::from_str(&response.body).map_err(|error| {
        format!(
            "OpenAI Codex token {label} returned invalid JSON (HTTP {}): {error}; body={}",
            response.status,
            response_snippet(&response.body)
        )
    })?;
    let missing_fields = || {
        format!(
            "OpenAI Codex token {label} response missing fields: {}",
            response_snippet(&json.to_string())
        )
    };
    let Some(access) = json
        .get("access_token")
        .and_then(serde_json::Value::as_str)
        .filter(|token| !token.is_empty())
    else {
        return Err(missing_fields());
    };
    let Some(refresh) = json
        .get("refresh_token")
        .and_then(serde_json::Value::as_str)
        .filter(|token| !token.is_empty())
    else {
        return Err(missing_fields());
    };
    let Some(expires_in) = json.get("expires_in").and_then(serde_json::Value::as_f64) else {
        return Err(missing_fields());
    };
    if !expires_in.is_finite() {
        // A NaN/`inf` lifetime is not a lifetime (TS's arithmetic yields
        // a never-expiring credential; the port refuses it as a broken
        // response instead).
        return Err(missing_fields());
    }
    // Epoch millis fit i64 for ~292 million years; the u128 duration's millis are the i64 convention here.
    #[allow(clippy::cast_possible_truncation)]
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(i64::MAX, |elapsed| elapsed.as_millis() as i64);
    // Saturating: an oversized `expires_in` cannot overflow the
    // epoch-millisecond sum (the worst case saturates at the never
    // until it refreshes).
    // The wire's expires_in is a second count read through JSON f64; i64 ms is the credentials' convention.
    #[allow(clippy::cast_possible_truncation)]
    let expires = now.saturating_add((expires_in * 1000.0) as i64);
    Ok(TokenSuccess {
        access: access.to_string(),
        refresh: refresh.to_string(),
        expires,
    })
}

/// TS `exchangeAuthorizationCode`: the authorization-code grant with the
/// PKCE verifier against the registered redirect.
async fn exchange_authorization_code(
    http: &dyn CodexHttp,
    code: &str,
    verifier: &str,
) -> Result<TokenSuccess, String> {
    token_post_bounded(
        http,
        &[
            ("grant_type", "authorization_code"),
            ("client_id", OPENAI_CODEX_CLIENT_ID),
            ("code", code),
            ("code_verifier", verifier),
            ("redirect_uri", REDIRECT_URI),
        ],
        "exchange",
        DEFAULT_TOKEN_TIMEOUT_MS,
    )
    .await
}

/// TS `refreshAccessToken`: the refresh-token grant.
async fn refresh_access_token(
    http: &dyn CodexHttp,
    refresh_token: &str,
) -> Result<TokenSuccess, String> {
    token_post_bounded(
        http,
        &[
            ("grant_type", "refresh_token"),
            ("refresh_token", refresh_token),
            ("client_id", OPENAI_CODEX_CLIENT_ID),
        ],
        "refresh",
        REFRESH_TIMEOUT_MS,
    )
    .await
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oauth::redirect_input::RedirectInputError;
    use crate::oauth::CodexHttpResponse;
    use serde_json::json;
    use std::collections::{HashMap, VecDeque};
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Arc, Mutex};
    use tokio::io::AsyncWriteExt as _;

    /// The app registration's redirect port is one fixed socket and every
    /// `login_openai_codex` flow binds it, while the default harness runs
    /// this module's tests on parallel threads: each flow stages the
    /// port under this lock, so a sibling's bind can never land in the
    /// browser race's probe-to-bind window and leave its flow's listener
    /// dead. The lock is the async-aware one — the guard is held across
    /// the flow's awaits by design (and never poisons).
    static REDIRECT_PORT: tokio::sync::Mutex<()> = tokio::sync::Mutex::const_new(());

    /// A scripted transport: url -> queued responses (the last one
    /// repeats), recording every posted body. Unknown urls fail the
    /// request (the TS suite throws on unexpected fetches).
    struct ScriptedHttp {
        responses: Mutex<HashMap<String, VecDeque<CodexHttpResponse>>>,
        seen: Mutex<Vec<(String, String)>>,
    }

    impl ScriptedHttp {
        fn new(responses: Vec<(&str, u16, &str)>) -> Self {
            let mut queued: HashMap<String, VecDeque<CodexHttpResponse>> = HashMap::new();
            for (url, status, body) in responses {
                queued
                    .entry(url.to_string())
                    .or_default()
                    .push_back(CodexHttpResponse {
                        status,
                        body: body.to_string(),
                    });
            }
            ScriptedHttp {
                responses: Mutex::new(queued),
                seen: Mutex::new(Vec::new()),
            }
        }

        fn seen_bodies(&self, url: &str) -> Vec<String> {
            self.seen
                .lock()
                .unwrap()
                .iter()
                .filter(|(seen_url, _)| seen_url == url)
                .map(|(_, body)| body.clone())
                .collect()
        }
    }

    impl CodexHttp for ScriptedHttp {
        fn post_form<'a>(
            &'a self,
            url: &'a str,
            body: &'a str,
            _timeout_ms: u64,
        ) -> Pin<Box<dyn Future<Output = Result<CodexHttpResponse, String>> + Send + 'a>> {
            self.seen
                .lock()
                .unwrap()
                .push((url.to_string(), body.to_string()));
            let response = self
                .responses
                .lock()
                .unwrap()
                .get_mut(url)
                .and_then(|queue| {
                    if queue.len() > 1 {
                        queue.pop_front()
                    } else {
                        queue.front().cloned()
                    }
                });
            Box::pin(async move { response.ok_or_else(|| format!("{url} was not scripted")) })
        }
    }

    /// One scripted UI answer: an immediate value (`Some`), an
    /// immediate cancel (`None`), a never-resolving surface, a surface
    /// that marks the cancel flag on its first poll and then never
    /// resolves, or a paste built from the presented state (the address
    /// a remote browser lands on).
    enum ScriptedAnswer {
        Once(Option<String>),
        Pending,
        PendingMarksCancel,
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

    /// The scripted login surface: the captured authorization URL, the
    /// queued pastes (one per mounted field; an exhausted queue
    /// cancels), the fallback prompt, and the rejections.
    struct ScriptedUi {
        auth_url: Mutex<Option<String>>,
        pastes: Option<Mutex<VecDeque<ScriptedAnswer>>>,
        prompt: ScriptedAnswer,
        rejections: Mutex<Vec<String>>,
        cancelled: Arc<AtomicBool>,
        cancel_on_auth: bool,
    }

    impl ScriptedUi {
        fn new(manual: Option<ScriptedAnswer>, prompt: ScriptedAnswer) -> Self {
            ScriptedUi {
                auth_url: Mutex::new(None),
                pastes: manual.map(|answer| Mutex::new(VecDeque::from([answer]))),
                prompt,
                rejections: Mutex::new(Vec::new()),
                cancelled: Arc::new(AtomicBool::new(false)),
                cancel_on_auth: false,
            }
        }

        fn with_pastes(pastes: Vec<ScriptedAnswer>) -> Self {
            ScriptedUi {
                pastes: Some(Mutex::new(pastes.into_iter().collect())),
                ..ScriptedUi::new(None, ScriptedAnswer::Pending)
            }
        }

        /// The rejections, the port-busy line excluded (a port held
        /// outside this binary is a run condition; its own test pins it).
        fn paste_rejections(&self) -> Vec<String> {
            self.rejections
                .lock()
                .unwrap()
                .iter()
                .filter(|reason| !reason.starts_with("Port 1455 is busy"))
                .cloned()
                .collect()
        }

        /// The presented state.
        fn state(&self) -> String {
            let url = self
                .auth_url
                .lock()
                .unwrap()
                .clone()
                .expect("the url shows first");
            url::Url::parse(&url)
                .unwrap()
                .query_pairs()
                .find(|(key, _)| key == "state")
                .map(|(_, value)| value.to_string())
                .expect("the url carries a state")
        }

        /// The captured authorization URL: waits for the flow's
        /// `onAuth` -- observable readiness, bounded by a deadline that
        /// fails the test (never a green-on-timeout retry loop).
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
                tokio::time::sleep(Duration::from_millis(5)).await;
            }
        }

        /// The answer future (the marks-then-pends mode sets the
        /// surface's own cancel flag on the first poll).
        fn future(
            &self,
            answer: &ScriptedAnswer,
        ) -> Pin<Box<dyn Future<Output = Option<String>> + Send>> {
            match answer {
                ScriptedAnswer::Once(value) => Box::pin(std::future::ready(value.clone())),
                ScriptedAnswer::Pending => Box::pin(std::future::pending()),
                ScriptedAnswer::PendingMarksCancel => {
                    let cancel = Arc::clone(&self.cancelled);
                    Box::pin(async move {
                        cancel.store(true, Ordering::Relaxed);
                        std::future::pending::<Option<String>>().await
                    })
                }
                ScriptedAnswer::Redirect(build) => {
                    Box::pin(std::future::ready(Some(build(&self.state()))))
                }
            }
        }
    }

    impl CodexLoginUi for ScriptedUi {
        fn on_auth(&self, url: &str, _instructions: &str) {
            *self.auth_url.lock().unwrap() = Some(url.to_string());
            if self.cancel_on_auth {
                self.cancelled.store(true, Ordering::Relaxed);
            }
        }

        fn on_manual_code_input(
            &self,
        ) -> Option<Pin<Box<dyn Future<Output = Option<String>> + Send>>> {
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

        fn on_prompt(
            &self,
            _message: &str,
        ) -> Pin<Box<dyn Future<Output = Option<String>> + Send>> {
            self.future(&self.prompt)
        }

        fn is_cancelled(&self) -> bool {
            self.cancelled.load(Ordering::Relaxed)
        }
    }

    /// The callback address a remote browser lands on.
    fn landed(state: &str) -> String {
        format!("{REDIRECT_URI}?code=abc&state={state}")
    }

    /// One fake access token: a three-segment JWT whose payload carries
    /// the account id under the TS claim path (no signature — the flow
    /// never verifies one, like the TS `atob` decode).
    fn account_jwt(account_id: Option<&str>) -> String {
        let payload = match account_id {
            Some(account_id) => json!({
                "https://api.openai.com/auth": {"chatgpt_account_id": account_id}
            }),
            None => json!({"sub": "someone"}),
        };
        let segment =
            |value: serde_json::Value| base64url(serde_json::to_string(&value).unwrap().as_bytes());
        format!(
            "{}.{}.not-a-signature",
            segment(json!({"alg": "RS256"})),
            segment(payload)
        )
    }

    fn token_body(access: &str) -> String {
        json!({
            "access_token": access,
            "refresh_token": "r-1",
            "expires_in": 3600,
        })
        .to_string()
    }

    /// The scripted token endpoint: one answer for the whole flow.
    fn token_http(access: &str) -> ScriptedHttp {
        ScriptedHttp::new(vec![(TOKEN_URL, 200, &token_body(access))])
    }

    fn first_param(body: &str, name: &str) -> String {
        url::form_urlencoded::parse(body.as_bytes())
            .find(|(key, _)| key == name)
            .map(|(_, value)| value.to_string())
            .unwrap_or_default()
    }

    /// Stage the app registration's redirect port busy for a
    /// dead-callback flow, on the same host the flow itself binds (the
    /// `EUKHE_OAUTH_CALLBACK_HOST` override, default `127.0.0.1`).
    /// `Some(listener)` means the caller actively holds the port, so
    /// the flow's own bind cannot succeed against it (an active
    /// listener blocks the same-address bind — both sockets set
    /// `SO_REUSEADDR`, neither sets `SO_REUSEPORT`) and the flow's
    /// callback server is dead by construction; `None` means the port
    /// cannot be staged this run and the caller skips rather than run
    /// a login against a listener it does not own.
    fn stage_busy_registered_port() -> Option<std::net::TcpListener> {
        let host = std::env::var(crate::oauth::callback::CALLBACK_HOST_ENV)
            .unwrap_or_else(|_| "127.0.0.1".to_string());
        std::net::TcpListener::bind((host, 1455)).ok()
    }

    #[tokio::test]
    async fn the_exchange_body_matches_the_ts_grant() {
        let _registered_port = REDIRECT_PORT.lock().await;
        let http = token_http(&account_jwt(Some("acct-1")));
        let ui = ScriptedUi::new(
            Some(ScriptedAnswer::value(&format!("{REDIRECT_URI}?code=abc"))),
            ScriptedAnswer::ready(),
        );
        let credentials = login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR)
            .await
            .unwrap();
        assert_eq!(credentials.account_id, "acct-1");
        assert_eq!(credentials.refresh, "r-1");
        assert!(credentials.expires > 0);
        let body = &http.seen_bodies(TOKEN_URL)[0];
        assert_eq!(first_param(body, "grant_type"), "authorization_code");
        assert_eq!(first_param(body, "client_id"), OPENAI_CODEX_CLIENT_ID);
        assert_eq!(first_param(body, "code"), "abc");
        assert_eq!(first_param(body, "redirect_uri"), REDIRECT_URI);
        let verifier = first_param(body, "code_verifier");
        assert_eq!(
            verifier.len(),
            43,
            "the PKCE verifier is 32 base64url bytes"
        );
        // The manual paste carried no state: TS's falsy state skips the
        // echo check and the code is used as-is.
    }

    #[tokio::test]
    async fn the_refresh_body_matches_the_ts_grant() {
        let http = token_http(&account_jwt(Some("acct-1")));
        let credentials = refresh_openai_codex_token(&http, "r-old").await.unwrap();
        assert_eq!(credentials.account_id, "acct-1");
        assert_eq!(credentials.access, account_jwt(Some("acct-1")));
        let body = &http.seen_bodies(TOKEN_URL)[0];
        assert_eq!(first_param(body, "grant_type"), "refresh_token");
        assert_eq!(first_param(body, "refresh_token"), "r-old");
        assert_eq!(first_param(body, "client_id"), OPENAI_CODEX_CLIENT_ID);
    }

    /// A failed exchange keeps the login open: the real reason lands as
    /// the notice and the retried paste logs in with the same verifier.
    #[tokio::test]
    async fn a_failed_exchange_re_prompts_and_the_retry_logs_in() {
        let _registered_port = REDIRECT_PORT.lock().await;
        let http = ScriptedHttp::new(vec![
            (TOKEN_URL, 400, "no grant"),
            (TOKEN_URL, 200, &token_body(&account_jwt(Some("acct-1")))),
        ]);
        let ui = ScriptedUi::with_pastes(vec![
            ScriptedAnswer::Redirect(landed),
            ScriptedAnswer::Redirect(landed),
        ]);
        let credentials = login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR)
            .await
            .unwrap();
        assert_eq!(credentials.account_id, "acct-1");
        assert_eq!(
            ui.paste_rejections(),
            vec![exchange_retry_notice(
                "OpenAI Codex token exchange failed (400): no grant"
            )]
        );
        let bodies = http.seen_bodies(TOKEN_URL);
        assert_eq!(bodies.len(), 2);
        assert_eq!(bodies[0], bodies[1], "the retry posts the same grant");
        assert_eq!(first_param(&bodies[1], "code"), "abc");
    }

    #[tokio::test]
    async fn a_missing_field_exchange_names_the_response() {
        let _registered_port = REDIRECT_PORT.lock().await;
        let http = ScriptedHttp::new(vec![(TOKEN_URL, 200, r#"{"access_token":"a"}"#)]);
        // One paste, then the user cancels the re-prompt.
        let ui = ScriptedUi::new(
            Some(ScriptedAnswer::value(&format!("{REDIRECT_URI}?code=abc"))),
            ScriptedAnswer::ready(),
        );
        let error = login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR)
            .await
            .unwrap_err();
        assert_eq!(error, LOGIN_CANCELLED);
        assert_eq!(
            ui.paste_rejections(),
            vec![exchange_retry_notice(
                r#"OpenAI Codex token exchange response missing fields: {"access_token":"a"}"#
            )]
        );
    }

    #[tokio::test]
    async fn a_failed_refresh_surfaces_the_ts_message() {
        let http = ScriptedHttp::new(vec![(TOKEN_URL, 401, "expired")]);
        let error = refresh_openai_codex_token(&http, "r-old")
            .await
            .unwrap_err();
        assert_eq!(error, "OpenAI Codex token refresh failed (401): expired");
    }

    #[tokio::test]
    async fn an_unreachable_token_endpoint_surfaces_a_transport_error() {
        // Nothing scripted: the transport fails the request (the
        // scripted stand-in for the request timeout).
        let http = ScriptedHttp::new(Vec::new());
        let error = refresh_openai_codex_token(&http, "r-old")
            .await
            .unwrap_err();
        assert!(
            error.starts_with("OpenAI Codex token refresh error:"),
            "{error}"
        );
    }

    #[tokio::test]
    async fn a_token_without_the_account_id_fails_the_login() {
        let _registered_port = REDIRECT_PORT.lock().await;
        let http = token_http(&account_jwt(None));
        let ui = ScriptedUi::new(
            Some(ScriptedAnswer::value(&format!("{REDIRECT_URI}?code=abc"))),
            ScriptedAnswer::ready(),
        );
        let error = login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR)
            .await
            .unwrap_err();
        assert_eq!(error, "Failed to extract accountId from token");
    }

    #[tokio::test]
    async fn a_cancelled_surface_ends_the_login_between_polls() {
        let _registered_port = REDIRECT_PORT.lock().await;
        // The flag flips when the url lands: the race loop's first
        // poll-step check ends the flow before any code arrives.
        let http = token_http(&account_jwt(Some("acct-1")));
        let mut ui = ScriptedUi::new(Some(ScriptedAnswer::Pending), ScriptedAnswer::Pending);
        ui.cancel_on_auth = true;
        let error = login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR)
            .await
            .unwrap_err();
        assert_eq!(error, LOGIN_CANCELLED);
        // No token request ever posted.
        assert!(http.seen_bodies(TOKEN_URL).is_empty());
    }

    #[tokio::test]
    async fn a_cancelled_paste_ends_the_login() {
        let _registered_port = REDIRECT_PORT.lock().await;
        let http = token_http(&account_jwt(Some("acct-1")));
        let ui = ScriptedUi::new(
            Some(ScriptedAnswer::ready()),
            ScriptedAnswer::value("late-code"),
        );
        let error = login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR)
            .await
            .unwrap_err();
        assert_eq!(error, LOGIN_CANCELLED);
    }

    /// The wrong-tab regression: a paste from another login attempt is a
    /// notice and a fresh field; the right paste then logs in with one
    /// exchange.
    #[tokio::test]
    async fn a_wrong_state_paste_re_prompts_then_the_right_one_logs_in() {
        let _registered_port = REDIRECT_PORT.lock().await;
        let http = token_http(&account_jwt(Some("acct-1")));
        let ui = ScriptedUi::with_pastes(vec![
            ScriptedAnswer::value(&format!("{REDIRECT_URI}?code=stolen&state=not-ours")),
            ScriptedAnswer::Redirect(landed),
        ]);
        let credentials = login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR)
            .await
            .unwrap();
        assert_eq!(credentials.account_id, "acct-1");
        assert_eq!(
            ui.paste_rejections(),
            vec![RedirectInputError::StateMismatch.to_string()]
        );
        let bodies = http.seen_bodies(TOKEN_URL);
        assert_eq!(bodies.len(), 1);
        assert_eq!(first_param(&bodies[0], "code"), "abc");
        assert_eq!(first_param(&bodies[0], "redirect_uri"), REDIRECT_URI);
    }

    #[tokio::test]
    async fn a_paste_without_a_code_re_prompts() {
        let _registered_port = REDIRECT_PORT.lock().await;
        let http = token_http(&account_jwt(Some("acct-1")));
        let ui = ScriptedUi::with_pastes(vec![
            ScriptedAnswer::value(REDIRECT_URI),
            ScriptedAnswer::value("pasted-code"),
        ]);
        let credentials = login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR)
            .await
            .unwrap();
        assert_eq!(credentials.account_id, "acct-1");
        assert_eq!(
            ui.paste_rejections(),
            vec![RedirectInputError::MissingCode.to_string()]
        );
        assert_eq!(
            first_param(&http.seen_bodies(TOKEN_URL)[0], "code"),
            "pasted-code"
        );
    }

    #[tokio::test]
    async fn a_cancelled_re_prompt_ends_the_login() {
        let _registered_port = REDIRECT_PORT.lock().await;
        let http = token_http(&account_jwt(Some("acct-1")));
        let ui = ScriptedUi::with_pastes(vec![
            ScriptedAnswer::value(REDIRECT_URI),
            ScriptedAnswer::ready(),
        ]);
        let error = login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR)
            .await
            .unwrap_err();
        assert_eq!(error, LOGIN_CANCELLED);
        assert!(http.seen_bodies(TOKEN_URL).is_empty());
    }

    /// The busy-port path: another process holds 1455, the user is told
    /// why, and the paste still logs in.
    #[tokio::test]
    async fn a_busy_port_leaves_the_paste_path_that_still_logs_in() {
        let _registered_port = REDIRECT_PORT.lock().await;
        let Some(held) = stage_busy_registered_port() else {
            return; // the registered port is busy: this run cannot stage it.
        };
        let http = token_http(&account_jwt(Some("acct-1")));
        let ui = ScriptedUi::with_pastes(vec![ScriptedAnswer::Redirect(landed)]);
        let credentials = login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR)
            .await
            .unwrap();
        assert_eq!(credentials.account_id, "acct-1");
        let rejections = ui.rejections.lock().unwrap().clone();
        assert_eq!(rejections.len(), 1, "{rejections:?}");
        assert!(
            rejections[0].starts_with(
                "Port 1455 is busy, so the browser cannot hand the login back automatically"
            ),
            "{rejections:?}"
        );
        drop(held);
    }

    /// Without a paste surface the prompt answer is the only input: its
    /// rejection is the error.
    #[tokio::test]
    async fn an_empty_prompt_answer_reports_the_missing_code() {
        let _registered_port = REDIRECT_PORT.lock().await;
        let Some(held) = stage_busy_registered_port() else {
            return; // the registered port is busy: this run cannot stage it.
        };
        let http = token_http(&account_jwt(Some("acct-1")));
        let ui = ScriptedUi::new(None, ScriptedAnswer::value("  "));
        let error = login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR)
            .await
            .unwrap_err();
        assert_eq!(error, RedirectInputError::MissingCode.to_string());
        drop(held);
    }

    #[tokio::test]
    async fn a_dead_callback_falls_to_the_prompt_without_a_paste_surface() {
        let _registered_port = REDIRECT_PORT.lock().await;
        // The app registration's redirect port is the flow's wire
        // contract (a bind-anywhere test would not exercise it): the
        // staged listener blocks the flow's own bind, so its server is
        // dead by construction and the paste-free prompt is the only
        // path, settling in microseconds. A port that cannot be staged
        // this run skips the flow rather than races it.
        let Some(held) = stage_busy_registered_port() else {
            return; // the registered port is busy: this run cannot stage it.
        };
        let http = token_http(&account_jwt(Some("acct-1")));
        let ui = ScriptedUi::new(None, ScriptedAnswer::value("the-code"));
        let credentials = tokio::time::timeout(
            Duration::from_secs(10),
            login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR),
        )
        .await
        .expect("the dead-server flow settles promptly")
        .unwrap();
        assert_eq!(credentials.account_id, "acct-1");
        assert_eq!(
            first_param(&http.seen_bodies(TOKEN_URL)[0], "code"),
            "the-code"
        );
        drop(held);
    }

    /// The staging contract, pinned with the flow's own bind call: a
    /// listener from `stage_busy_registered_port` actively holds the
    /// registered port, so the flow's callback bind fails against it —
    /// the dead-server premise is a fact, not an assumption — and the
    /// released port hosts the bind again. Any staging that stops
    /// blocking (a probe-and-release shape, a freed port) reds here
    /// deterministically: that is the load window the registered
    /// settle red came from.
    #[tokio::test]
    async fn the_staged_registered_port_blocks_the_flow_bind() {
        let _registered_port = REDIRECT_PORT.lock().await;
        let Some(held) = stage_busy_registered_port() else {
            return; // the registered port is busy: this run cannot stage it.
        };
        let blocked = CodexCallbackServer::bind("127.0.0.1", 1455, "the-state").await;
        assert!(
            blocked.is_err(),
            "the staged port must block the flow's callback bind"
        );
        drop(held);
        let live = CodexCallbackServer::bind("127.0.0.1", 1455, "the-state").await;
        assert!(
            live.is_ok(),
            "the released port hosts the flow's callback bind again"
        );
    }

    /// The cancellation-aware-wait regression: a dead callback server
    /// plus a paste that never resolves — the surface's cancel flag (set
    /// by the paste's own first poll, standing in for the pane exit)
    /// must end the flow with the cancel, never hang the wait.
    #[tokio::test]
    async fn a_pending_paste_never_holds_a_cancelled_flow() {
        let _registered_port = REDIRECT_PORT.lock().await;
        // The same verified staging as the dead-callback test: the
        // premise must not be silent, and an unstaged port skips
        // instead of handing the flow a listener of its own.
        let Some(held) = stage_busy_registered_port() else {
            return; // the registered port is busy: this run cannot stage it.
        };
        let http = token_http(&account_jwt(Some("acct-1")));
        let ui = ScriptedUi::new(
            Some(ScriptedAnswer::PendingMarksCancel),
            ScriptedAnswer::Pending,
        );
        let error = tokio::time::timeout(
            Duration::from_secs(2),
            login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR),
        )
        .await
        .expect("the cancelled wait returns instead of hanging")
        .unwrap_err();
        assert_eq!(error, LOGIN_CANCELLED);
        assert!(http.seen_bodies(TOKEN_URL).is_empty());
        drop(held);
    }

    /// A login without a paste surface has no settle of its own while
    /// its callback server waits (the browser path is the only
    /// settler, live or dead), so the surface's cancel flag is the
    /// only bound. The flag flips from outside the flow here — the
    /// pane-exit shape (#2770) — and the login must end cancelled
    /// inside the poll bound with no exchange, whichever way its
    /// callback server's bind went.
    #[tokio::test]
    async fn a_cancelled_surface_ends_a_login_without_a_paste_surface() {
        let _registered_port = REDIRECT_PORT.lock().await;
        let http = token_http(&account_jwt(Some("acct-1")));
        let ui = ScriptedUi::new(None, ScriptedAnswer::Pending);
        let cancel = Arc::clone(&ui.cancelled);
        tokio::spawn(async move {
            tokio::time::sleep(Duration::from_millis(150)).await;
            cancel.store(true, Ordering::Relaxed);
        });
        let error = tokio::time::timeout(
            Duration::from_secs(2),
            login_openai_codex(&http, &ui, DEFAULT_ORIGINATOR),
        )
        .await
        .expect("the no-paste login ends on the surface's cancel")
        .unwrap_err();
        assert_eq!(error, LOGIN_CANCELLED);
        assert!(http.seen_bodies(TOKEN_URL).is_empty());
    }

    #[tokio::test]
    async fn the_browser_callback_wins_the_race() {
        let _registered_port = REDIRECT_PORT.lock().await;
        // The app registration's redirect port is the flow's wire
        // contract (a bind-anywhere test would not exercise the real
        // listener): the flow binds its callback server and the browser
        // redirect settles the code. Skip when another process holds the
        // port — the bind-failure path is covered above.
        let Ok(probe) = std::net::TcpListener::bind(("127.0.0.1", 1455)) else {
            return; // the registered port is busy: this run cannot stage it.
        };
        drop(probe);
        let http = Arc::new(token_http(&account_jwt(Some("acct-live"))));
        let ui = Arc::new(ScriptedUi::new(
            Some(ScriptedAnswer::Pending),
            ScriptedAnswer::Pending,
        ));
        let flow_ui = Arc::clone(&ui);
        let flow = {
            let flow_http = Arc::clone(&http);
            tokio::spawn(async move {
                login_openai_codex(flow_http.as_ref(), flow_ui.as_ref(), DEFAULT_ORIGINATOR).await
            })
        };
        let url = ui.captured_url().await;
        let state = url::Url::parse(&url)
            .unwrap()
            .query_pairs()
            .find(|(key, _)| key == "state")
            .map(|(_, value)| value.to_string())
            .expect("the authorization url carries the state");
        // The captured url implies the flow's bind already resolved (the
        // server starts before the url is presented), so a refused
        // connect here is a port stolen after the probe: wait for the
        // listener itself — observable readiness, bounded by a deadline
        // that fails the test (never a green-on-timeout retry loop).
        let deadline = std::time::Instant::now() + Duration::from_secs(1);
        let mut stream = loop {
            match tokio::net::TcpStream::connect(("127.0.0.1", 1455)).await {
                Ok(stream) => break stream,
                Err(error) => {
                    assert!(
                        std::time::Instant::now() < deadline,
                        "the flow's callback server never listened: {error}"
                    );
                    tokio::time::sleep(Duration::from_millis(5)).await;
                }
            }
        };
        stream
            .write_all(
                format!("GET /auth/callback?code=live-code&state={state} HTTP/1.1\r\nHost: localhost\r\n\r\n")
                    .as_bytes(),
            )
            .await
            .expect("the redirect writes");
        let credentials = tokio::time::timeout(Duration::from_secs(10), flow)
            .await
            .expect("the flow settles once the redirect lands")
            .unwrap()
            .unwrap();
        assert_eq!(credentials.account_id, "acct-live");
        assert_eq!(
            first_param(&http.seen_bodies(TOKEN_URL)[0], "code"),
            "live-code"
        );
    }

    #[test]
    fn the_authorization_url_carries_the_ts_parameters() {
        let url = authorization_url("the-challenge", "the-state", "pi");
        let parsed = url::Url::parse(&url).unwrap();
        assert_eq!(parsed.host_str(), Some("auth.openai.com"));
        assert_eq!(parsed.path(), "/oauth/authorize");
        let param = |name: &str| {
            parsed
                .query_pairs()
                .find(|(key, _)| key == name)
                .map(|(_, value)| value.to_string())
                .unwrap_or_default()
        };
        assert_eq!(param("response_type"), "code");
        assert_eq!(param("client_id"), OPENAI_CODEX_CLIENT_ID);
        assert_eq!(param("redirect_uri"), REDIRECT_URI);
        assert_eq!(param("scope"), SCOPE);
        assert_eq!(param("code_challenge"), "the-challenge");
        assert_eq!(param("code_challenge_method"), "S256");
        assert_eq!(param("state"), "the-state");
        assert_eq!(param("id_token_add_organizations"), "true");
        assert_eq!(param("codex_cli_simplified_flow"), "true");
        assert_eq!(param("originator"), "pi");
    }

    #[tokio::test]
    async fn the_pkce_pair_matches_the_ts_shapes() {
        let (verifier, challenge) = generate_pkce();
        assert_eq!(verifier.len(), 43);
        assert_eq!(
            challenge,
            base64url(Sha256::digest(verifier.as_bytes()).as_slice())
        );
        let state = create_state();
        assert_eq!(state.len(), 32);
        assert!(state.chars().all(|character| character.is_ascii_hexdigit()));
    }
}
