//! The interactive MCP OAuth login flow and its refresh path.
//!
//! One login: discover the server's OAuth metadata, register (or take) a
//! client, run the PKCE authorization-code flow against a local callback
//! server while racing a manual paste, exchange the code for tokens, and
//! hand back endpoint-bound credentials for `auth.json`. Refresh validates
//! every binding before asking the stored token endpoint again.
//!
//! With a paste surface, a rejected paste or browser hit and a failed
//! exchange re-prompt with the same verifier and state while the callback
//! keeps waiting; only a cancelled paste ends the login. Busy callback
//! ports leave the paste as the only path.

use std::future::Future;
use std::pin::{pin, Pin};

use anyhow::{anyhow, bail, Result};
use eukhe_ai::oauth::{exchange_retry_notice, parse_redirect_input};

use crate::auth::types::AuthCredential;

use super::oauth_callback::{
    redirect_uri_for, CallbackResult, CallbackServer, CALLBACK_PORT_BASE, CALLBACK_PORT_COUNT,
};
use super::oauth_discovery::{
    canonical_resource, discover, exchange_token, generate_pkce, random_state, register_client,
    validated_https_url, TokenResponse, TOKEN_EXPIRY_BUFFER_MS,
};
use super::oauth_http::OAuthHttp;
use url::Url;

/// One MCP server's OAuth setup: builtin catalog entries and `--oauth`
/// user servers both reduce to this.
#[derive(Debug, Clone, PartialEq)]
pub struct McpOAuthConfig {
    /// MCP server name; the credential lands under `mcp:<server>`.
    pub server: String,
    /// Human-readable label for progress and error messages.
    pub label: String,
    /// The MCP resource URL discovery starts from.
    pub url: String,
    /// Pre-registered client id (servers without dynamic registration).
    pub client_id: Option<String>,
    /// Requested scopes; defaults to the server's advertised scopes.
    pub scopes: Option<String>,
}

/// The interactive surface a login drives (the TS `OAuthLoginCallbacks`).
pub trait McpLoginUi: Send + Sync {
    /// Narration for slow steps (discovery, registration, exchange).
    fn on_progress(&self, message: &str);
    /// The authorization URL to open in a browser, plus instructions.
    fn on_auth(&self, url: &str, instructions: &str);
    /// Ask the user for one line of input (the callback fallback when no
    /// manual-paste surface exists). An error means the login was
    /// cancelled or the surface went away.
    fn on_prompt(
        &self,
        message: &str,
        placeholder: &str,
    ) -> Pin<Box<dyn Future<Output = Result<String>> + Send>>;
    /// The manual-paste channel racing the browser callback: `None` when
    /// the surface offers none. Resolving `None` cancels the login. The
    /// flow asks again after a rejected paste or a failed exchange, so
    /// each call mounts a fresh paste field.
    fn on_manual_code_input(&self) -> Option<Pin<Box<dyn Future<Output = Option<String>> + Send>>>;
    /// A paste, a browser hit, or an exchange failed but the login goes
    /// on: show `reason` where the paste field is (re-)mounted. Only
    /// flows with a paste surface call it; the panel shows a warning row
    /// that clears on the next submit.
    fn on_input_rejected(&self, reason: &str);
}

/// Wall-clock milliseconds since the epoch (the `expires` convention).
fn now_ms() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(i64::MAX, |elapsed| elapsed.as_millis() as i64)
}

/// Build the credential the flow persists. A missing `expires_in` defaults
/// to one hour; some servers omit `refresh_token` on refresh, so the prior
/// one is kept.
fn to_credentials(
    token: TokenResponse,
    token_endpoint: &str,
    client_id: &str,
    endpoint: Option<&str>,
    resource: Option<&str>,
    issuer: Option<&str>,
    previous_refresh: Option<&str>,
) -> AuthCredential {
    AuthCredential::Oauth {
        access: token.access_token,
        refresh: token
            .refresh_token
            .or_else(|| previous_refresh.map(str::to_string)),
        expires: now_ms()
            + token
                .expires_in
                .map_or(3600 * 1000, |seconds| seconds * 1000)
            - TOKEN_EXPIRY_BUFFER_MS,
        account_id: None,
        endpoint: endpoint.map(str::to_string),
        token_endpoint: Some(token_endpoint.to_string()),
        client_id: (!client_id.is_empty()).then(|| client_id.to_string()),
        resource: resource.map(str::to_string),
        issuer: issuer.map(str::to_string),
        enterprise_url: None,
    }
}

/// The authorization URL a login opens: the PKCE challenge, the CSRF state,
/// the callback redirect, the scopes, and the resource indicator.
fn authorization_url(endpoint: &str, params: &[(String, String)]) -> Result<String> {
    let mut url = Url::parse(endpoint).map_err(|_| anyhow!("Authorization endpoint is invalid"))?;
    for (name, value) in params {
        url.query_pairs_mut().append_pair(name, value);
    }
    Ok(url.to_string())
}

/// Run one interactive login for a server; the returned credential is
/// ready to persist under `mcp:<server>`.
///
/// # Errors
///
/// Returns an error when the discovery document cannot be fetched, the
/// server supports neither dynamic client registration nor a configured
/// client id, client registration fails, the authorization URL cannot be
/// built, or the paste is cancelled; without a paste surface also when no
/// callback port binds, the browser hit or prompt answer is rejected, or
/// the token exchange fails.
pub async fn mcp_login(
    http: &dyn OAuthHttp,
    config: &McpOAuthConfig,
    ui: &dyn McpLoginUi,
) -> Result<AuthCredential> {
    let discovery = discover(http, &config.url).await?;
    ui.on_progress(&format!(
        "Discovered {}",
        discovery
            .issuer
            .as_deref()
            .unwrap_or(discovery.metadata.issuer.as_str())
    ));

    let client_id = if let Some(client_id) = &config.client_id {
        client_id.clone()
    } else {
        let Some(registration_endpoint) = &discovery.metadata.registration_endpoint else {
            bail!(
                "{} does not support dynamic client registration and no clientId was \
                     configured. Set a pre-registered client id for this server.",
                config.label
            );
        };
        ui.on_progress("Registering OAuth client...");
        register_client(http, registration_endpoint, &config.label).await?
    };

    let (verifier, challenge) = generate_pkce();
    // `state` is independent of the PKCE verifier: the verifier is the
    // token-exchange secret, `state` is echoed on the redirect URL.
    let state = random_state();
    let callback = CallbackServer::start(&config.label, &state).await;
    // Every candidate is registered: with all ports busy the browser
    // still lands on the first one, whose address the user pastes.
    let redirect_uri = match &callback {
        Ok(server) => server.redirect_uri(),
        Err(_) => redirect_uri_for(CALLBACK_PORT_BASE),
    };

    let scope = config
        .scopes
        .clone()
        .or_else(|| {
            discovery
                .metadata
                .scopes_supported
                .as_ref()
                .map(|scopes| scopes.join(" "))
        })
        .unwrap_or_default();
    let mut auth_params: Vec<(String, String)> = vec![
        ("client_id".to_string(), client_id.clone()),
        ("response_type".to_string(), "code".to_string()),
        ("redirect_uri".to_string(), redirect_uri.clone()),
        ("code_challenge".to_string(), challenge),
        ("code_challenge_method".to_string(), "S256".to_string()),
        ("state".to_string(), state.clone()),
    ];
    if !scope.is_empty() {
        auth_params.push(("scope".to_string(), scope));
    }
    if let Some(resource) = &discovery.resource {
        auth_params.push(("resource".to_string(), resource.clone()));
    }
    let auth_url = authorization_url(&discovery.metadata.authorization_endpoint, &auth_params)?;
    ui.on_auth(
        &auth_url,
        "Complete login in your browser. On another machine, the browser ends on a localhost \
         page that fails to load: copy that page's full address and paste it below.",
    );

    // Race the local callback server against a manual paste (a browser on
    // another machine); whichever settles a valid code first wins.
    let mut manual = ui.on_manual_code_input();
    let paste_surface = manual.is_some();
    let (server, mut bind_error) = match callback {
        Ok(server) => (Some(server), None),
        Err(error) => {
            if paste_surface {
                ui.on_progress(&format!(
                    "Ports {CALLBACK_PORT_BASE}-{} are busy, so the browser cannot hand the \
                     login back automatically: paste the address of the page your browser ends \
                     on. ({error:#})",
                    CALLBACK_PORT_BASE + CALLBACK_PORT_COUNT - 1
                ));
            }
            (None, Some(error))
        }
    };
    let callback_live = server.is_some();
    let wait_once = || async {
        match &server {
            Some(server) => server.wait_for_code().await,
            // Never polled: the race arm is off without a server.
            None => std::future::pending::<CallbackResult>().await,
        }
    };
    let mut wait = pin!(wait_once());
    loop {
        let code = loop {
            if !callback_live && manual.is_none() {
                // No browser hand-back and no paste surface: the blocking
                // prompt is the only input (a refusing surface reports the
                // port failure that left it).
                let input = match ui
                    .on_prompt(
                        "Paste the authorization code or full redirect URL:",
                        &redirect_uri,
                    )
                    .await
                {
                    Ok(input) => input,
                    Err(prompt_error) => return Err(bind_error.take().unwrap_or(prompt_error)),
                };
                break parse_redirect_input(&input)
                    .and_then(|pasted| pasted.verify_state(&state))?;
            }
            let step = tokio::select! {
                settled = &mut wait, if callback_live => RaceStep::Callback(settled),
                answer = async {
                    match manual.as_mut() {
                        Some(field) => field.await,
                        None => std::future::pending().await,
                    }
                }, if manual.is_some() => RaceStep::Paste(answer),
            };
            match step {
                // The wait re-arms for the next browser hit either way.
                RaceStep::Callback(Ok(code)) => {
                    wait.set(wait_once());
                    break code;
                }
                RaceStep::Callback(Err(rejected)) => {
                    wait.set(wait_once());
                    if !paste_surface {
                        return Err(rejected.into());
                    }
                    // The pending paste field stays; the notice says why
                    // the browser did not finish the login.
                    ui.on_input_rejected(&rejected.to_string());
                }
                RaceStep::Paste(None) => bail!("Login cancelled"),
                RaceStep::Paste(Some(input)) => {
                    match parse_redirect_input(&input)
                        .and_then(|pasted| pasted.verify_state(&state))
                    {
                        Ok(accepted) => break accepted,
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

        ui.on_progress("Exchanging authorization code for tokens...");
        let mut token_params: Vec<(String, String)> = vec![
            ("grant_type".to_string(), "authorization_code".to_string()),
            ("code".to_string(), code.code),
            ("redirect_uri".to_string(), redirect_uri.clone()),
            ("client_id".to_string(), client_id.clone()),
            ("code_verifier".to_string(), verifier.clone()),
        ];
        if let Some(resource) = &discovery.resource {
            token_params.push(("resource".to_string(), resource.clone()));
        }
        match exchange_token(http, &discovery.metadata.token_endpoint, &token_params).await {
            Ok(token) => {
                return Ok(to_credentials(
                    token,
                    &discovery.metadata.token_endpoint,
                    &client_id,
                    Some(&config.url),
                    discovery.resource.as_deref(),
                    discovery.issuer.as_deref(),
                    None,
                ));
            }
            Err(error) if paste_surface => {
                ui.on_input_rejected(&exchange_retry_notice(&format!("{error:#}")));
                manual = ui.on_manual_code_input();
            }
            Err(error) => return Err(error),
        }
    }
}

/// One step of the race: the browser callback or the paste answer.
enum RaceStep {
    Callback(CallbackResult),
    /// The paste answered: the input, or `None` when cancelled.
    Paste(Option<String>),
}

/// Refresh stored credentials. Every binding the login established must
/// still hold; anything drifted requires a fresh login.
///
/// # Errors
///
/// Returns an error when the stored credential is not OAuth, is no longer
/// bound to the same endpoint, resource, issuer, or token endpoint, carries
/// no refresh token, when discovery fails or changed modes, or when the
/// token exchange fails.
///
/// # Panics
///
/// The `expect` on the discovery resource is unreachable: the discovery-mode
/// check above it already rejects a mode mismatch.
pub async fn mcp_refresh_token(
    http: &dyn OAuthHttp,
    config: &McpOAuthConfig,
    credentials: &AuthCredential,
) -> Result<AuthCredential> {
    let AuthCredential::Oauth {
        refresh,
        endpoint,
        token_endpoint,
        client_id,
        resource,
        issuer,
        ..
    } = credentials
    else {
        bail!(
            "Stored credentials for {} are not OAuth; re-run /mcp login {}",
            config.label,
            config.server
        );
    };
    if endpoint.as_deref() != Some(config.url.as_str()) {
        bail!(
            "Stored OAuth credentials are not bound to {}; re-run /mcp login {}",
            config.url,
            config.server
        );
    }
    if let Some(stored_resource) = resource {
        let configured = canonical_resource(&validated_https_url(&config.url, "MCP endpoint")?);
        if stored_resource != &configured {
            bail!(
                "Stored OAuth credentials are not bound to {configured}; re-run /mcp login {}",
                config.server
            );
        }
    }
    match (resource.is_some(), issuer.is_some()) {
        (true, true) | (false, false) => {}
        _ => bail!(
            "Stored OAuth credentials for {} have incomplete resource binding; re-run /mcp \
             login {}",
            config.label,
            config.server
        ),
    }
    if let Some(issuer) = issuer {
        validated_https_url(issuer, "Stored authorization server issuer")?;
    }
    let Some(refresh_token) = refresh.as_deref().filter(|token| !token.is_empty()) else {
        bail!(
            "No refresh token stored for {}; re-run /mcp login {}",
            config.label,
            config.server
        );
    };

    let discovery = discover(http, &config.url).await?;
    if resource.is_some() != discovery.resource.is_some() {
        bail!(
            "OAuth discovery mode changed for {}; re-run /mcp login {}",
            config.url,
            config.server
        );
    }
    if let Some(stored_resource) = resource {
        let current_resource = discovery
            .resource
            .as_deref()
            .expect("mode change rejected above");
        if stored_resource != current_resource || issuer.as_deref() != discovery.issuer.as_deref() {
            bail!(
                "Stored OAuth credentials do not match current protected-resource metadata \
                 for {}",
                config.url
            );
        }
    }
    let stored_token_endpoint = token_endpoint.clone();
    let token_endpoint = stored_token_endpoint
        .clone()
        .unwrap_or_else(|| discovery.metadata.token_endpoint.clone());
    if let Some(stored_endpoint) = stored_token_endpoint {
        if stored_endpoint != discovery.metadata.token_endpoint {
            bail!(
                "Stored OAuth token endpoint does not match current authorization-server \
                 metadata for {}",
                config.url
            );
        }
    }
    let client_id = client_id
        .clone()
        .or_else(|| config.client_id.clone())
        .unwrap_or_default();
    if token_endpoint.is_empty() {
        bail!(
            "No token endpoint stored for {}; re-run /mcp login {}",
            config.label,
            config.server
        );
    }
    let mut refresh_params: Vec<(String, String)> = vec![
        ("grant_type".to_string(), "refresh_token".to_string()),
        ("refresh_token".to_string(), refresh_token.to_string()),
    ];
    if !client_id.is_empty() {
        refresh_params.push(("client_id".to_string(), client_id.clone()));
    }
    if let Some(resource) = resource {
        refresh_params.push(("resource".to_string(), resource.clone()));
    }
    let token = exchange_token(http, &token_endpoint, &refresh_params).await?;
    Ok(to_credentials(
        token,
        &token_endpoint,
        &client_id,
        endpoint.as_deref(),
        resource.as_deref(),
        issuer.as_deref(),
        refresh.as_deref(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mcp::oauth_http::{OAuthHttpRequest, OAuthHttpResponse};
    use eukhe_ai::oauth::RedirectInputError;
    use std::collections::{HashMap, VecDeque};
    use std::sync::Mutex;

    /// A scripted transport: url -> queued responses (the last one
    /// repeats). Unknown urls fail the request (the TS suite throws on
    /// unexpected fetches).
    struct ScriptedHttp {
        responses: Mutex<HashMap<String, VecDeque<OAuthHttpResponse>>>,
        seen: Mutex<Vec<(String, Option<String>)>>,
    }

    impl ScriptedHttp {
        fn new(responses: Vec<(&str, u16, Option<&str>, &str)>) -> Self {
            let mut queued: HashMap<String, VecDeque<OAuthHttpResponse>> = HashMap::new();
            for (url, status, header, body) in responses {
                let mut headers =
                    vec![("content-type".to_string(), "application/json".to_string())];
                if let Some(header) = header {
                    headers.push(("www-authenticate".to_string(), header.to_string()));
                }
                queued
                    .entry(url.to_string())
                    .or_default()
                    .push_back(OAuthHttpResponse {
                        status,
                        headers,
                        body: body.to_string(),
                    });
            }
            ScriptedHttp {
                responses: Mutex::new(queued),
                seen: Mutex::new(Vec::new()),
            }
        }

        fn bodies(&self, url: &str) -> Vec<String> {
            self.seen
                .lock()
                .unwrap()
                .iter()
                .filter(|(seen, _)| seen == url)
                .map(|(_, body)| body.clone().unwrap_or_default())
                .collect()
        }
    }

    impl OAuthHttp for ScriptedHttp {
        fn request(
            &self,
            request: OAuthHttpRequest,
        ) -> futures::future::BoxFuture<'_, Result<OAuthHttpResponse>> {
            Box::pin(async move {
                self.seen
                    .lock()
                    .unwrap()
                    .push((request.url.clone(), request.body.clone()));
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
                response.ok_or_else(|| anyhow!("unexpected request: {}", request.url))
            })
        }
    }

    fn json_response(body: &serde_json::Value) -> String {
        body.to_string()
    }

    /// A login UI with a manual-paste surface: the paste is derived from
    /// the authorization URL the way a user would (their own redirect URL
    /// plus the code), after an optional fixed first input; `pending`
    /// holds every field open instead (the browser path wins). Rejections
    /// and dropped fields are recorded.
    struct TestUi {
        auth_url: Mutex<String>,
        manual: Mutex<Option<String>>,
        pending: bool,
        progress: Mutex<Vec<String>>,
        rejections: Mutex<Vec<String>>,
        dropped_fields: std::sync::Arc<std::sync::atomic::AtomicUsize>,
    }

    /// Counts a dropped pending field.
    struct DropCounter(std::sync::Arc<std::sync::atomic::AtomicUsize>);

    impl Drop for DropCounter {
        fn drop(&mut self) {
            self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        }
    }

    impl TestUi {
        fn with_manual_input(input: &str) -> Self {
            TestUi {
                manual: Mutex::new(Some(input.to_string())),
                ..TestUi::from_auth_url()
            }
        }
        fn from_auth_url() -> Self {
            TestUi {
                auth_url: Mutex::new(String::new()),
                manual: Mutex::new(None),
                pending: false,
                progress: Mutex::new(Vec::new()),
                rejections: Mutex::new(Vec::new()),
                dropped_fields: std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0)),
            }
        }
        fn rejections(&self) -> Vec<String> {
            self.rejections.lock().unwrap().clone()
        }
        fn auth_param(&self, name: &str) -> Option<String> {
            Url::parse(&self.auth_url.lock().unwrap())
                .ok()?
                .query_pairs()
                .find(|(key, _)| key == name)
                .map(|(_, value)| value.to_string())
        }
    }

    impl McpLoginUi for std::sync::Arc<TestUi> {
        fn on_progress(&self, message: &str) {
            self.progress.lock().unwrap().push(message.to_string());
        }
        fn on_auth(&self, url: &str, _instructions: &str) {
            *self.auth_url.lock().unwrap() = url.to_string();
        }
        fn on_prompt(
            &self,
            _message: &str,
            _placeholder: &str,
        ) -> Pin<Box<dyn Future<Output = Result<String>> + Send>> {
            Box::pin(async { Err(anyhow!("prompt surface unavailable in tests")) })
        }
        fn on_manual_code_input(
            &self,
        ) -> Option<Pin<Box<dyn Future<Output = Option<String>> + Send>>> {
            if self.pending {
                let counter = DropCounter(std::sync::Arc::clone(&self.dropped_fields));
                return Some(Box::pin(async move {
                    let _counter = counter;
                    std::future::pending::<Option<String>>().await
                }));
            }
            // The paste surface exists once a login is live (the surface
            // resolves from the authorization URL like a user would).
            let ui = std::sync::Arc::clone(self);
            Some(Box::pin(async move {
                if let Some(input) = ui.manual.lock().unwrap().take() {
                    return Some(input);
                }
                let redirect = ui.auth_param("redirect_uri")?;
                let state = ui.auth_param("state")?;
                Some(format!("{redirect}?code=the-code&state={state}"))
            }))
        }
        fn on_input_rejected(&self, reason: &str) {
            self.rejections.lock().unwrap().push(reason.to_string());
        }
    }

    fn test_ui() -> std::sync::Arc<TestUi> {
        std::sync::Arc::new(TestUi::from_auth_url())
    }

    const RESOURCE: &str = "https://mcp.plane.so/http/mcp";
    const PLANE_ISSUER: &str = "https://mcp.plane.so/http";
    const PLANE_PRM_URL: &str =
        "https://mcp.plane.so/.well-known/oauth-protected-resource/http/mcp";
    const PLANE_META_URL: &str = "https://mcp.plane.so/.well-known/oauth-authorization-server/http";
    const PLANE_REGISTER: &str = "https://mcp.plane.so/http/register";
    const PLANE_TOKEN: &str = "https://mcp.plane.so/http/token";
    const PLANE_AUTHORIZE: &str = "https://mcp.plane.so/http/authorize";
    const ORIGIN_URL: &str = "https://srv.test/mcp";
    const ORIGIN_META_URL: &str = "https://srv.test/.well-known/oauth-authorization-server";
    const ORIGIN_AUTHORIZE: &str = "https://srv.test/authorize";
    const ORIGIN_REGISTER: &str = "https://srv.test/register";
    const ORIGIN_TOKEN: &str = "https://srv.test/token";

    fn plane_meta() -> serde_json::Value {
        serde_json::json!({
            "issuer": PLANE_ISSUER,
            "authorization_endpoint": PLANE_AUTHORIZE,
            "token_endpoint": PLANE_TOKEN,
            "registration_endpoint": PLANE_REGISTER,
            "scopes_supported": ["read", "write"],
        })
    }

    fn origin_meta() -> serde_json::Value {
        serde_json::json!({
            "issuer": "https://srv.test/tenant",
            "authorization_endpoint": ORIGIN_AUTHORIZE,
            "token_endpoint": ORIGIN_TOKEN,
            "registration_endpoint": ORIGIN_REGISTER,
            "scopes_supported": ["read", "write"],
        })
    }

    fn config(server: &str, url: &str) -> McpOAuthConfig {
        McpOAuthConfig {
            server: server.to_string(),
            label: server.to_string(),
            url: url.to_string(),
            client_id: None,
            scopes: None,
        }
    }

    /// PRM metadata, its issuer's metadata, DCR, and the token endpoint —
    /// the full Plane-style login through a manual paste.
    #[tokio::test]
    async fn discovers_protected_resource_metadata_and_external_issuer() {
        let http = ScriptedHttp::new(vec![
            (RESOURCE, 401, None, ""),
            (
                PLANE_PRM_URL,
                200,
                None,
                &json_response(&serde_json::json!({
                    "resource": RESOURCE,
                    "authorization_servers": [PLANE_ISSUER],
                })),
            ),
            (PLANE_META_URL, 200, None, &json_response(&plane_meta())),
            (
                PLANE_REGISTER,
                200,
                None,
                &json_response(&serde_json::json!({ "client_id": "plane-client" })),
            ),
            (
                PLANE_TOKEN,
                200,
                None,
                &json_response(&serde_json::json!({
                    "access_token": "access-1",
                    "refresh_token": "refresh-1",
                    "expires_in": 3600,
                })),
            ),
        ]);
        let ui = test_ui();
        let credentials = mcp_login(&http, &config("plane", RESOURCE), &ui)
            .await
            .unwrap();
        match &credentials {
            AuthCredential::Oauth {
                access,
                refresh,
                endpoint,
                token_endpoint,
                client_id,
                resource,
                issuer,
                ..
            } => {
                assert_eq!(access, "access-1");
                assert_eq!(refresh.as_deref(), Some("refresh-1"));
                assert_eq!(endpoint.as_deref(), Some(RESOURCE));
                assert_eq!(token_endpoint.as_deref(), Some(PLANE_TOKEN));
                assert_eq!(client_id.as_deref(), Some("plane-client"));
                assert_eq!(resource.as_deref(), Some(RESOURCE));
                assert_eq!(issuer.as_deref(), Some(PLANE_ISSUER));
            }
            other => panic!("oauth credential expected, got {other:?}"),
        }
        // The authorization URL carries the client, the resource, and the
        // server's advertised scopes.
        let auth_url = Url::parse(&ui.auth_url.lock().unwrap()).unwrap();
        let param = |name: &str| {
            auth_url
                .query_pairs()
                .find(|(key, _)| key == name)
                .map(|(_, value)| value.to_string())
        };
        assert_eq!(param("client_id").as_deref(), Some("plane-client"));
        assert_eq!(param("resource").as_deref(), Some(RESOURCE));
        assert_eq!(param("scope").as_deref(), Some("read write"));
        assert_eq!(param("code_challenge_method").as_deref(), Some("S256"));
        // The token request carried the resource indicator.
        let token_request = http
            .seen
            .lock()
            .unwrap()
            .iter()
            .find(|(url, _)| url == PLANE_TOKEN)
            .cloned()
            .unwrap();
        let body = token_request.1.unwrap();
        assert!(body.contains("grant_type=authorization_code"));
        let encoded_resource = url::form_urlencoded::Serializer::new(String::new())
            .append_pair("resource", RESOURCE)
            .finish();
        assert!(body.contains(&encoded_resource));
    }

    /// Origin-level discovery when the server serves no RFC 9728 metadata.
    #[tokio::test]
    async fn origin_level_metadata_without_protected_resource() {
        let origin_prm = "https://srv.test/.well-known/oauth-protected-resource/mcp";
        let http = ScriptedHttp::new(vec![
            (ORIGIN_URL, 404, None, ""),
            (origin_prm, 404, None, ""),
            (ORIGIN_META_URL, 200, None, &json_response(&origin_meta())),
            (
                ORIGIN_REGISTER,
                200,
                None,
                &json_response(&serde_json::json!({ "client_id": "origin-client" })),
            ),
            (
                ORIGIN_TOKEN,
                200,
                None,
                &json_response(&serde_json::json!({
                    "access_token": "origin-access",
                    "refresh_token": "origin-refresh",
                    "expires_in": 3600,
                })),
            ),
        ]);
        let ui = test_ui();
        let credentials = mcp_login(&http, &config("origin", ORIGIN_URL), &ui)
            .await
            .unwrap();
        match &credentials {
            AuthCredential::Oauth {
                access,
                endpoint,
                resource,
                issuer,
                ..
            } => {
                assert_eq!(access, "origin-access");
                assert_eq!(endpoint.as_deref(), Some(ORIGIN_URL));
                assert_eq!(*resource, None);
                assert_eq!(*issuer, None);
            }
            other => panic!("oauth credential expected, got {other:?}"),
        }
        // No resource parameter on the authorization URL.
        let auth_url = Url::parse(&ui.auth_url.lock().unwrap()).unwrap();
        assert!(!auth_url.query_pairs().any(|(key, _)| key == "resource"));
        // The root PRM location is never probed for a pathful resource.
        let urls: Vec<String> = http
            .seen
            .lock()
            .unwrap()
            .iter()
            .map(|(url, _)| url.clone())
            .collect();
        assert!(
            !urls.contains(&"https://srv.test/.well-known/oauth-protected-resource".to_string())
        );
    }

    /// A `WWW-Authenticate` resource pointer wins over the derived location.
    #[tokio::test]
    async fn www_authenticate_pointer_preferred() {
        let pointer = "https://metadata.example/resources/plane";
        let http = ScriptedHttp::new(vec![
            (
                RESOURCE,
                401,
                Some(
                    r#"Bearer realm="mcp", resource_metadata="https://metadata.example/resources/plane""#,
                ),
                "",
            ),
            (
                pointer,
                200,
                None,
                &json_response(&serde_json::json!({
                    "resource": RESOURCE,
                    "authorization_servers": [PLANE_ISSUER],
                })),
            ),
            (PLANE_META_URL, 200, None, &json_response(&plane_meta())),
            (
                PLANE_REGISTER,
                200,
                None,
                &json_response(&serde_json::json!({ "client_id": "pointer-client" })),
            ),
            (
                PLANE_TOKEN,
                200,
                None,
                &json_response(&serde_json::json!({ "access_token": "pointer-access" })),
            ),
        ]);
        let ui = test_ui();
        let credentials = mcp_login(&http, &config("plane", RESOURCE), &ui)
            .await
            .unwrap();
        match &credentials {
            AuthCredential::Oauth {
                access,
                resource,
                issuer,
                ..
            } => {
                assert_eq!(access, "pointer-access");
                assert_eq!(resource.as_deref(), Some(RESOURCE));
                assert_eq!(issuer.as_deref(), Some(PLANE_ISSUER));
            }
            other => panic!("oauth credential expected, got {other:?}"),
        }
        // The derived PRM URL was never fetched.
        let urls: Vec<String> = http
            .seen
            .lock()
            .unwrap()
            .iter()
            .map(|(url, _)| url.clone())
            .collect();
        assert!(!urls.contains(&PLANE_PRM_URL.to_string()));
    }

    /// Metadata for a different resource fails closed.
    #[tokio::test]
    async fn protected_resource_mismatch_fails() {
        let http = ScriptedHttp::new(vec![
            (RESOURCE, 401, None, ""),
            (
                PLANE_PRM_URL,
                200,
                None,
                &json_response(&serde_json::json!({
                    "resource": "https://attacker.example/mcp",
                    "authorization_servers": [PLANE_ISSUER],
                })),
            ),
        ]);
        let error = mcp_login(&http, &config("plane", RESOURCE), &test_ui())
            .await
            .unwrap_err()
            .to_string();
        assert!(error.contains("resource does not exactly match"), "{error}");
    }

    /// An issuer that does not exactly match the PRM-selected one fails.
    #[tokio::test]
    async fn prm_selected_issuer_must_match_exactly() {
        let http = ScriptedHttp::new(vec![
            (RESOURCE, 401, None, ""),
            (
                PLANE_PRM_URL,
                200,
                None,
                &json_response(&serde_json::json!({
                    "resource": RESOURCE,
                    "authorization_servers": [PLANE_ISSUER],
                })),
            ),
            (
                PLANE_META_URL,
                200,
                None,
                &json_response(&serde_json::json!({
                    "issuer": "https://wrong.example",
                    "authorization_endpoint": PLANE_AUTHORIZE,
                    "token_endpoint": PLANE_TOKEN,
                })),
            ),
            (
                "https://mcp.plane.so/http/.well-known/openid-configuration",
                404,
                None,
                "",
            ),
        ]);
        let error = mcp_login(&http, &config("plane", RESOURCE), &test_ui())
            .await
            .unwrap_err()
            .to_string();
        assert!(error.contains("issuer does not exactly match"), "{error}");
    }

    /// Pathful OIDC metadata when RFC 8414 serves a non-metadata document.
    #[tokio::test]
    async fn pathful_oidc_fallback() {
        let issuer = "https://login.example/tenant";
        let oidc_meta = "https://login.example/tenant/.well-known/openid-configuration";
        let oidc = serde_json::json!({
            "issuer": issuer,
            "authorization_endpoint": "https://login.example/tenant/authorize",
            "token_endpoint": "https://login.example/tenant/token",
            "registration_endpoint": "https://login.example/tenant/register",
            "scopes_supported": ["read", "write"],
        });
        let http = ScriptedHttp::new(vec![
            (RESOURCE, 404, None, ""),
            (
                PLANE_PRM_URL,
                200,
                None,
                &json_response(&serde_json::json!({
                    "resource": RESOURCE,
                    "authorization_servers": [issuer],
                })),
            ),
            (
                "https://login.example/.well-known/oauth-authorization-server/tenant",
                200,
                None,
                "<html>not metadata</html>",
            ),
            (oidc_meta, 200, None, &json_response(&oidc)),
            (
                "https://login.example/tenant/register",
                200,
                None,
                &json_response(&serde_json::json!({ "client_id": "c" })),
            ),
            (
                "https://login.example/tenant/token",
                200,
                None,
                &json_response(&serde_json::json!({ "access_token": "a", "expires_in": 60 })),
            ),
        ]);
        let credentials = mcp_login(&http, &config("plane", RESOURCE), &test_ui())
            .await
            .unwrap();
        match &credentials {
            AuthCredential::Oauth {
                resource, issuer, ..
            } => {
                assert_eq!(resource.as_deref(), Some(RESOURCE));
                assert_eq!(issuer.as_deref(), Some("https://login.example/tenant"));
            }
            other => panic!("oauth credential expected, got {other:?}"),
        }
    }

    /// Servers without a registration endpoint need a pre-registered id.
    #[tokio::test]
    async fn dynamic_registration_unavailable_fails_clearly() {
        let meta = serde_json::json!({
            "issuer": "https://srv.test/tenant",
            "authorization_endpoint": ORIGIN_AUTHORIZE,
            "token_endpoint": ORIGIN_TOKEN,
        });
        let origin_prm = "https://srv.test/.well-known/oauth-protected-resource/mcp";
        let http = ScriptedHttp::new(vec![
            (ORIGIN_URL, 404, None, ""),
            (origin_prm, 404, None, ""),
            (ORIGIN_META_URL, 200, None, &json_response(&meta)),
        ]);
        let error = mcp_login(&http, &config("slackish", ORIGIN_URL), &test_ui())
            .await
            .unwrap_err()
            .to_string();
        assert!(error.contains("dynamic client registration"), "{error}");
    }

    /// A redirected token POST fails instead of following the redirect.
    #[tokio::test]
    async fn redirected_token_post_rejected() {
        let credentials = AuthCredential::Oauth {
            access: "a".to_string(),
            refresh: Some("r".to_string()),
            expires: 0,
            account_id: None,
            endpoint: Some(ORIGIN_URL.to_string()),
            token_endpoint: Some(ORIGIN_TOKEN.to_string()),
            client_id: Some("c".to_string()),
            resource: None,
            issuer: None,
            enterprise_url: None,
        };
        let origin_prm = "https://srv.test/.well-known/oauth-protected-resource/mcp";
        let http = ScriptedHttp::new(vec![
            (ORIGIN_URL, 404, None, ""),
            (origin_prm, 404, None, ""),
            (ORIGIN_META_URL, 200, None, &json_response(&origin_meta())),
            (ORIGIN_TOKEN, 302, None, "redirect"),
        ]);
        let error = mcp_refresh_token(&http, &config("origin", ORIGIN_URL), &credentials)
            .await
            .unwrap_err()
            .to_string();
        assert!(error.contains("Token request to"), "{error}");
    }

    /// Refresh keeps the stored bindings and the resource indicator, and
    /// keeps the prior refresh token when the server omits a new one.
    #[tokio::test]
    async fn refresh_validates_bindings() {
        let credentials = AuthCredential::Oauth {
            access: "access-1".to_string(),
            refresh: Some("old-refresh".to_string()),
            expires: 0,
            account_id: None,
            endpoint: Some(RESOURCE.to_string()),
            token_endpoint: Some(PLANE_TOKEN.to_string()),
            client_id: Some("client-xyz".to_string()),
            resource: Some(RESOURCE.to_string()),
            issuer: Some(PLANE_ISSUER.to_string()),
            enterprise_url: None,
        };
        let http = ScriptedHttp::new(vec![
            (RESOURCE, 401, None, ""),
            (
                PLANE_PRM_URL,
                200,
                None,
                &json_response(&serde_json::json!({
                    "resource": RESOURCE,
                    "authorization_servers": [PLANE_ISSUER],
                })),
            ),
            (PLANE_META_URL, 200, None, &json_response(&plane_meta())),
            (
                PLANE_TOKEN,
                200,
                None,
                &json_response(&serde_json::json!({
                    "access_token": "access-2",
                    "expires_in": 1800,
                })),
            ),
        ]);
        let refreshed = mcp_refresh_token(&http, &config("plane", RESOURCE), &credentials)
            .await
            .unwrap();
        match &refreshed {
            AuthCredential::Oauth {
                access,
                refresh,
                endpoint,
                resource,
                issuer,
                token_endpoint,
                ..
            } => {
                assert_eq!(access, "access-2");
                // Some servers omit refresh_token on refresh; the prior one
                // stays.
                assert_eq!(refresh.as_deref(), Some("old-refresh"));
                assert_eq!(endpoint.as_deref(), Some(RESOURCE));
                assert_eq!(resource.as_deref(), Some(RESOURCE));
                assert_eq!(issuer.as_deref(), Some(PLANE_ISSUER));
                assert_eq!(token_endpoint.as_deref(), Some(PLANE_TOKEN));
            }
            other => panic!("oauth credential expected, got {other:?}"),
        }
        // The refresh request carried the resource and the stored client.
        let token_request = http
            .seen
            .lock()
            .unwrap()
            .iter()
            .find(|(url, _)| url == PLANE_TOKEN)
            .cloned()
            .unwrap();
        let body = token_request.1.unwrap();
        assert!(body.contains("grant_type=refresh_token"));
        assert!(body.contains("refresh_token=old-refresh"));
        assert!(body.contains("client_id=client-xyz"));

        // A different endpoint requires a fresh login.
        let retargeted = AuthCredential::Oauth {
            access: "a".to_string(),
            refresh: Some("r".to_string()),
            expires: 0,
            account_id: None,
            endpoint: Some("https://other.test/mcp".to_string()),
            token_endpoint: None,
            client_id: None,
            resource: None,
            issuer: None,
            enterprise_url: None,
        };
        let error = mcp_refresh_token(&http, &config("plane", RESOURCE), &retargeted)
            .await
            .unwrap_err()
            .to_string();
        assert!(error.contains("not bound"), "{error}");

        // A stored token endpoint that drifted from current metadata is
        // refused without ever being contacted.
        let drifted = AuthCredential::Oauth {
            access: "a".to_string(),
            refresh: Some("r".to_string()),
            expires: 0,
            account_id: None,
            endpoint: Some(RESOURCE.to_string()),
            token_endpoint: Some("https://attacker.example/token".to_string()),
            client_id: Some("client-xyz".to_string()),
            resource: Some(RESOURCE.to_string()),
            issuer: Some(PLANE_ISSUER.to_string()),
            enterprise_url: None,
        };
        let error = mcp_refresh_token(&http, &config("plane", RESOURCE), &drifted)
            .await
            .unwrap_err()
            .to_string();
        assert!(error.contains("token endpoint does not match"), "{error}");
        let urls: Vec<String> = http
            .seen
            .lock()
            .unwrap()
            .iter()
            .map(|(url, _)| url.clone())
            .collect();
        assert!(!urls.contains(&"https://attacker.example/token".to_string()));
    }

    /// A discovery-mode change (origin-only credentials against a
    /// resource-bound server) requires a fresh login.
    #[tokio::test]
    async fn discovery_mode_change_requires_relogin() {
        let credentials = AuthCredential::Oauth {
            access: "origin-access".to_string(),
            refresh: Some("origin-refresh".to_string()),
            expires: 0,
            account_id: None,
            endpoint: Some(RESOURCE.to_string()),
            token_endpoint: Some(PLANE_TOKEN.to_string()),
            client_id: Some("origin-client".to_string()),
            resource: None,
            issuer: None,
            enterprise_url: None,
        };
        let http = ScriptedHttp::new(vec![
            (RESOURCE, 401, None, ""),
            (
                PLANE_PRM_URL,
                200,
                None,
                &json_response(&serde_json::json!({
                    "resource": RESOURCE,
                    "authorization_servers": [PLANE_ISSUER],
                })),
            ),
            (PLANE_META_URL, 200, None, &json_response(&plane_meta())),
        ]);
        let error = mcp_refresh_token(&http, &config("plane", RESOURCE), &credentials)
            .await
            .unwrap_err()
            .to_string();
        assert!(error.contains("discovery mode changed"), "{error}");
        let urls: Vec<String> = http
            .seen
            .lock()
            .unwrap()
            .iter()
            .map(|(url, _)| url.clone())
            .collect();
        assert!(!urls.contains(&PLANE_TOKEN.to_string()));
    }

    /// The origin-level fixture: discovery, registration, and the token
    /// endpoint's queued answers.
    fn origin_http(token_answers: Vec<(u16, &str)>) -> ScriptedHttp {
        let mut responses = vec![
            (ORIGIN_URL, 404, None, ""),
            (
                "https://srv.test/.well-known/oauth-protected-resource/mcp",
                404,
                None,
                "",
            ),
        ];
        let meta = json_response(&origin_meta());
        let client = json_response(&serde_json::json!({ "client_id": "c" }));
        responses.push((ORIGIN_META_URL, 200, None, meta.as_str()));
        responses.push((ORIGIN_REGISTER, 200, None, client.as_str()));
        for (status, body) in token_answers {
            responses.push((ORIGIN_TOKEN, status, None, body));
        }
        ScriptedHttp::new(responses)
    }

    fn token_param(body: &str, name: &str) -> Option<String> {
        url::form_urlencoded::parse(body.as_bytes())
            .find(|(key, _)| key == name)
            .map(|(_, value)| value.to_string())
    }

    /// The wrong-tab regression: a paste carrying another login's state
    /// is a notice and a fresh field, never a failed login; the right
    /// paste then exchanges exactly once with this login's redirect and
    /// verifier.
    #[tokio::test]
    async fn a_wrong_state_paste_re_prompts_then_the_right_one_logs_in() {
        let http = origin_http(vec![(200, r#"{"access_token":"origin-access"}"#)]);
        let ui = std::sync::Arc::new(TestUi::with_manual_input(
            "http://localhost:53700/callback?code=stolen&state=other",
        ));
        let credentials = mcp_login(&http, &config("origin", ORIGIN_URL), &ui)
            .await
            .unwrap();
        assert!(matches!(
            &credentials,
            AuthCredential::Oauth { access, .. } if access == "origin-access"
        ));
        assert_eq!(
            ui.rejections(),
            vec![RedirectInputError::StateMismatch.to_string()]
        );
        let bodies = http.bodies(ORIGIN_TOKEN);
        assert_eq!(bodies.len(), 1);
        assert_eq!(token_param(&bodies[0], "code").as_deref(), Some("the-code"));
        assert_eq!(
            token_param(&bodies[0], "redirect_uri"),
            ui.auth_param("redirect_uri")
        );
        assert!(token_param(&bodies[0], "code_verifier").is_some());
    }

    /// A failed exchange keeps the login open: the endpoint's status and
    /// body land as the notice, and the retried paste logs in with the
    /// same verifier.
    #[tokio::test]
    async fn a_failed_exchange_re_prompts_and_the_retry_logs_in() {
        let http = origin_http(vec![
            (400, r#"{"error":"invalid_grant"}"#),
            (200, r#"{"access_token":"origin-access"}"#),
        ]);
        let ui = test_ui();
        mcp_login(&http, &config("origin", ORIGIN_URL), &ui)
            .await
            .unwrap();
        assert_eq!(
            ui.rejections(),
            vec![exchange_retry_notice(&format!(
                r#"Token request to {ORIGIN_TOKEN} failed: 400: {{"error":"invalid_grant"}}"#
            ))]
        );
        let bodies = http.bodies(ORIGIN_TOKEN);
        assert_eq!(bodies.len(), 2);
        assert_eq!(bodies[0], bodies[1], "the retry posts the same grant");
    }

    /// The browser callback wins over a pending paste: the paste field is
    /// dropped and the redirect's code is exchanged.
    #[tokio::test]
    async fn the_browser_callback_wins_and_drops_the_paste() {
        let http = std::sync::Arc::new(origin_http(vec![(
            200,
            r#"{"access_token":"origin-access"}"#,
        )]));
        let ui = std::sync::Arc::new(TestUi {
            pending: true,
            ..TestUi::from_auth_url()
        });
        let flow = {
            let (http, ui) = (std::sync::Arc::clone(&http), std::sync::Arc::clone(&ui));
            tokio::spawn(async move {
                mcp_login(http.as_ref(), &config("origin", ORIGIN_URL), &ui).await
            })
        };
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        let (redirect, state) = loop {
            if let (Some(redirect), Some(state)) =
                (ui.auth_param("redirect_uri"), ui.auth_param("state"))
            {
                break (redirect, state);
            }
            assert!(
                std::time::Instant::now() < deadline,
                "the flow never presented its url"
            );
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        };
        let port = Url::parse(&redirect).unwrap().port().unwrap();
        let status = reqwest::Client::new()
            .get(format!(
                "http://127.0.0.1:{port}/callback?code=live-code&state={state}"
            ))
            .send()
            .await
            .unwrap()
            .status();
        assert_eq!(status.as_u16(), 200);
        tokio::time::timeout(std::time::Duration::from_secs(10), flow)
            .await
            .expect("the flow settles once the redirect lands")
            .unwrap()
            .unwrap();
        let bodies = http.bodies(ORIGIN_TOKEN);
        assert_eq!(bodies.len(), 1);
        assert_eq!(
            token_param(&bodies[0], "code").as_deref(),
            Some("live-code")
        );
        assert_eq!(
            ui.dropped_fields.load(std::sync::atomic::Ordering::SeqCst),
            1
        );
    }

    /// A pre-registered client id skips dynamic registration.
    #[tokio::test]
    async fn pre_registered_client_skips_registration() {
        let http = ScriptedHttp::new(vec![
            (ORIGIN_URL, 404, None, ""),
            (
                "https://srv.test/.well-known/oauth-protected-resource/mcp",
                404,
                None,
                "",
            ),
            (ORIGIN_META_URL, 200, None, &json_response(&origin_meta())),
            (
                ORIGIN_TOKEN,
                200,
                None,
                &json_response(&serde_json::json!({ "access_token": "root-access" })),
            ),
        ]);
        let ui = test_ui();
        let mut login_config = config("root", ORIGIN_URL);
        login_config.client_id = Some("root-client".to_string());
        let credentials = mcp_login(&http, &login_config, &ui).await.unwrap();
        match &credentials {
            AuthCredential::Oauth {
                access, client_id, ..
            } => {
                assert_eq!(access, "root-access");
                assert_eq!(client_id.as_deref(), Some("root-client"));
            }
            other => panic!("oauth credential expected, got {other:?}"),
        }
        let urls: Vec<String> = http
            .seen
            .lock()
            .unwrap()
            .iter()
            .map(|(url, _)| url.clone())
            .collect();
        assert!(!urls.contains(&ORIGIN_REGISTER.to_string()));
    }
}
