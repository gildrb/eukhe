//! The composition root's subscription logins (TS `auth-flows.ts`'s
//! `showLoginDialog` over the AI library's `openaiCodex`, `anthropic`,
//! `githubCopilot`, and `xai` OAuth providers): each provider's pi-ai flow
//! ([`OAuthAuth::login`]) runs against the inline auth panel — the browser
//! URL block, the prompts, the progress lines, the manual paste racing the
//! localhost callback — and the credential lands under the provider's id
//! in the TS `auth.json` wire shape. Nothing touches the plain terminal.
//!
//! The panel keeps the paste loop's behavior: a paste that carries no
//! code, reports a sign-in error, or echoes another login's state is
//! rejected with a notice and the paste field re-mounts (the flow never
//! sees it); a login that fails after its code reached the flow (the
//! token exchange) shows the retry notice and starts the login again.
//! The panel has no picker, so a method selection takes the flow's first
//! (default) option: the browser login.
//!
//! Cancellation (#2770): the panel handle's shared flag is the seam -- the
//! driving pane marks it on exit, the login's abort signal follows it, and
//! the flag is checked again before the credential write, so an exited
//! pane never lands a credential (a task abort cannot reach the started
//! blocking body). An Esc on a prompt ends the login silently.

use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_ai::auth::{
    AuthEvent, AuthInteraction, AuthPrompt, AuthPromptKind, OAuthAuth, ProviderAuthInteraction,
};
use eukhe_ai::utils::diagnostics::Thrown;
use eukhe_chord::context::{AbortController, AbortSignal};
use eukhe_core::auth::{
    exchange_retry_notice, parse_redirect_input, stored_oauth_credential, AuthStorage,
    RedirectInputError, VerifiedAuthorization, GITHUB_COPILOT_PROVIDER_ID,
};
use eukhe_tui::auth_panel::{AuthPanelHandle, PastePromptTone, PasteStyle};
use eukhe_tui::provider_auth::ProviderAuthOutcome;
use futures::future::BoxFuture;

/// TS the login dialog's manual-input prompt (the callback-server
/// providers' paste line).
const MANUAL_INPUT_PROMPT: &str = "Paste redirect URL below, or complete login in browser:";
/// TS `showWaiting` for the Copilot device flow (the composition root's
/// onAuth handling for `github-copilot`).
const COPILOT_WAITING: &str = "Waiting for browser authentication...";
/// The error a cancelled prompt answers the flow with.
const LOGIN_CANCELLED: &str = "Login cancelled";
/// How often the login re-checks the pane's cancel flag.
const CANCEL_POLL_INTERVAL: Duration = Duration::from_millis(250);

/// Opens a URL in the user's browser.
pub(crate) type BrowserOpener = fn(&str);

/// The surface one login drives: the inline auth panel and the browser.
#[derive(Clone)]
pub(crate) struct LoginSurface {
    panel: AuthPanelHandle,
    open_browser: BrowserOpener,
}

impl LoginSurface {
    /// The panel, with the system browser.
    pub(crate) fn new(panel: AuthPanelHandle) -> Self {
        LoginSurface {
            panel,
            open_browser: eukhe_core::platform::browser::open_in_browser,
        }
    }
}

/// The inline auth panel as one pi-ai login attempt's interaction.
struct PanelAuthInteraction {
    surface: LoginSurface,
    provider_id: String,
    signal: AbortSignal,
    /// A retried attempt keeps the browser tab the first one opened.
    open_browser: bool,
    /// The attempt's `state` (its authorization URL's): a paste echoing
    /// another login's state is rejected before the flow sees it.
    expected_state: Mutex<Option<String>>,
    /// The user cancelled a prompt (Esc).
    cancelled: AtomicBool,
    /// A code reached the flow (a paste answered the manual prompt, or
    /// the browser callback ended the race): a later failure is the
    /// token exchange's.
    code_delivered: AtomicBool,
}

impl PanelAuthInteraction {
    fn new(surface: LoginSurface, provider_id: &str, signal: AbortSignal, first: bool) -> Self {
        PanelAuthInteraction {
            surface,
            provider_id: provider_id.to_string(),
            signal,
            open_browser: first,
            expected_state: Mutex::new(None),
            cancelled: AtomicBool::new(false),
            code_delivered: AtomicBool::new(false),
        }
    }

    fn cancel(&self) -> Thrown {
        self.cancelled.store(true, Ordering::Relaxed);
        login_error(LOGIN_CANCELLED)
    }

    fn show_url(&self, url: &str, instructions: Option<&str>) {
        self.surface.panel.auth_url(url, instructions);
        if self.open_browser {
            (self.surface.open_browser)(url);
        }
    }

    /// One text prompt (the placeholder renders as an example).
    async fn text_prompt(
        &self,
        message: &str,
        placeholder: Option<&str>,
        style: PasteStyle,
        allow_empty: bool,
    ) -> Result<String, Thrown> {
        let message = match placeholder {
            // TS `showPrompt` renders the placeholder as an example.
            Some(placeholder) => format!("{message} (e.g. {placeholder})"),
            None => message.to_string(),
        };
        let panel = &self.surface.panel;
        let answer = if allow_empty {
            panel
                .paste_prompt_allow_empty(&message, PastePromptTone::Text, style)
                .await
        } else {
            panel
                .paste_prompt(&message, PastePromptTone::Text, style)
                .await
        };
        answer.ok_or_else(|| self.cancel())
    }

    /// The manual paste racing the browser callback: rejected pastes
    /// notice and re-mount the field; the accepted one reaches the flow
    /// as a `code=..&state=..` query.
    async fn manual_code(&self, prompt_signal: Option<AbortSignal>) -> Result<String, Thrown> {
        loop {
            let paste = self.surface.panel.paste_prompt(
                MANUAL_INPUT_PROMPT,
                PastePromptTone::Muted,
                PasteStyle::Visible,
            );
            let input = match &prompt_signal {
                Some(signal) => tokio::select! {
                    reason = signal.cancelled() => {
                        // The callback ended the race (its code goes to
                        // the exchange) unless the whole login aborted.
                        if !self.signal.aborted() {
                            self.code_delivered.store(true, Ordering::Relaxed);
                        }
                        return Err(reason);
                    }
                    input = paste => input,
                },
                None => paste.await,
            };
            let Some(input) = input else {
                return Err(self.cancel());
            };
            let expected = self
                .expected_state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .clone();
            match verified_paste(&input, expected.as_deref()) {
                Ok(accepted) => {
                    self.code_delivered.store(true, Ordering::Relaxed);
                    return Ok(url::form_urlencoded::Serializer::new(String::new())
                        .append_pair("code", &accepted.code)
                        .append_pair("state", &accepted.state)
                        .finish());
                }
                // The warning row under the re-mounted paste field.
                Err(rejected) => self.surface.panel.notice(rejected.to_string()),
            }
        }
    }
}

/// A paste's code, checked against the login's state when one is known.
fn verified_paste(
    input: &str,
    expected_state: Option<&str>,
) -> Result<VerifiedAuthorization, RedirectInputError> {
    let pasted = parse_redirect_input(input)?;
    match expected_state {
        Some(state) => pasted.verify_state(state),
        None => Ok(VerifiedAuthorization {
            state: pasted.state.unwrap_or_default(),
            code: pasted.code,
        }),
    }
}

impl AuthInteraction for PanelAuthInteraction {
    fn signal(&self) -> Option<AbortSignal> {
        Some(self.signal.clone())
    }

    fn prompt(&self, prompt: AuthPrompt) -> BoxFuture<'_, Result<String, Thrown>> {
        Box::pin(async move {
            match prompt.kind {
                // The panel has no picker: the flows list their default
                // (the browser login) first.
                AuthPromptKind::Select { message, options } => options
                    .into_iter()
                    .next()
                    .map(|option| option.id)
                    .ok_or_else(|| login_error(format!("{message} offers no option"))),
                // A blank answer is the flow's to judge (the Copilot
                // domain prompt's "blank for github.com").
                AuthPromptKind::Text {
                    message,
                    placeholder,
                } => {
                    self.text_prompt(&message, placeholder.as_deref(), PasteStyle::Visible, true)
                        .await
                }
                AuthPromptKind::Secret {
                    message,
                    placeholder,
                } => {
                    self.text_prompt(&message, placeholder.as_deref(), PasteStyle::Masked, false)
                        .await
                }
                AuthPromptKind::ManualCode { .. } => self.manual_code(prompt.signal).await,
            }
        })
    }

    fn notify(&self, event: AuthEvent) {
        match event {
            AuthEvent::AuthUrl { url, instructions } => {
                *self
                    .expected_state
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner) = authorization_state(&url);
                self.show_url(&url, instructions.as_deref());
            }
            AuthEvent::DeviceCode {
                user_code,
                verification_uri,
                ..
            } => {
                self.show_url(&verification_uri, Some(&format!("Enter code: {user_code}")));
                if self.provider_id == GITHUB_COPILOT_PROVIDER_ID {
                    // TS `showWaiting` (the dialog's own method, no
                    // onboarding guard).
                    self.surface.panel.waiting(COPILOT_WAITING);
                }
            }
            // TS `showLoginDialog`'s `onProgress` arm is unguarded chatter:
            // a direct `dialog.showProgress` line on every surface.
            AuthEvent::Progress { message } => self.surface.panel.progress_line(message),
            // Guidance and a failed exchange's retry reason stay readable
            // under the re-mounted paste field.
            AuthEvent::Info { message, .. } => self.surface.panel.notice(message),
        }
    }
}

/// The `state` parameter of an authorization URL.
fn authorization_state(url: &str) -> Option<String> {
    url::Url::parse(url).ok().and_then(|url| {
        url.query_pairs()
            .find(|(key, _)| key == "state")
            .map(|(_, value)| value.into_owned())
    })
}

fn login_error(message: impl Into<String>) -> Thrown {
    Arc::new(std::io::Error::other(message.into()))
}

/// Aborts the login when the pane exits, until dropped.
struct CancelWatch(tokio::task::JoinHandle<()>);

impl CancelWatch {
    fn start(panel: AuthPanelHandle, controller: AbortController) -> Self {
        CancelWatch(tokio::spawn(async move {
            while !panel.cancelled() {
                tokio::time::sleep(CANCEL_POLL_INTERVAL).await;
            }
            controller.abort(Some(login_error(LOGIN_CANCELLED)));
        }))
    }
}

impl Drop for CancelWatch {
    fn drop(&mut self) {
        self.0.abort();
    }
}

/// TS `showLoginDialog` + `completeProviderAuthentication`: run the
/// provider's flow on the panel, store the credential, and report the TS
/// status. A cancelled surface stays silent; a failed flow reports the TS
/// error row.
pub(crate) async fn run_subscription_login(
    agent_dir: &Path,
    provider_id: &str,
    provider_name: &str,
    flow: &dyn OAuthAuth,
    surface: &LoginSurface,
) -> ProviderAuthOutcome {
    let controller = AbortController::new();
    let _watch = CancelWatch::start(surface.panel.clone(), controller.clone());
    let mut first = true;
    let credential = loop {
        let interaction = Arc::new(PanelAuthInteraction::new(
            surface.clone(),
            provider_id,
            controller.signal(),
            first,
        ));
        first = false;
        let login = flow
            .login(
                ProviderAuthInteraction::new(
                    Arc::clone(&interaction) as Arc<dyn AuthInteraction>,
                    controller.signal(),
                ),
                None,
            )
            .await;
        match login {
            Ok(credential) => break credential,
            Err(_)
                if interaction.cancelled.load(Ordering::Relaxed)
                    || surface.panel.cancelled()
                    || controller.signal().aborted() =>
            {
                return ProviderAuthOutcome::Cancelled;
            }
            // The code reached the flow and the exchange failed: the same
            // panel retries with a fresh login.
            Err(error) if interaction.code_delivered.load(Ordering::Relaxed) => {
                surface
                    .panel
                    .notice(exchange_retry_notice(&error.to_string()));
            }
            Err(error) => {
                return ProviderAuthOutcome::Error(format!(
                    "Failed to login to {provider_name}: {error}"
                ));
            }
        }
    };
    // The pane exited while the login ran: no credential write lands.
    if surface.panel.cancelled() {
        return ProviderAuthOutcome::Cancelled;
    }
    let mut auth = AuthStorage::create(agent_dir);
    if let Err(error) = auth.set(provider_id, stored_oauth_credential(&credential)) {
        return ProviderAuthOutcome::Error(format!(
            "Failed to login to {provider_name}: could not save the login: {error}"
        ));
    }
    ProviderAuthOutcome::Status(format!(
        "Logged in to {provider_name}. Credentials saved to {}",
        agent_dir.join("auth.json").display()
    ))
}

#[cfg(test)]
#[path = "subscription_login_tests.rs"]
mod tests;
