//! The subscription logins on the inline auth panel: scripted pi-ai flows
//! drive a real [`AuthPanelHandle`] whose requests a scripted pane
//! answers.

use std::cell::Cell;
use std::collections::VecDeque;
use std::sync::atomic::AtomicUsize;

use eukhe_core::auth::{
    AuthCredential, ANTHROPIC_PROVIDER_ID, OPENAI_CODEX_PROVIDER_ID, XAI_PROVIDER_ID,
};
use eukhe_pi_ai::auth::{AuthSelectOption, LoginOptions, ModelAuth, OAuthCredential};
use eukhe_tui::auth_panel::AuthPanelRequest;

use super::*;

thread_local! {
    /// Browser launches on this test's runtime thread.
    static BROWSER_OPENS: Cell<usize> = const { Cell::new(0) };
}

fn count_browser_open(_url: &str) {
    BROWSER_OPENS.with(|opens| opens.set(opens.get() + 1));
}

/// One request the scripted pane saw.
#[derive(Debug, Clone, PartialEq)]
enum Seen {
    AuthUrl(String, Option<String>),
    Notice(String),
    Waiting(String),
    Progress(String),
    Prompt {
        prompt: String,
        tone: PastePromptTone,
        style: PasteStyle,
        allow_empty: bool,
    },
}

/// A scripted pane: answers each paste prompt from the queue (an empty
/// queue answers Esc) and records every request.
struct ScriptedPane {
    surface: LoginSurface,
    seen: Arc<Mutex<Vec<Seen>>>,
    driver: tokio::task::JoinHandle<()>,
}

impl ScriptedPane {
    fn start(answers: Vec<Option<&str>>) -> Self {
        let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel();
        let seen: Arc<Mutex<Vec<Seen>>> = Arc::default();
        let record = Arc::clone(&seen);
        let mut answers: VecDeque<Option<String>> = answers
            .into_iter()
            .map(|answer| answer.map(str::to_string))
            .collect();
        let driver = tokio::spawn(async move {
            while let Some(request) = rx.recv().await {
                let mut seen = record.lock().unwrap();
                match request {
                    AuthPanelRequest::AuthUrl { url, instructions } => {
                        seen.push(Seen::AuthUrl(url, instructions));
                    }
                    AuthPanelRequest::Notice { message } => seen.push(Seen::Notice(message)),
                    AuthPanelRequest::Waiting { message } => seen.push(Seen::Waiting(message)),
                    AuthPanelRequest::Progress { message, .. } => {
                        seen.push(Seen::Progress(message));
                    }
                    AuthPanelRequest::PastePrompt {
                        prompt,
                        tone,
                        style,
                        allow_empty,
                        reply,
                    } => {
                        seen.push(Seen::Prompt {
                            prompt,
                            tone,
                            style,
                            allow_empty,
                        });
                        let _ = reply.send(answers.pop_front().flatten());
                    }
                    AuthPanelRequest::SelectTeam { .. }
                    | AuthPanelRequest::ProviderSettled { .. }
                    | AuthPanelRequest::McpSettled { .. } => {
                        panic!("the subscription logins never send this request");
                    }
                }
            }
        });
        ScriptedPane {
            surface: LoginSurface {
                panel: AuthPanelHandle::new(tx),
                open_browser: count_browser_open,
            },
            seen,
            driver,
        }
    }

    /// Every request the login sent: the pane closes and drains its queue
    /// (the fire-and-forget rows land after the login returns).
    async fn finish(self) -> Vec<Seen> {
        let ScriptedPane {
            surface,
            seen,
            driver,
        } = self;
        drop(surface);
        driver.await.expect("the scripted pane runs");
        let seen = seen.lock().unwrap().clone();
        seen
    }
}

fn notices(seen: &[Seen]) -> Vec<String> {
    seen.iter()
        .filter_map(|seen| match seen {
            Seen::Notice(message) => Some(message.clone()),
            _ => None,
        })
        .collect()
}

type Attempt = Arc<
    dyn Fn(ProviderAuthInteraction, usize) -> BoxFuture<'static, Result<OAuthCredential, Thrown>>
        + Send
        + Sync,
>;

/// A scripted pi-ai flow: each login attempt runs the script with its
/// attempt number.
struct ScriptedFlow {
    attempt: Attempt,
    attempts: AtomicUsize,
}

impl ScriptedFlow {
    fn new(attempt: Attempt) -> Self {
        ScriptedFlow {
            attempt,
            attempts: AtomicUsize::new(0),
        }
    }
}

impl OAuthAuth for ScriptedFlow {
    fn name(&self) -> &'static str {
        "scripted"
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        _options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        let attempt = self.attempts.fetch_add(1, Ordering::SeqCst);
        (self.attempt)(interaction, attempt)
    }

    fn refresh(
        &self,
        _credential: OAuthCredential,
        _signal: AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async {
            Ok(OAuthCredential::new(
                "r-2",
                "refreshed-access",
                4_000_000_000_000.0,
            ))
        })
    }

    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        Box::pin(async move {
            Ok(ModelAuth {
                api_key: Some(credential.access.clone()),
                headers: None,
                base_url: None,
            })
        })
    }
}

/// The browser login of the callback flows: the method select, the
/// authorization URL (state `st`), the manual paste, then the exchange
/// (`exchange` answers per attempt).
fn browser_flow(
    inputs: Arc<Mutex<Vec<String>>>,
    exchange: impl Fn(usize) -> Result<OAuthCredential, String> + Send + Sync + 'static,
) -> Attempt {
    let exchange = Arc::new(exchange);
    Arc::new(move |interaction, attempt| {
        let inputs = Arc::clone(&inputs);
        let exchange = Arc::clone(&exchange);
        Box::pin(async move {
            let method = interaction
                .prompt(AuthPrompt::new(AuthPromptKind::Select {
                    message: "Select login method:".to_string(),
                    options: vec![
                        AuthSelectOption::new("browser", "Browser login (default)"),
                        AuthSelectOption::new("device_code", "Device code login"),
                    ],
                }))
                .await?;
            assert_eq!(method, "browser", "the panel takes the default method");
            interaction.notify(AuthEvent::AuthUrl {
                url: "https://auth.example/authorize?client_id=c&state=st".to_string(),
                instructions: Some("Complete login in your browser.".to_string()),
            });
            let input = interaction
                .prompt(AuthPrompt::new(AuthPromptKind::ManualCode {
                    message: "Paste the code".to_string(),
                    placeholder: None,
                }))
                .await?;
            inputs.lock().unwrap().push(input);
            exchange(attempt).map_err(login_error)
        })
    })
}

fn codex_credential() -> OAuthCredential {
    OAuthCredential::new("r-1", "codex-access", 1_800_000_000_000.0)
        .with_extra("accountId", serde_json::Value::String("acct-1".to_string()))
}

fn agent_dir(dir: &tempfile::TempDir) -> std::path::PathBuf {
    let agent = dir.path().join("agent");
    std::fs::create_dir_all(&agent).expect("agent dir");
    agent
}

fn stored(agent: &Path, provider_id: &str) -> serde_json::Value {
    let document: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(agent.join("auth.json")).unwrap()).unwrap();
    document[provider_id].clone()
}

#[tokio::test]
async fn the_browser_login_stores_the_credential_and_reports_the_ts_status() {
    let dir = tempfile::tempdir().expect("temp dir");
    let agent = agent_dir(&dir);
    let inputs: Arc<Mutex<Vec<String>>> = Arc::default();
    let flow = ScriptedFlow::new(browser_flow(
        Arc::clone(&inputs),
        |_| Ok(codex_credential()),
    ));
    let pane = ScriptedPane::start(vec![Some(
        "  \"http://localhost:1455/auth/callback?code=abc&state=st\"\n",
    )]);
    let outcome = run_subscription_login(
        &agent,
        OPENAI_CODEX_PROVIDER_ID,
        "ChatGPT Plus/Pro (Codex Subscription)",
        &flow,
        &pane.surface,
    )
    .await;
    assert_eq!(
        outcome,
        ProviderAuthOutcome::Status(format!(
            "Logged in to ChatGPT Plus/Pro (Codex Subscription). Credentials saved to {}",
            agent.join("auth.json").display()
        ))
    );
    // The cleaned paste reaches the flow as its code and state.
    assert_eq!(
        *inputs.lock().unwrap(),
        vec!["code=abc&state=st".to_string()]
    );
    let seen = pane.finish().await;
    assert_eq!(
        seen[0],
        Seen::AuthUrl(
            "https://auth.example/authorize?client_id=c&state=st".to_string(),
            Some("Complete login in your browser.".to_string())
        )
    );
    assert_eq!(
        seen[1],
        Seen::Prompt {
            prompt: MANUAL_INPUT_PROMPT.to_string(),
            tone: PastePromptTone::Muted,
            style: PasteStyle::Visible,
            allow_empty: false,
        }
    );
    assert_eq!(BROWSER_OPENS.with(Cell::get), 1);
    // The packaged auth.json wire shape: the TS credential with its
    // `accountId`.
    let stored = stored(&agent, OPENAI_CODEX_PROVIDER_ID);
    assert_eq!(stored["type"], "oauth");
    assert_eq!(stored["access"], "codex-access");
    assert_eq!(stored["refresh"], "r-1");
    assert_eq!(stored["expires"], 1_800_000_000_000_i64);
    assert_eq!(stored["accountId"], "acct-1");
    assert!(stored.get("enterpriseUrl").is_none());
    let mut auth = AuthStorage::create(&agent);
    assert_eq!(
        auth.get_api_key(OPENAI_CODEX_PROVIDER_ID),
        Some("codex-access".to_string())
    );
}

/// A paste from another login attempt (or without a code) is a notice on
/// the same panel: the field re-mounts and the flow never sees it.
#[tokio::test]
async fn a_rejected_paste_notices_and_re_prompts() {
    let dir = tempfile::tempdir().expect("temp dir");
    let agent = agent_dir(&dir);
    let inputs: Arc<Mutex<Vec<String>>> = Arc::default();
    let flow = ScriptedFlow::new(browser_flow(
        Arc::clone(&inputs),
        |_| Ok(codex_credential()),
    ));
    let pane = ScriptedPane::start(vec![
        Some("http://localhost:1455/auth/callback?code=abc&state=other"),
        Some("http://localhost:1455/auth/callback"),
        Some("abc"),
    ]);
    let outcome = run_subscription_login(
        &agent,
        ANTHROPIC_PROVIDER_ID,
        "Anthropic (Claude Pro/Max)",
        &flow,
        &pane.surface,
    )
    .await;
    assert!(
        matches!(outcome, ProviderAuthOutcome::Status(_)),
        "{outcome:?}"
    );
    assert_eq!(
        notices(&pane.finish().await),
        vec![
            RedirectInputError::StateMismatch.to_string(),
            RedirectInputError::MissingCode.to_string(),
        ]
    );
    // A bare code takes the login's own state.
    assert_eq!(
        *inputs.lock().unwrap(),
        vec!["code=abc&state=st".to_string()]
    );
}

/// A failed exchange is a notice on the same panel, not an error row: the
/// login starts again (the browser tab stays), and the cancelled re-prompt
/// ends it silently without a credential.
#[tokio::test]
async fn a_failed_exchange_notices_and_retries() {
    let dir = tempfile::tempdir().expect("temp dir");
    let agent = agent_dir(&dir);
    let inputs: Arc<Mutex<Vec<String>>> = Arc::default();
    let flow = ScriptedFlow::new(browser_flow(Arc::clone(&inputs), |_| {
        Err("Token exchange failed (400): invalid_grant".to_string())
    }));
    let pane = ScriptedPane::start(vec![Some("abc#st")]);
    assert_eq!(
        run_subscription_login(
            &agent,
            ANTHROPIC_PROVIDER_ID,
            "Anthropic (Claude Pro/Max)",
            &flow,
            &pane.surface,
        )
        .await,
        ProviderAuthOutcome::Cancelled
    );
    assert_eq!(
        notices(&pane.finish().await),
        vec![exchange_retry_notice(
            "Token exchange failed (400): invalid_grant"
        )]
    );
    assert_eq!(flow.attempts.load(Ordering::SeqCst), 2);
    assert_eq!(BROWSER_OPENS.with(Cell::get), 1, "the retry keeps the tab");
    assert!(!agent.join("auth.json").exists());
}

/// The device flows: the Copilot domain prompt accepts a blank answer,
/// the verification URL renders with its code, Copilot adds its waiting
/// line, and the enterprise domain rides the credential.
#[tokio::test]
async fn the_device_login_renders_the_code_and_stores_the_enterprise_domain() {
    let dir = tempfile::tempdir().expect("temp dir");
    let agent = agent_dir(&dir);
    let flow = ScriptedFlow::new(Arc::new(|interaction, _| {
        Box::pin(async move {
            let domain = interaction
                .prompt(AuthPrompt::new(AuthPromptKind::Text {
                    message: "GitHub Enterprise URL/domain (blank for github.com)".to_string(),
                    placeholder: Some("company.ghe.com".to_string()),
                }))
                .await?;
            assert_eq!(domain, "");
            interaction.notify(AuthEvent::DeviceCode {
                user_code: "ABCD-1234".to_string(),
                verification_uri: "https://github.com/login/device".to_string(),
                interval_seconds: None,
                expires_in_seconds: None,
            });
            interaction.notify(AuthEvent::Progress {
                message: "Enabling models...".to_string(),
            });
            Ok(
                OAuthCredential::new("gh-token", "copilot-token", 1_800_000_000_000.0).with_extra(
                    "enterpriseUrl",
                    serde_json::Value::String("company.ghe.com".to_string()),
                ),
            )
        })
    }));
    let pane = ScriptedPane::start(vec![Some("")]);
    let outcome = run_subscription_login(
        &agent,
        GITHUB_COPILOT_PROVIDER_ID,
        "GitHub Copilot",
        &flow,
        &pane.surface,
    )
    .await;
    assert!(
        matches!(outcome, ProviderAuthOutcome::Status(_)),
        "{outcome:?}"
    );
    assert_eq!(
        pane.finish().await,
        vec![
            Seen::Prompt {
                prompt:
                    "GitHub Enterprise URL/domain (blank for github.com) (e.g. company.ghe.com)"
                        .to_string(),
                tone: PastePromptTone::Text,
                style: PasteStyle::Visible,
                allow_empty: true,
            },
            Seen::AuthUrl(
                "https://github.com/login/device".to_string(),
                Some("Enter code: ABCD-1234".to_string())
            ),
            Seen::Waiting(COPILOT_WAITING.to_string()),
            Seen::Progress("Enabling models...".to_string()),
        ]
    );
    let stored = stored(&agent, GITHUB_COPILOT_PROVIDER_ID);
    assert_eq!(stored["access"], "copilot-token");
    assert_eq!(stored["refresh"], "gh-token");
    assert_eq!(stored["enterpriseUrl"], "company.ghe.com");
}

/// A cancelled pane never receives the credential (#2770: no write after
/// the exit) -- the regression test for the abort-cleanup contract.
#[tokio::test]
async fn a_cancelled_pane_writes_no_credential() {
    let dir = tempfile::tempdir().expect("temp dir");
    let agent = agent_dir(&dir);
    let flow = ScriptedFlow::new(Arc::new(|_, _| {
        Box::pin(async { Ok(OAuthCredential::new("r", "a", 1_800_000_000_000.0)) })
    }));
    let pane = ScriptedPane::start(Vec::new());
    // The pane exits right before the flow returns.
    pane.surface
        .panel
        .cancel_flag()
        .store(true, Ordering::Relaxed);
    assert_eq!(
        run_subscription_login(&agent, XAI_PROVIDER_ID, "xAI (Grok)", &flow, &pane.surface).await,
        ProviderAuthOutcome::Cancelled
    );
    assert!(
        !agent.join("auth.json").exists(),
        "a cancelled pane lands no credential"
    );
}

/// The pane's exit aborts a login that is still waiting (a device poll).
#[tokio::test]
async fn an_exited_pane_aborts_the_running_login() {
    let dir = tempfile::tempdir().expect("temp dir");
    let agent = agent_dir(&dir);
    let flow = ScriptedFlow::new(Arc::new(|interaction, _| {
        Box::pin(async move { Err(interaction.signal.cancelled().await) })
    }));
    let pane = ScriptedPane::start(Vec::new());
    let flag = pane.surface.panel.cancel_flag();
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_millis(20)).await;
        flag.store(true, Ordering::Relaxed);
    });
    assert_eq!(
        run_subscription_login(&agent, XAI_PROVIDER_ID, "xAI (Grok)", &flow, &pane.surface).await,
        ProviderAuthOutcome::Cancelled
    );
}

#[tokio::test]
async fn a_failed_flow_reports_the_ts_error_row() {
    let dir = tempfile::tempdir().expect("temp dir");
    let agent = agent_dir(&dir);
    let flow = ScriptedFlow::new(Arc::new(|_, _| {
        Box::pin(async { Err(login_error("xAI OAuth request failed: offline")) })
    }));
    let pane = ScriptedPane::start(Vec::new());
    assert_eq!(
        run_subscription_login(&agent, XAI_PROVIDER_ID, "xAI (Grok)", &flow, &pane.surface).await,
        ProviderAuthOutcome::Error(
            "Failed to login to xAI (Grok): xAI OAuth request failed: offline".to_string()
        )
    );
    assert!(!agent.join("auth.json").exists());
}

/// The credential round-trip: the stored credential reloads, resolves
/// while unexpired, and refreshes at expiry through the provider
/// integration (the same `AuthStorage` every surface uses).
#[tokio::test]
async fn the_stored_credential_round_trips_and_refreshes() {
    let dir = tempfile::tempdir().expect("temp dir");
    let agent = agent_dir(&dir);
    let flow = Arc::new(ScriptedFlow::new(Arc::new(|_, _| {
        Box::pin(async {
            Ok(OAuthCredential::new(
                "grok-refresh",
                "grok-access",
                4_000_000_000_000.0,
            ))
        })
    })));
    let pane = ScriptedPane::start(Vec::new());
    run_subscription_login(
        &agent,
        XAI_PROVIDER_ID,
        "xAI (Grok)",
        flow.as_ref(),
        &pane.surface,
    )
    .await;
    let mut auth = AuthStorage::create(&agent);
    assert_eq!(
        auth.get_api_key(XAI_PROVIDER_ID),
        Some("grok-access".to_string())
    );
    // An expired credential refreshes through the integration's flow and
    // the fresh token resolves.
    let mut data = auth.get_all();
    if let Some(document) = data.0.get_mut(XAI_PROVIDER_ID) {
        document["expires"] = serde_json::json!(1);
    }
    let mut expired = AuthStorage::in_memory_without_env(
        &data,
        Arc::new(eukhe_core::auth::ProviderOAuth::with_flows([(
            XAI_PROVIDER_ID.to_string(),
            flow as Arc<dyn OAuthAuth>,
        )])),
    );
    assert_eq!(
        expired.get_api_key(XAI_PROVIDER_ID),
        Some("refreshed-access".to_string())
    );
    assert!(matches!(
        expired.get_all().credential(XAI_PROVIDER_ID),
        Some(AuthCredential::Oauth { refresh: Some(refresh), .. }) if refresh == "r-2"
    ));
}
