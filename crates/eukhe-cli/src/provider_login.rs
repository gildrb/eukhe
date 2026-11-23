//! The composition root's provider auth flows behind the TUI's `/login`
//! and `/logout` (TS `ProviderAuthFlows`): the provider catalog rows with
//! their auth status, the API-key store, the MCP device flow, and the
//! four subscription logins (`subscription_login`: the Codex
//! Subscription, Anthropic, GitHub Copilot, and xAI pi-ai OAuth flows on
//! the inline auth panel, and the credential writes).

use std::path::{Path, PathBuf};

use eukhe_core::auth::{AuthCredential, AuthSource, AuthStatus};
use eukhe_core::models::ModelRegistry;
use eukhe_tui::provider_auth::{
    AuthFlow, AuthStatusIndicator, AuthStatusStyle, AuthType, ProviderAccountsFuture,
    ProviderAuthCommands, ProviderAuthFuture, ProviderAuthOutcome, ProviderRow, ProviderRowsFuture,
    ProviderWarningFuture,
};
use serde_json::Value;

/// The TS OAuth provider rows (`the TS AI library/oauth` registry): the
/// subscription logins, every flow ported.
const SUBSCRIPTION_PROVIDERS: [(&str, &str); 4] = [
    ("anthropic", "Anthropic (Claude Pro/Max)"),
    ("github-copilot", "GitHub Copilot"),
    ("openai-codex", "ChatGPT Plus/Pro (Codex Subscription)"),
    ("xai", "xAI (Grok)"),
];

/// TS `BUILT_IN_PROVIDER_DISPLAY_NAMES` (provider id -> display name):
/// a known display name marks an API-key login provider.
const BUILT_IN_PROVIDER_DISPLAY_NAMES: &[(&str, &str)] = &[
    ("anthropic", "Anthropic"),
    ("amazon-bedrock", "Amazon Bedrock"),
    ("azure-openai-responses", "Azure OpenAI Responses"),
    ("cerebras", "Cerebras"),
    ("cloudflare-ai-gateway", "Cloudflare AI Gateway"),
    ("cloudflare-workers-ai", "Cloudflare Workers AI"),
    ("deepseek", "DeepSeek"),
    ("fireworks", "Fireworks"),
    ("google", "Google Gemini"),
    ("google-vertex", "Google Vertex AI"),
    ("groq", "Groq"),
    ("huggingface", "Hugging Face"),
    ("kimi-coding", "Kimi For Coding"),
    ("mistral", "Mistral"),
    ("minimax", "MiniMax"),
    ("minimax-cn", "MiniMax (China)"),
    ("moonshotai", "Moonshot AI"),
    ("moonshotai-cn", "Moonshot AI (China)"),
    ("opencode", "OpenCode Zen"),
    ("opencode-go", "OpenCode Go"),
    ("openai", "OpenAI"),
    ("openrouter", "OpenRouter"),
    ("vercel-ai-gateway", "Vercel AI Gateway"),
    ("xai", "xAI (Grok)"),
    ("zai", "ZAI"),
    ("xiaomi", "Xiaomi MiMo"),
    ("xiaomi-token-plan-cn", "Xiaomi MiMo Token Plan (China)"),
    (
        "xiaomi-token-plan-ams",
        "Xiaomi MiMo Token Plan (Amsterdam)",
    ),
    (
        "xiaomi-token-plan-sgp",
        "Xiaomi MiMo Token Plan (Singapore)",
    ),
];

/// The display name of a provider id (the TS map, else the id itself).
fn display_name(provider_id: &str) -> String {
    BUILT_IN_PROVIDER_DISPLAY_NAMES
        .iter()
        .find(|(id, _)| *id == provider_id)
        .map_or_else(|| provider_id.to_string(), |(_, name)| name.to_string())
}

/// TS `isApiKeyLoginProvider`: the display-name map, or a provider the
/// built-in model provider set does not know (custom models.json entries).
fn is_api_key_login_provider(
    provider_id: &str,
    built_in_provider_ids: &std::collections::HashSet<String>,
) -> bool {
    if BUILT_IN_PROVIDER_DISPLAY_NAMES
        .iter()
        .any(|(id, _)| *id == provider_id)
    {
        return true;
    }
    !built_in_provider_ids.contains(provider_id)
}

/// The provider's status indicator (TS `formatStatusIndicator` +
/// `formatApiKeyStatusIndicator`): the stored credential's match, the env
/// key, or the unconfigured hidden meta.
fn status_indicator(
    credential: Option<&AuthCredential>,
    status: &AuthStatus,
    auth_type: AuthType,
) -> Option<AuthStatusIndicator> {
    // A stale credential shows its warning label.
    if status.source == Some(AuthSource::Stale) {
        return Some(AuthStatusIndicator {
            style: AuthStatusStyle::Warning,
            label: status
                .label
                .clone()
                .unwrap_or_else(|| "expired".to_string()),
        });
    }
    // A non-stored source: env keys and config mark api-key providers
    // configured; subscription rows stay "unconfigured".
    if let Some(source) = status.source {
        if source != AuthSource::Stored {
            return match auth_type {
                AuthType::ApiKey => Some(AuthStatusIndicator {
                    style: AuthStatusStyle::Success,
                    label: api_key_source_label(source, status.label.as_deref()),
                }),
                AuthType::Oauth => Some(AuthStatusIndicator {
                    style: AuthStatusStyle::Muted,
                    label: "unconfigured".to_string(),
                }),
            };
        }
    }
    if let Some(credential) = credential {
        let credential_type = match credential {
            AuthCredential::ApiKey { .. } | AuthCredential::McpStaticToken { .. } => {
                AuthType::ApiKey
            }
            AuthCredential::Oauth { .. } => AuthType::Oauth,
        };
        return Some(if credential_type == auth_type {
            AuthStatusIndicator {
                style: AuthStatusStyle::Success,
                label: "configured".to_string(),
            }
        } else {
            AuthStatusIndicator {
                style: AuthStatusStyle::Warning,
                label: match credential_type {
                    AuthType::Oauth => "subscription configured".to_string(),
                    AuthType::ApiKey => "API key configured".to_string(),
                },
            }
        });
    }
    if auth_type != AuthType::ApiKey {
        return Some(AuthStatusIndicator {
            style: AuthStatusStyle::Muted,
            label: "unconfigured".to_string(),
        });
    }
    // An unconfigured api-key row hides its meta (TS inline rule).
    None
}

/// TS `formatApiKeyStatusIndicator`.
fn api_key_source_label(source: AuthSource, label: Option<&str>) -> String {
    match source {
        AuthSource::Environment => {
            format!("env: {}", label.unwrap_or("API key"))
        }
        AuthSource::Runtime => "runtime API key".to_string(),
        AuthSource::Fallback => "custom API key".to_string(),
        AuthSource::ModelsJsonKey => "key in models.json".to_string(),
        AuthSource::ModelsJsonCommand => "command in models.json".to_string(),
        AuthSource::Stored | AuthSource::Stale => "unconfigured".to_string(),
    }
}

/// TS `compareAuthSelectorProviders`: oauth before api key, then by name.
fn ts_row_order(a: &ProviderRow, b: &ProviderRow) -> std::cmp::Ordering {
    if a.auth_type != b.auth_type {
        return if a.auth_type == AuthType::Oauth {
            std::cmp::Ordering::Less
        } else {
            std::cmp::Ordering::Greater
        };
    }
    a.name.cmp(&b.name)
}

/// TS `ANTHROPIC_SUBSCRIPTION_AUTH_WARNING` (#2645): subscription
/// requests identify as Claude Code, which may violate Anthropic's
/// terms; an API key avoids the risk.
const ANTHROPIC_SUBSCRIPTION_AUTH_WARNING: &str = "Anthropic subscription auth is active. Usage draws from your plan limits, but Eukhe identifies as Claude Code and this may violate Anthropic's terms -- your account can be restricted or banned. An Anthropic API key avoids the risk. Manage usage at https://claude.ai/settings/usage.";

/// The provider auth surface against one daemon's shared directories.
#[derive(Clone)]
pub struct ProviderAuth {
    cwd: PathBuf,
    agent_dir: PathBuf,
}

impl ProviderAuth {
    pub fn new(cwd: impl Into<PathBuf>, agent_dir: impl Into<PathBuf>) -> Self {
        ProviderAuth {
            cwd: cwd.into(),
            agent_dir: agent_dir.into(),
        }
    }

    fn auth_storage(&self) -> eukhe_core::auth::AuthStorage {
        eukhe_core::auth::AuthStorage::create(&self.agent_dir)
    }

    /// The stored credential + auth status of one provider id.
    fn credential_status(&self, provider_id: &str) -> (Option<AuthCredential>, AuthStatus) {
        let auth = self.auth_storage();
        let credential = auth.get_all().credential(provider_id);
        let status = auth.get_auth_status(provider_id);
        (credential, status)
    }

    /// TS `getAnthropicSubscriptionAuthWarning` (#2645, blocking body):
    /// the ban-risk warning applies when the stored Anthropic credential
    /// is an OAuth login, or the resolved key is a subscription token
    /// (`sk-ant-oat...` -- the same prefix the provider layer treats as
    /// OAuth). `None` = the auth is not a subscription.
    fn anthropic_subscription_warning_blocking(&self) -> Option<&'static str> {
        let mut auth = self.auth_storage();
        if let Some(credential) = auth.get_all().credential("anthropic") {
            if matches!(credential, AuthCredential::Oauth { .. }) {
                return Some(ANTHROPIC_SUBSCRIPTION_AUTH_WARNING);
            }
        }
        auth.get_api_key("anthropic")
            .is_some_and(|key| key.starts_with("sk-ant-oat"))
            .then_some(ANTHROPIC_SUBSCRIPTION_AUTH_WARNING)
    }
}

impl ProviderAuthCommands for ProviderAuth {
    /// TS `getLoginProviderOptions`: the subscription rows and the
    /// API-key model providers, sorted TS-style. The service rows (the
    /// MCP OAuth integrations) live on the
    /// `/mcp` view (the operator's 2026-09-24 `/login`-is-providers-only
    /// directive).
    fn login_options(&self) -> ProviderRowsFuture {
        let provider = self.clone();
        Box::pin(async move {
            // The row build locks the auth store and the MCP manager
            // (blocking mutexes); keep them off the async workers.
            tokio::task::spawn_blocking(move || provider.login_rows_blocking())
                .await
                .expect("the row build task ran")
        })
    }

    /// The `/logout` rows: one per stored account and per MCP server
    /// credential.
    fn logout_options(&self) -> ProviderRowsFuture {
        let provider = self.clone();
        Box::pin(async move {
            // The stored-credential list locks the auth store; keep it
            // off the async workers.
            tokio::task::spawn_blocking(move || provider.logout_rows_blocking())
                .await
                .expect("the row build task ran")
        })
    }

    /// TS `loginProvider`: the API-key store for prompted keys, the MCP
    /// device flow for integrations; the panel-driven subscription flows
    /// route through [`ProviderAuth::login_on_panel`].
    fn login(&self, provider: &ProviderRow, api_key: Option<&str>) -> ProviderAuthFuture {
        let provider_row = provider.clone();
        let agent_dir = self.agent_dir.clone();
        let api_key = api_key.map(str::to_string);
        Box::pin(async move {
            // The auth-store writes and the MCP manager locks stay off
            // the async workers.
            tokio::task::spawn_blocking(move || login_blocking(&provider_row, &agent_dir, api_key))
                .await
                .expect("the login task ran")
        })
    }

    /// TS `loginProvider` for the panel-driven flows (the MCP OAuth
    /// login, the subscription logins): the flow drives the inline auth
    /// panel (progress lines and prompts render in the TUI; the oneshot
    /// replies answer the flow) and never touches
    /// the terminal.
    fn login_on_panel(
        &self,
        provider: &ProviderRow,
        panel: eukhe_tui::auth_panel::AuthPanelHandle,
    ) -> ProviderAuthFuture {
        let provider_row = provider.clone();
        let cwd = self.cwd.clone();
        let agent_dir = self.agent_dir.clone();
        Box::pin(async move {
            // The auth-store writes, the MCP manager locks, and the
            // panel round-trips stay off the async workers (a prompt's
            // answer arrives from the TUI loop's thread).
            tokio::task::spawn_blocking(move || {
                login_blocking_on_panel(&provider_row, cwd, agent_dir, panel)
            })
            .await
            .expect("the login task ran")
        })
    }

    /// TS `getAnthropicSubscriptionAuthWarning` (#2645): the ban-risk
    /// warning for an active Anthropic subscription auth, for the session
    /// surface to show once per run. The store lock (and the key
    /// resolution, which may run a `!command` credential) stay off the
    /// async workers.
    fn anthropic_subscription_warning(&self) -> ProviderWarningFuture {
        let provider = self.clone();
        Box::pin(async move {
            // The lookup is warning-only (TS ignores auth lookup failures
            // the same way), so a hung `!command` credential must not pin
            // the session surface: the TS resolution caps command
            // execution at 10s (`execSyncHidden`/`spawnSyncHidden`
            // `timeout: 10000`), and the check resolves no-warning at the
            // same bound.
            let lookup = tokio::task::spawn_blocking(move || {
                provider.anthropic_subscription_warning_blocking()
            });
            match tokio::time::timeout(std::time::Duration::from_secs(10), lookup).await {
                Ok(joined) => joined.unwrap_or(None),
                Err(_) => None,
            }
        })
    }

    /// `/logout`'s removal of one account
    /// ([`crate::provider_accounts::logout`]).
    fn logout(&self, provider: &str, account: Option<&str>) -> ProviderAuthFuture {
        let agent_dir = self.agent_dir.clone();
        let provider = provider.to_owned();
        let account = account.map(str::to_owned);
        Box::pin(async move {
            // The auth store's file lock stays off the async workers.
            tokio::task::spawn_blocking(move || {
                crate::provider_accounts::logout(&agent_dir, &provider, account.as_deref())
            })
            .await
            .expect("the logout task ran")
        })
    }

    /// `/accounts`: each provider's stored accounts, a limit shown in the
    /// local time zone.
    fn accounts(&self) -> ProviderAccountsFuture {
        let auth = self.clone();
        Box::pin(async move {
            // The auth store's file read stays off the async workers.
            tokio::task::spawn_blocking(move || {
                crate::provider_accounts::listing(
                    &crate::provider_accounts::stored_accounts(&auth.auth_storage()),
                    crate::util_time::now_ms(),
                    &eukhe_daemon::limits_text::local_clock,
                )
            })
            .await
            .expect("the account listing task ran")
        })
    }
}

impl ProviderAuth {
    /// The login row build (blocking: the auth store and MCP manager
    /// locks must stay off the async workers). The operator's 2026-09-24
    /// directive keeps `/login` providers only: the service rows (the MCP
    /// OAuth integrations) live on the `/mcp` view instead.
    pub(crate) fn login_rows_blocking(self) -> Vec<ProviderRow> {
        let provider = self;
        {
            let mut rows: Vec<ProviderRow> = Vec::new();

            // The subscription OAuth rows (TS `getOAuthProviders`).
            // Every flow is ported: the rows select and their logins
            // run through the panel (the menu rule's unavailable
            // marking stays for the surfaces a future row may lack).
            for (id, name) in SUBSCRIPTION_PROVIDERS {
                let (credential, status) = provider.credential_status(id);
                rows.push(ProviderRow {
                    id: id.to_string(),
                    name: name.to_string(),
                    auth_type: AuthType::Oauth,
                    status: status_indicator(credential.as_ref(), &status, AuthType::Oauth),
                    flow: AuthFlow::TerminalFlow,
                    configured: status.configured,
                    available: true,
                    account: None,
                });
            }

            // The API-key model providers (TS `isApiKeyLoginProvider` over
            // the registry's provider set).
            let registry = ModelRegistry::create(
                provider.auth_storage(),
                provider.agent_dir.join("models.json"),
            );
            let built_in_provider_ids: std::collections::HashSet<String> =
                eukhe_models::transports::compiled_provider_ids()
                    .into_iter()
                    .map(str::to_string)
                    .collect();
            let mut providers: Vec<String> = registry
                .get_all()
                .map(|model| model.provider.clone())
                .collect();
            providers.sort();
            providers.dedup();
            for provider_id in providers {
                if !is_api_key_login_provider(&provider_id, &built_in_provider_ids) {
                    continue;
                }
                let (credential, status) = provider.credential_status(&provider_id);
                rows.push(ProviderRow {
                    status: status_indicator(credential.as_ref(), &status, AuthType::ApiKey),
                    id: provider_id.clone(),
                    name: display_name(&provider_id),
                    auth_type: AuthType::ApiKey,
                    flow: AuthFlow::ApiKeyPrompt,
                    configured: status.configured,
                    available: true,
                    account: None,
                });
            }

            // TS sort: configured first, then oauth before api key by
            // name.
            rows.sort_by(|a, b| {
                let configured = |row: &ProviderRow| {
                    matches!(
                        row.status.as_ref().map(|status| status.style),
                        Some(AuthStatusStyle::Success)
                    )
                };
                configured(b).cmp(&configured(a)).then(ts_row_order(a, b))
            });
            rows
        }
    }

    /// The logout row build (blocking: the auth store lock stays off the
    /// async workers): per provider (by name), one row per account
    /// (`<provider>: <label>`) in login order, and an MCP server's row.
    fn logout_rows_blocking(self) -> Vec<ProviderRow> {
        let auth = self.auth_storage();
        let data = auth.get_all();
        let mut groups: Vec<(String, Vec<ProviderRow>)> = auth
            .list()
            .into_iter()
            .map(|provider_id| {
                if let Some(server) = provider_id.strip_prefix("mcp:") {
                    let row = data
                        .get(&provider_id)
                        .and_then(Value::as_object)
                        .map(|credential| {
                            stored_row(&provider_id, server.to_owned(), credential, None)
                        });
                    (server.to_owned(), row.into_iter().collect())
                } else {
                    let name = display_name(&provider_id);
                    let rows = data
                        .accounts(&provider_id)
                        .iter()
                        .enumerate()
                        .map(|(at, account)| {
                            let label = account.label(at + 1);
                            // The identity names the account; one without
                            // an identity goes by its place.
                            let selector = if account.identity.is_empty() {
                                (at + 1).to_string()
                            } else {
                                account.identity.clone()
                            };
                            stored_row(
                                &provider_id,
                                format!("{name}: {label}"),
                                &account.credential,
                                Some(selector),
                            )
                        })
                        .collect();
                    (name, rows)
                }
            })
            .collect();
        groups.sort_by(|(left, _), (right, _)| left.cmp(right));
        groups.into_iter().flat_map(|(_, rows)| rows).collect()
    }
}

/// One `/logout` row of a stored credential object: its auth type is the
/// credential's `type`.
fn stored_row(
    provider_id: &str,
    name: String,
    credential: &serde_json::Map<String, Value>,
    account: Option<String>,
) -> ProviderRow {
    let auth_type = match credential.get("type").and_then(Value::as_str) {
        Some("oauth") => AuthType::Oauth,
        Some(_) | None => AuthType::ApiKey,
    };
    ProviderRow {
        id: provider_id.to_owned(),
        name,
        auth_type,
        status: Some(AuthStatusIndicator {
            style: AuthStatusStyle::Success,
            label: "configured".to_string(),
        }),
        flow: AuthFlow::TerminalFlow,
        // The stored-credential rows exist because the credential is
        // there; their removal always runs.
        configured: true,
        available: true,
        account,
    }
}

/// The login flow body (blocking: the auth store and the MCP manager stay
/// off the async workers). The panel-driven rows (the MCP OAuth logins,
/// the subscription logins) route to
/// [`login_blocking_on_panel`]; this body serves the panel-prompted key
/// store, and an OAuth row reaching it answers the silent cancel (the
/// session routes the panel rows to the panel body).
pub(crate) fn login_blocking(
    provider_row: &ProviderRow,
    agent_dir: &Path,
    api_key: Option<String>,
) -> ProviderAuthOutcome {
    if provider_row.auth_type == AuthType::Oauth {
        // The panel-driven flows (the MCP logins, the subscription
        // logins) run on the panel. An OAuth row reaching this
        // non-panel body answers the silent cancel -- the session
        // routes the panel rows to the panel body, and no row dead-ends
        // in an after-selection error wall.
        return ProviderAuthOutcome::Cancelled;
    }
    let Some(api_key) = api_key.filter(|key| !key.is_empty()) else {
        return ProviderAuthOutcome::Error(format!(
            "Failed to save API key for {}: API key cannot be empty.",
            provider_row.name
        ));
    };
    // A new key adds an account; the same key again replaces it.
    let mut auth = eukhe_core::auth::AuthStorage::create(agent_dir);
    let account = match auth.add_account(
        &provider_row.id,
        AuthCredential::ApiKey { key: api_key },
        "",
    ) {
        Ok(account) => account,
        Err(error) => {
            return ProviderAuthOutcome::Error(format!("could not save the API key: {error}"));
        }
    };
    ProviderAuthOutcome::Status(format!(
        "Saved API key for {} as {account}. Credentials saved to {}",
        provider_row.name,
        agent_dir.join("auth.json").display()
    ))
}

/// The login flow body for the panel-driven rows (the MCP OAuth logins,
/// the four subscription logins): blocking on the dedicated thread --
/// the flow awaits its transport AND the panel's prompt replies (the
/// answers arrive from the TUI loop's thread), and the inline auth panel
/// carries every surface the plain terminal used to.
fn login_blocking_on_panel(
    provider_row: &ProviderRow,
    cwd: PathBuf,
    agent_dir: PathBuf,
    panel: eukhe_tui::auth_panel::AuthPanelHandle,
) -> ProviderAuthOutcome {
    if let Some(server) = provider_row.id.strip_prefix("mcp:") {
        let auth = crate::mcp_login::TerminalMcpAuth::new(cwd, agent_dir);
        let outcome = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .map_or_else(
                |error: std::io::Error| format!("login failed: {error}"),
                |runtime| {
                    runtime.block_on(eukhe_tui::client_auth::run_mcp_auth_command(
                        &auth,
                        &format!("login {server}"),
                        panel,
                    ))
                },
            );
        return if outcome.starts_with("Usage:") {
            ProviderAuthOutcome::Error(outcome)
        } else {
            ProviderAuthOutcome::Status(outcome)
        };
    }
    // The four subscription logins (TS `loginProvider`'s dispatch to the
    // AI library's `openaiCodex`, `anthropic`, `githubCopilot`, and `xai`
    // OAuth providers): the provider's pi-ai flow -- the browser
    // authorization URL block and the manual paste racing the localhost
    // callback, or the device flow -- and the credential write, all
    // through the inline auth panel (TS the login dialog).
    if let Some(flow) = eukhe_core::auth::subscription_oauth_flow(&provider_row.id) {
        return tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .map_or_else(
                |error: std::io::Error| {
                    ProviderAuthOutcome::Error(format!(
                        "Failed to login to {}: {error}",
                        provider_row.name
                    ))
                },
                |runtime| {
                    runtime.block_on(crate::subscription_login::run_subscription_login(
                        &agent_dir,
                        &provider_row.id,
                        &provider_row.name,
                        flow.as_ref(),
                        &crate::subscription_login::LoginSurface::new(panel),
                    ))
                },
            );
    }
    // Any other row that reaches the panel body answers the silent
    // cancel (the session routes only the ported rows here -- never an
    // error wall).
    ProviderAuthOutcome::Cancelled
}

#[cfg(test)]
mod tests;
