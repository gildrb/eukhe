//! `eukhe login [<provider>]`: the logins of the TUI's `/login` on the plain
//! terminal, for hosts and scripts without the TUI. The same rows, flows
//! and `auth.json` accounts (a login as a new identity adds an account; as
//! a known one, it replaces that account). The subscription logins drive
//! the inline auth panel's requests through [`terminal_panel`]: the
//! sign-in URL and the progress on stderr, a prompt answered by a line on
//! stdin. An API key comes from `EUKHE_LOGIN_API_KEY`, piped stdin or a
//! hidden prompt, never from the arguments. Success prints one line on
//! stdout. Exit codes: 0 logged in, 1 failed, 2 usage.

use std::io::{IsTerminal as _, Read as _};
use std::path::Path;

use eukhe_tui::auth_panel::AuthPanelHandle;
use eukhe_tui::provider_auth::{AuthStatusStyle, AuthType, ProviderAuthOutcome, ProviderRow};
use serde_json::{json, Value};

use crate::list_models::pad_end;
use crate::provider_login::{login_blocking, ProviderAuth};
use crate::subscription_login::{run_subscription_login, BrowserOpener, LoginMethod, LoginSurface};

mod terminal_panel;

/// The variable `eukhe login` reads an API key from.
const API_KEY_ENV: &str = "EUKHE_LOGIN_API_KEY";

/// The subscription logins with a device-code flow: the Codex
/// Subscription's is an option (`--device`); xAI and GitHub Copilot have
/// only that one.
const DEVICE_CODE_PROVIDERS: [&str; 3] = ["openai-codex", "github-copilot", "xai"];

/// How the listing prints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Output {
    Table,
    Json,
}

/// The credential a login stores.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Credential {
    /// The provider's subscription login, else its API key.
    Default,
    /// An API key (`--key`).
    ApiKey,
}

/// Whether the login opens the sign-in URL in the browser.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Browser {
    Open,
    /// `--no-browser`: the URL is only printed.
    Skip,
}

/// The parsed `eukhe login` invocation.
#[derive(Debug, PartialEq, Eq)]
enum LoginCommand {
    /// The providers and their login state.
    List { output: Output },
    Login {
        provider: String,
        credential: Credential,
        method: LoginMethod,
        browser: Browser,
    },
}

/// Why the `login` arguments name no login.
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
enum LoginUsageError {
    #[error("unknown option: {0}")]
    UnknownOption(String),
    #[error(
        "Usage: eukhe login [--json] | eukhe login <provider> [--key | --device] [--no-browser]"
    )]
    Usage,
    #[error("Unknown provider: {0}. \"eukhe login\" lists the providers.")]
    UnknownProvider(String),
    #[error("{0} has no API-key login.")]
    NoApiKeyLogin(String),
    #[error("{0} has no device-code login.")]
    NoDeviceCodeLogin(String),
}

/// Run `eukhe login`; returns the process exit code.
pub fn run_login_command(args: &[String]) -> i32 {
    let command = match parse_login_command(args) {
        Ok(command) => command,
        Err(error) => return usage_failure(&error),
    };
    let agent_dir = crate::config::get_agent_dir();
    let auth = ProviderAuth::new(std::env::current_dir().unwrap_or_default(), &agent_dir);
    // A stored Claude subscription login, or an `anthropic` login asked
    // without `--key` (once the subscription login): the migration notice,
    // once, on stderr.
    let asks_claude_subscription = matches!(
        &command,
        LoginCommand::Login { provider, credential: Credential::Default, .. }
            if provider == "anthropic"
    );
    if let Some(notice) = auth.claude_login_notice().or_else(|| {
        asks_claude_subscription.then_some(eukhe_ai::api::anthropic_messages::CLAUDE_LOGIN_MOVED)
    }) {
        eprintln!("{notice}");
    }
    let rows = auth.login_rows_blocking();
    match command {
        LoginCommand::List { output } => print_listing(&rows, output),
        LoginCommand::Login {
            provider,
            credential,
            method,
            browser,
        } => match chosen_row(rows, &provider, credential, method) {
            Ok(row) => report(match row.auth_type {
                AuthType::Oauth => run_subscription(&row, &agent_dir, method, browser),
                AuthType::ApiKey => store_api_key(&row, &agent_dir),
            }),
            Err(error) => usage_failure(&error),
        },
    }
}

fn parse_login_command(args: &[String]) -> Result<LoginCommand, LoginUsageError> {
    let mut output = Output::Table;
    let mut credential = Credential::Default;
    let mut method = LoginMethod::Default;
    let mut browser = Browser::Open;
    let mut operands: Vec<String> = Vec::new();
    for arg in args {
        match arg.as_str() {
            "--json" => output = Output::Json,
            "--key" => credential = Credential::ApiKey,
            "--device" => method = LoginMethod::DeviceCode,
            "--no-browser" => browser = Browser::Skip,
            other if other.starts_with('-') => {
                return Err(LoginUsageError::UnknownOption(other.to_owned()));
            }
            other => operands.push(other.to_owned()),
        }
    }
    match (operands.as_slice(), output, credential, method, browser) {
        ([], output, Credential::Default, LoginMethod::Default, Browser::Open) => {
            Ok(LoginCommand::List { output })
        }
        ([provider], Output::Table, Credential::ApiKey, LoginMethod::Default, browser)
        | (
            [provider],
            Output::Table,
            Credential::Default,
            LoginMethod::Default | LoginMethod::DeviceCode,
            browser,
        ) => Ok(LoginCommand::Login {
            provider: provider.clone(),
            credential,
            method,
            browser,
        }),
        _ => Err(LoginUsageError::Usage),
    }
}

/// The login row `provider` names: its subscription login unless `--key`
/// asks for its API key; a provider without a subscription login logs in
/// with its key.
fn chosen_row(
    rows: Vec<ProviderRow>,
    provider: &str,
    credential: Credential,
    method: LoginMethod,
) -> Result<ProviderRow, LoginUsageError> {
    let (oauth, api_key): (Vec<ProviderRow>, Vec<ProviderRow>) = rows
        .into_iter()
        .filter(|row| row.id == provider)
        .partition(|row| row.auth_type == AuthType::Oauth);
    let row = match (
        credential,
        oauth.into_iter().next(),
        api_key.into_iter().next(),
    ) {
        (_, None, None) => return Err(LoginUsageError::UnknownProvider(provider.to_owned())),
        (Credential::ApiKey, Some(_), None) => {
            return Err(LoginUsageError::NoApiKeyLogin(provider.to_owned()));
        }
        (Credential::ApiKey | Credential::Default, None, Some(row))
        | (Credential::ApiKey, Some(_), Some(row))
        | (Credential::Default, Some(row), _) => row,
    };
    let device_code = row.auth_type == AuthType::Oauth && DEVICE_CODE_PROVIDERS.contains(&provider);
    match (method, device_code) {
        (LoginMethod::DeviceCode, false) => {
            Err(LoginUsageError::NoDeviceCodeLogin(provider.to_owned()))
        }
        (LoginMethod::DeviceCode, true) | (LoginMethod::Default, _) => Ok(row),
    }
}

/// A usage failure: the error, the help hint, exit 2.
fn usage_failure(error: &LoginUsageError) -> i32 {
    eprintln!("Error: {error}");
    eprintln!("Run \"{} help login\" for usage.", crate::config::APP_NAME);
    2
}

/// The login's one line: the status on stdout (exit 0), or the error on
/// stderr (exit 1).
fn report(outcome: ProviderAuthOutcome) -> i32 {
    match outcome {
        ProviderAuthOutcome::Status(status) => {
            println!("{status}");
            0
        }
        ProviderAuthOutcome::Error(error) => {
            eprintln!("Error: {error}");
            1
        }
        ProviderAuthOutcome::Cancelled => {
            eprintln!("Error: login cancelled");
            1
        }
    }
}

/// Whether a row's provider is logged in: the row's status is the
/// configured one (a stored credential of its kind, or an API key from the
/// environment or models.json).
fn logged_in(row: &ProviderRow) -> bool {
    matches!(
        row.status.as_ref().map(|status| status.style),
        Some(AuthStatusStyle::Success)
    )
}

/// The listing, then exit 0 when a provider is logged in, else 1.
fn print_listing(rows: &[ProviderRow], output: Output) -> i32 {
    match output {
        Output::Table => println!("{}", listing_table(rows)),
        Output::Json => {
            if let Err(error) = crate::json_out::print_json_document(&listing_json(rows)) {
                eprintln!("Error: {error}");
                return 1;
            }
        }
    }
    i32::from(!rows.iter().any(logged_in))
}

/// `provider  login  status  name`, `-` for a row without a status,
/// columns padded to their widest cell.
fn listing_table(rows: &[ProviderRow]) -> String {
    const HEADERS: [&str; 4] = ["provider", "login", "status", "name"];
    let cells: Vec<[&str; 4]> = rows
        .iter()
        .map(|row| {
            [
                row.id.as_str(),
                row.auth_type.label(),
                row.status
                    .as_ref()
                    .map_or("-", |status| status.label.as_str()),
                row.name.as_str(),
            ]
        })
        .collect();
    let widths = cells.iter().fold(HEADERS.map(str::len), |widths, row| {
        std::array::from_fn(|at| widths[at].max(row[at].chars().count()))
    });
    std::iter::once(HEADERS)
        .chain(cells)
        .map(|row| {
            row.iter()
                .zip(widths)
                .map(|(cell, width)| pad_end(cell, width))
                .collect::<Vec<_>>()
                .join("  ")
                .trim_end()
                .to_owned()
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// `{"providers":[{"provider","name","method":"oauth"|"api_key",
/// "loggedIn","status"}]}`.
fn listing_json(rows: &[ProviderRow]) -> Value {
    let providers: Vec<Value> = rows
        .iter()
        .map(|row| {
            json!({
                "provider": row.id,
                "name": row.name,
                "method": match row.auth_type {
                    AuthType::Oauth => "oauth",
                    AuthType::ApiKey => "api_key",
                },
                "loggedIn": logged_in(row),
                "status": row.status.as_ref().map(|status| status.label.clone()),
            })
        })
        .collect();
    json!({ "providers": providers })
}

/// The subscription login on the plain terminal: the provider's flow
/// against a panel whose requests [`terminal_panel::serve`] answers.
fn run_subscription(
    row: &ProviderRow,
    agent_dir: &Path,
    method: LoginMethod,
    browser: Browser,
) -> ProviderAuthOutcome {
    let Some(flow) = eukhe_core::auth::subscription_oauth_flow(&row.id) else {
        return ProviderAuthOutcome::Error(format!("{} has no subscription login", row.name));
    };
    let runtime = match tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(error) => {
            return ProviderAuthOutcome::Error(format!("Failed to login to {}: {error}", row.name));
        }
    };
    let open_browser: BrowserOpener = match browser {
        Browser::Open => eukhe_core::platform::browser::open_in_browser,
        Browser::Skip => |_url| {},
    };
    runtime.block_on(async {
        let (requests_tx, requests) = tokio::sync::mpsc::unbounded_channel();
        let surface = LoginSurface::with(AuthPanelHandle::new(requests_tx), open_browser, method);
        // The surface (the panel's sender) drops with the login, which
        // ends the terminal's request loop.
        let login = async move {
            run_subscription_login(agent_dir, &row.id, &row.name, flow.as_ref(), &surface).await
        };
        let (outcome, _stderr) = tokio::join!(
            login,
            terminal_panel::serve(requests, terminal_panel::stdin_lines(), std::io::stderr())
        );
        outcome
    })
}

/// The API-key login: the key stored as `/login` stores it.
fn store_api_key(row: &ProviderRow, agent_dir: &Path) -> ProviderAuthOutcome {
    match api_key_input(&row.name) {
        Ok(Some(key)) => login_blocking(row, agent_dir, Some(key)),
        Ok(None) => ProviderAuthOutcome::Cancelled,
        Err(error) => ProviderAuthOutcome::Error(format!("could not read the API key: {error}")),
    }
}

/// The API key: `EUKHE_LOGIN_API_KEY`, else piped stdin, else typed on the
/// terminal without echo. `None`: the prompt was cancelled.
fn api_key_input(provider_name: &str) -> std::io::Result<Option<String>> {
    if let Some(key) = std::env::var(API_KEY_ENV)
        .ok()
        .filter(|key| !key.trim().is_empty())
    {
        return Ok(Some(key.trim().to_owned()));
    }
    let mut stdin = std::io::stdin();
    if stdin.is_terminal() {
        return terminal_panel::hidden_line(&format!("Enter API key for {provider_name}: "));
    }
    let mut key = String::new();
    stdin.read_to_string(&mut key)?;
    Ok(Some(key.trim().to_owned()))
}

#[cfg(test)]
mod tests;
