use eukhe_tui::provider_auth::{AuthFlow, AuthStatusIndicator};

use super::*;

fn args(words: &[&str]) -> Vec<String> {
    words.iter().map(ToString::to_string).collect()
}

fn login(
    provider: &str,
    credential: Credential,
    method: LoginMethod,
    browser: Browser,
) -> LoginCommand {
    LoginCommand::Login {
        provider: provider.to_string(),
        credential,
        method,
        browser,
    }
}

#[test]
fn parses_the_listing_and_the_logins() {
    let parsed: Vec<Result<LoginCommand, LoginUsageError>> = [
        &[][..],
        &["--json"],
        &["anthropic"],
        &["openai", "--key"],
        &["--device", "openai-codex", "--no-browser"],
        &["anthropic", "--key", "--device"],
        &["anthropic", "--json"],
        &["anthropic", "xai"],
        &["--no-browser"],
        &["anthropic", "--api-key=sk"],
    ]
    .iter()
    .map(|words| parse_login_command(&args(words)))
    .collect();
    assert_eq!(
        parsed,
        vec![
            Ok(LoginCommand::List {
                output: Output::Table
            }),
            Ok(LoginCommand::List {
                output: Output::Json
            }),
            Ok(login(
                "anthropic",
                Credential::Default,
                LoginMethod::Default,
                Browser::Open
            )),
            Ok(login(
                "openai",
                Credential::ApiKey,
                LoginMethod::Default,
                Browser::Open
            )),
            Ok(login(
                "openai-codex",
                Credential::Default,
                LoginMethod::DeviceCode,
                Browser::Skip
            )),
            Err(LoginUsageError::Usage),
            Err(LoginUsageError::Usage),
            Err(LoginUsageError::Usage),
            Err(LoginUsageError::Usage),
            Err(LoginUsageError::UnknownOption("--api-key=sk".to_string())),
        ]
    );
}

fn row(id: &str, auth_type: AuthType, status: Option<(AuthStatusStyle, &str)>) -> ProviderRow {
    ProviderRow {
        id: id.to_string(),
        name: format!("{id} {}", auth_type.label()),
        auth_type,
        status: status.map(|(style, label)| AuthStatusIndicator {
            style,
            label: label.to_string(),
        }),
        flow: match auth_type {
            AuthType::Oauth => AuthFlow::TerminalFlow,
            AuthType::ApiKey => AuthFlow::ApiKeyPrompt,
        },
        configured: false,
        available: true,
        account: None,
    }
}

fn rows() -> Vec<ProviderRow> {
    vec![
        row(
            "anthropic",
            AuthType::Oauth,
            Some((AuthStatusStyle::Success, "configured")),
        ),
        row(
            "openai-codex",
            AuthType::Oauth,
            Some((AuthStatusStyle::Muted, "unconfigured")),
        ),
        row("anthropic", AuthType::ApiKey, None),
        row(
            "openai",
            AuthType::ApiKey,
            Some((AuthStatusStyle::Success, "env: OPENAI_API_KEY")),
        ),
    ]
}

/// A provider with both logins takes its subscription unless `--key`; a
/// key-only provider takes its key; `--key` and `--device` need a login of
/// that kind.
#[test]
fn chooses_the_row_the_options_name() {
    let chosen = |provider: &str, credential, method| {
        chosen_row(rows(), provider, credential, method).map(|row| (row.id, row.auth_type))
    };
    assert_eq!(
        [
            chosen("anthropic", Credential::Default, LoginMethod::Default),
            chosen("anthropic", Credential::ApiKey, LoginMethod::Default),
            chosen("openai", Credential::Default, LoginMethod::Default),
            chosen("openai-codex", Credential::Default, LoginMethod::DeviceCode),
            chosen("openai-codex", Credential::ApiKey, LoginMethod::Default),
            chosen("anthropic", Credential::Default, LoginMethod::DeviceCode),
            chosen("openai", Credential::Default, LoginMethod::DeviceCode),
            chosen("nope", Credential::Default, LoginMethod::Default),
        ],
        [
            Ok(("anthropic".to_string(), AuthType::Oauth)),
            Ok(("anthropic".to_string(), AuthType::ApiKey)),
            Ok(("openai".to_string(), AuthType::ApiKey)),
            Ok(("openai-codex".to_string(), AuthType::Oauth)),
            Err(LoginUsageError::NoApiKeyLogin("openai-codex".to_string())),
            Err(LoginUsageError::NoDeviceCodeLogin("anthropic".to_string())),
            Err(LoginUsageError::NoDeviceCodeLogin("openai".to_string())),
            Err(LoginUsageError::UnknownProvider("nope".to_string())),
        ]
    );
}

#[test]
fn lists_each_login_with_its_state() {
    assert_eq!(
        listing_table(&rows()),
        "provider      login         status               name\n\
         anthropic     subscription  configured           anthropic subscription\n\
         openai-codex  subscription  unconfigured         openai-codex subscription\n\
         anthropic     api key       -                    anthropic api key\n\
         openai        api key       env: OPENAI_API_KEY  openai api key"
    );
    assert_eq!(
        listing_json(&rows()[1..3]),
        json!({ "providers": [
            {
                "provider": "openai-codex",
                "name": "openai-codex subscription",
                "method": "oauth",
                "loggedIn": false,
                "status": "unconfigured",
            },
            {
                "provider": "anthropic",
                "name": "anthropic api key",
                "method": "api_key",
                "loggedIn": false,
                "status": null,
            },
        ] })
    );
}
