//! `eukhe provider`: the provider capability surface and the stored
//! accounts.
//!
//! `caps` prints what each provider's API offers besides chat streaming,
//! read from the quirks rulebook through `Models::provider_capabilities`; it
//! sends nothing. `models` asks the named provider's own model-listing
//! endpoint: the one subcommand that talks to the network, and only to the
//! provider the user configured. A provider without the operation fails
//! with a message, never a fallback. `accounts` lists each provider's
//! stored accounts; `logout` removes one.

use eukhe_ai::capabilities::{Capabilities, Capability, ListedModel, Support};
use eukhe_ai::models::{Models, ModelsCapabilityOptions};
use eukhe_core::auth::AuthStorage;
use eukhe_tui::provider_auth::ProviderAuthOutcome;

use crate::list_models::{format_token_count, pad_end};

/// How a subcommand prints its result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Output {
    Table,
    Json,
}

/// Which providers `caps` covers.
#[derive(Debug, PartialEq, Eq)]
enum Selection {
    /// Every provider with chat models.
    Every,
    Named(String),
}

/// The parsed `eukhe provider` invocation.
#[derive(Debug, PartialEq, Eq)]
enum ProviderCommand {
    Caps {
        selection: Selection,
        output: Output,
    },
    Models {
        provider: String,
        output: Output,
    },
    Accounts {
        output: Output,
    },
    /// Remove one stored account: the one `account` names (a place from 1
    /// or an identity), else the provider's only one.
    Logout {
        provider: String,
        account: Option<String>,
    },
}

/// Why the `provider` arguments do not parse.
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
enum ProviderUsageError {
    /// No subcommand.
    #[error("Missing provider command.")]
    Missing,
    #[error(
        "Unknown provider command: {subcommand}{}",
        .suggestion.as_ref().map_or_else(String::new, |s| format!(" (did you mean \"{s}\"?)"))
    )]
    Unknown {
        subcommand: String,
        suggestion: Option<String>,
    },
    #[error("unknown option: {0}")]
    UnknownOption(String),
    #[error("Usage: eukhe provider caps [<provider>] [--json]")]
    CapsUsage,
    #[error("Usage: eukhe provider models <provider> [--json]")]
    ModelsUsage,
    #[error("Usage: eukhe provider accounts [--json]")]
    AccountsUsage,
    #[error("Usage: eukhe provider logout <provider> [n|identity]")]
    LogoutUsage,
}

/// A provider id no chat model of the collection names.
#[derive(Debug, thiserror::Error)]
#[error("Couldn't find provider {0} in the catalog. The providers with chat models:\n    eukhe provider caps")]
struct UnknownProvider(String);

/// Parse the subcommand and its flags.
fn parse_provider_command(args: &[String]) -> Result<ProviderCommand, ProviderUsageError> {
    let children: Vec<&str> = crate::command_registry::get_child_command_specs(&["provider"])
        .into_iter()
        .map(|spec| spec.path[spec.path.len() - 1])
        .collect();
    let Some(subcommand) = args.first() else {
        return Err(ProviderUsageError::Missing);
    };
    if !children.contains(&subcommand.as_str()) {
        return Err(ProviderUsageError::Unknown {
            subcommand: subcommand.clone(),
            suggestion: eukhe_bend::rules::slash::suggestion(subcommand, &children)
                .map(str::to_owned),
        });
    }
    let mut output = Output::Table;
    let mut operands: Vec<String> = Vec::new();
    for arg in &args[1..] {
        match arg.as_str() {
            "--json" => output = Output::Json,
            other if other.starts_with('-') => {
                return Err(ProviderUsageError::UnknownOption(other.to_owned()));
            }
            other => operands.push(other.to_string()),
        }
    }
    match subcommand.as_str() {
        "caps" => {
            if operands.len() > 1 {
                return Err(ProviderUsageError::CapsUsage);
            }
            Ok(ProviderCommand::Caps {
                selection: operands.pop().map_or(Selection::Every, Selection::Named),
                output,
            })
        }
        "models" => {
            if operands.len() != 1 {
                return Err(ProviderUsageError::ModelsUsage);
            }
            Ok(ProviderCommand::Models {
                provider: operands.remove(0),
                output,
            })
        }
        "accounts" => {
            if !operands.is_empty() {
                return Err(ProviderUsageError::AccountsUsage);
            }
            Ok(ProviderCommand::Accounts { output })
        }
        // An identity may span several words (`a@x.com [org-1]`).
        "logout" => match (output, operands.split_first()) {
            (Output::Table, Some((provider, account))) => Ok(ProviderCommand::Logout {
                provider: provider.clone(),
                account: (!account.is_empty()).then(|| account.join(" ")),
            }),
            (Output::Table, None) | (Output::Json, _) => Err(ProviderUsageError::LogoutUsage),
        },
        _ => Err(ProviderUsageError::Missing),
    }
}

/// Run the `provider` command; returns the process exit code.
pub fn run_provider_command(args: &[String]) -> i32 {
    let command = match parse_provider_command(args) {
        Ok(command) => command,
        Err(error) => {
            eprintln!("Error: {error}");
            eprintln!(
                "Run \"{} help provider\" for usage.",
                crate::config::APP_NAME
            );
            return 2;
        }
    };
    match command {
        ProviderCommand::Caps { selection, output } => run_caps(&load_models(), &selection, output),
        ProviderCommand::Models { provider, output } => {
            run_models(&load_models(), &provider, output)
        }
        ProviderCommand::Accounts { output } => run_accounts(output),
        ProviderCommand::Logout { provider, account } => run_logout(&provider, account.as_deref()),
    }
}

/// The model collection of `caps` and `models`: models.json's problems
/// printed, its requests spending from the daemon's budget account.
fn load_models() -> Models {
    let loaded = eukhe_core::durable::create_models(&crate::config::get_agent_dir());
    if !loaded.diagnostics.is_empty() {
        eprintln!(
            "Warning: errors loading models.json:\n{}",
            loaded.diagnostics.join("\n")
        );
    }
    let models = loaded.models;
    // No task: any request it sends passes the daemon's budget account.
    let agent_dir = crate::config::get_agent_dir();
    eukhe_core::durable::budget::wrap_models_with_budget(
        &models,
        &eukhe_core::durable::budget::BudgetGate::daemon(&agent_dir),
    );
    models
}

/// `provider accounts`: each provider's stored accounts by place and
/// label, a limit with its local reset time while it lasts.
fn run_accounts(output: Output) -> i32 {
    let agent_dir = crate::config::get_agent_dir();
    let auth = AuthStorage::create(&agent_dir);
    if let Some(error) = auth.load_error() {
        eprintln!(
            "Error: {} could not be loaded: {error}",
            agent_dir.join(eukhe_core::auth::AUTH_FILE_NAME).display()
        );
        return 1;
    }
    let stored = crate::provider_accounts::stored_accounts(&auth);
    match output {
        Output::Json => print_json(&crate::provider_accounts::listing_json(&stored)),
        Output::Table => {
            let listing = crate::provider_accounts::listing(
                &stored,
                crate::util_time::now_ms(),
                &eukhe_daemon::limits_text::local_clock,
            );
            println!(
                "{}",
                eukhe_tui::provider_auth::accounts_text(
                    &listing,
                    &std::collections::BTreeMap::new()
                )
            );
            0
        }
    }
}

/// `provider logout <provider> [n|identity]`: remove one stored account.
fn run_logout(provider: &str, account: Option<&str>) -> i32 {
    match crate::provider_accounts::logout(&crate::config::get_agent_dir(), provider, account) {
        ProviderAuthOutcome::Status(message) => {
            println!("{message}");
            0
        }
        ProviderAuthOutcome::Error(message) => {
            eprintln!("Error: {message}");
            1
        }
        ProviderAuthOutcome::Cancelled => 1,
    }
}

/// The capability rows of the selected providers; every provider with
/// chat models is sorted by provider id. Sends nothing.
fn capability_rows(
    models: &Models,
    selection: &Selection,
) -> Result<Vec<Capabilities>, UnknownProvider> {
    match selection {
        Selection::Named(id) => {
            let rows = models.provider_capabilities(id);
            if rows.is_empty() {
                return Err(UnknownProvider(id.clone()));
            }
            Ok(rows)
        }
        Selection::Every => {
            let mut ids: Vec<String> = models
                .get_providers()
                .iter()
                .map(|provider| provider.id.clone())
                .collect();
            ids.sort();
            Ok(ids
                .iter()
                .flat_map(|id| models.provider_capabilities(id))
                .collect())
        }
    }
}

/// `provider caps [<provider>]`: the rulebook's capability table.
fn run_caps(models: &Models, selection: &Selection, output: Output) -> i32 {
    let rows = match capability_rows(models, selection) {
        Ok(rows) => rows,
        Err(error) => {
            eprintln!("Error: {error}");
            return 1;
        }
    };
    match output {
        Output::Json => print_json(&rows),
        Output::Table => {
            println!("{}", render_capabilities(&rows));
            0
        }
    }
}

/// One block per (provider, api, base URL): a header line, then one line
/// per capability with `<dialect>: <endpoint>` or `unsupported`.
fn render_capabilities(rows: &[Capabilities]) -> String {
    let width = Capability::ALL
        .iter()
        .map(|capability| capability.as_str().chars().count())
        .max()
        .unwrap_or(0);
    rows.iter()
        .map(|row| {
            let header = format!("{}  {}  {}", row.provider, row.api, row.base_url);
            let lines = row.entries.iter().map(|entry| {
                let support = match entry.support {
                    Support::Native { dialect, endpoint } => format!("{dialect}: {endpoint}"),
                    Support::Unsupported => "unsupported".to_string(),
                };
                format!("  {}  {support}", pad_end(entry.capability.as_str(), width))
            });
            std::iter::once(header)
                .chain(lines)
                .collect::<Vec<_>>()
                .join("\n")
        })
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// `provider models <provider>`: the provider's own model listing, asked
/// through its first chat model (catalog order) that has `list_models`.
fn run_models(models: &Models, provider: &str, output: Output) -> i32 {
    let chat_models = models.get_models(Some(provider));
    if chat_models.is_empty() {
        eprintln!("Error: {}", UnknownProvider(provider.to_owned()));
        return 1;
    }
    let Some(model) = chat_models.into_iter().find(|model| {
        matches!(
            models.capabilities(model).support(Capability::ListModels),
            Support::Native { .. }
        )
    }) else {
        eprintln!("Error: Provider {provider} does not offer model listing (list_models).");
        return 1;
    };
    let Ok(runtime) = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    else {
        eprintln!("Error: could not start the provider runtime.");
        return 1;
    };
    let listed =
        match runtime.block_on(models.list_models(&model, ModelsCapabilityOptions::default())) {
            Ok(listed) => listed,
            Err(error) => {
                eprintln!("Error: {error}");
                return 1;
            }
        };
    match output {
        Output::Json => print_json(&listed),
        Output::Table => {
            println!("{}", render_listing(&listed));
            0
        }
    }
}

/// The listing table: `id  name  context  max-out`, `-` for a value the
/// provider does not give, columns padded to their widest cell, on a
/// terminal and piped alike.
fn render_listing(listed: &[ListedModel]) -> String {
    const HEADERS: [&str; 4] = ["id", "name", "context", "max-out"];
    let tokens = |count: Option<u64>| count.map_or_else(|| "-".to_string(), format_token_count);
    let rows: Vec<[String; 4]> = listed
        .iter()
        .map(|model| {
            [
                model.id.clone(),
                model.name.clone().unwrap_or_else(|| "-".to_string()),
                tokens(model.context_window),
                tokens(model.max_output_tokens),
            ]
        })
        .collect();
    let mut widths = HEADERS.map(|header| header.chars().count());
    for row in &rows {
        for (width, cell) in widths.iter_mut().zip(row) {
            *width = (*width).max(cell.chars().count());
        }
    }
    let line = |cells: [&str; 4]| -> String {
        cells
            .iter()
            .zip(widths)
            .map(|(cell, width)| pad_end(cell, width))
            .collect::<Vec<_>>()
            .join("  ")
            .trim_end()
            .to_string()
    };
    std::iter::once(line(HEADERS))
        .chain(
            rows.iter()
                .map(|row| line(row.each_ref().map(String::as_str))),
        )
        .collect::<Vec<_>>()
        .join("\n")
}

/// Print `value` as the JSON contract's document (pretty on a terminal,
/// compact when piped); returns the exit code.
fn print_json<T: serde::Serialize>(value: &T) -> i32 {
    match crate::json_out::print_json_document(value) {
        Ok(()) => 0,
        Err(error) => {
            eprintln!("Error: {error}");
            1
        }
    }
}

#[cfg(test)]
mod tests {
    use eukhe_ai::capabilities::{CapabilitySupport, Dialect};

    use super::*;

    fn arg(words: &[&str]) -> Vec<String> {
        words.iter().map(ToString::to_string).collect()
    }

    #[test]
    fn parses_caps_and_models() {
        assert_eq!(
            parse_provider_command(&arg(&["caps"])),
            Ok(ProviderCommand::Caps {
                selection: Selection::Every,
                output: Output::Table,
            })
        );
        assert_eq!(
            parse_provider_command(&arg(&["caps", "llama-cpp", "--json"])),
            Ok(ProviderCommand::Caps {
                selection: Selection::Named("llama-cpp".to_string()),
                output: Output::Json,
            })
        );
        assert_eq!(
            parse_provider_command(&arg(&["models", "anthropic"])),
            Ok(ProviderCommand::Models {
                provider: "anthropic".to_string(),
                output: Output::Table,
            })
        );
        assert_eq!(
            parse_provider_command(&arg(&["models", "--json", "openai"])),
            Ok(ProviderCommand::Models {
                provider: "openai".to_string(),
                output: Output::Json,
            })
        );
    }

    #[test]
    fn parses_accounts_and_logout() {
        assert_eq!(
            [
                parse_provider_command(&arg(&["accounts"])),
                parse_provider_command(&arg(&["accounts", "--json"])),
                parse_provider_command(&arg(&["logout", "openai"])),
                parse_provider_command(&arg(&["logout", "openai", "2"])),
                parse_provider_command(&arg(&["logout", "anthropic", "a@x.com", "[org-1]"])),
                parse_provider_command(&arg(&["accounts", "openai"])),
                parse_provider_command(&arg(&["logout"])),
                parse_provider_command(&arg(&["logout", "openai", "--json"])),
            ],
            [
                Ok(ProviderCommand::Accounts {
                    output: Output::Table,
                }),
                Ok(ProviderCommand::Accounts {
                    output: Output::Json,
                }),
                Ok(ProviderCommand::Logout {
                    provider: "openai".to_string(),
                    account: None,
                }),
                Ok(ProviderCommand::Logout {
                    provider: "openai".to_string(),
                    account: Some("2".to_string()),
                }),
                Ok(ProviderCommand::Logout {
                    provider: "anthropic".to_string(),
                    account: Some("a@x.com [org-1]".to_string()),
                }),
                Err(ProviderUsageError::AccountsUsage),
                Err(ProviderUsageError::LogoutUsage),
                Err(ProviderUsageError::LogoutUsage),
            ]
        );
    }

    #[test]
    fn rejects_missing_and_unknown_arguments() {
        assert_eq!(
            parse_provider_command(&arg(&[])),
            Err(ProviderUsageError::Missing)
        );
        assert_eq!(
            parse_provider_command(&arg(&["model"])).map_err(|error| error.to_string()),
            Err("Unknown provider command: model (did you mean \"models\"?)".to_string())
        );
        assert_eq!(
            parse_provider_command(&arg(&["models"])).map_err(|error| error.to_string()),
            Err("Usage: eukhe provider models <provider> [--json]".to_string())
        );
        assert_eq!(
            parse_provider_command(&arg(&["caps", "a", "b"])).map_err(|error| error.to_string()),
            Err("Usage: eukhe provider caps [<provider>] [--json]".to_string())
        );
        assert_eq!(
            parse_provider_command(&arg(&["caps", "--yaml"])),
            Err(ProviderUsageError::UnknownOption("--yaml".to_string()))
        );
    }

    fn entry(capability: Capability, support: Support) -> CapabilitySupport {
        CapabilitySupport {
            capability,
            support,
        }
    }

    #[test]
    fn renders_a_capability_table() {
        let rows = vec![
            Capabilities {
                provider: "llama-cpp".to_string(),
                api: "openai-completions".to_string(),
                base_url: "http://127.0.0.1:8080/v1".to_string(),
                entries: vec![
                    entry(
                        Capability::CountTokens,
                        Support::Native {
                            dialect: Dialect::LlamaCpp,
                            endpoint: "POST /apply-template, POST /tokenize",
                        },
                    ),
                    entry(
                        Capability::ListModels,
                        Support::Native {
                            dialect: Dialect::OpenAi,
                            endpoint: "GET /v1/models",
                        },
                    ),
                    entry(Capability::GenerateImage, Support::Unsupported),
                ],
            },
            Capabilities {
                provider: "x".to_string(),
                api: "anthropic-messages".to_string(),
                base_url: "https://x.test".to_string(),
                entries: vec![entry(Capability::Usage, Support::Unsupported)],
            },
        ];
        assert_eq!(
            render_capabilities(&rows),
            "llama-cpp  openai-completions  http://127.0.0.1:8080/v1\n\
             \x20 count_tokens    llama-cpp: POST /apply-template, POST /tokenize\n\
             \x20 list_models     openai: GET /v1/models\n\
             \x20 generate_image  unsupported\n\
             \n\
             x  anthropic-messages  https://x.test\n\
             \x20 usage           unsupported"
        );
    }

    #[test]
    fn renders_a_model_listing() {
        let listed = vec![
            ListedModel {
                id: "claude-sonnet-4-5".to_string(),
                name: Some("Claude Sonnet 4.5".to_string()),
                context_window: Some(200_000),
                max_output_tokens: Some(64_000),
                ..ListedModel::default()
            },
            ListedModel {
                id: "qwen3-8b".to_string(),
                name: None,
                context_window: None,
                max_output_tokens: None,
                ..ListedModel::default()
            },
        ];
        assert_eq!(
            render_listing(&listed),
            "id                 name               context  max-out\n\
             claude-sonnet-4-5  Claude Sonnet 4.5  200K     64K\n\
             qwen3-8b           -                  -        -"
        );
    }
}
