//! `eukhe provider`: the provider capability surface.
//!
//! `caps` prints what each provider's API offers besides chat streaming,
//! read from the quirks rulebook through `Models::provider_capabilities`; it
//! sends nothing. `models` asks the named provider's own model-listing
//! endpoint: the one subcommand that talks to the network, and only to the
//! provider the user configured. A provider without the operation fails
//! with a message, never a fallback.

use eukhe_ai::capabilities::{Capabilities, Capability, ListedModel, Support};
use eukhe_ai::models::{Models, ModelsCapabilityOptions};

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
}

/// Parse the subcommand and its flags; `Err` carries a usage hint (empty
/// for a missing subcommand).
fn parse_provider_command(args: &[String]) -> Result<ProviderCommand, String> {
    let children: Vec<&str> = crate::command_registry::get_child_command_specs(&["provider"])
        .into_iter()
        .map(|spec| spec.path[spec.path.len() - 1])
        .collect();
    let Some(subcommand) = args.first() else {
        return Err(String::new());
    };
    if !children.contains(&subcommand.as_str()) {
        let suggestion = eukhe_bend::rules::slash::suggestion(subcommand, &children);
        return Err(format!(
            "Unknown provider command: {subcommand}{}",
            suggestion.map_or_else(String::new, |s| format!(" (did you mean \"{s}\"?)"))
        ));
    }
    let mut output = Output::Table;
    let mut operands: Vec<String> = Vec::new();
    for arg in &args[1..] {
        match arg.as_str() {
            "--json" => output = Output::Json,
            other if other.starts_with('-') => {
                return Err(format!("unknown option {other:?}"));
            }
            other => operands.push(other.to_string()),
        }
    }
    match subcommand.as_str() {
        "caps" => {
            if operands.len() > 1 {
                return Err("Usage: eukhe provider caps [<provider>] [--json]".to_string());
            }
            Ok(ProviderCommand::Caps {
                selection: operands.pop().map_or(Selection::Every, Selection::Named),
                output,
            })
        }
        "models" => {
            if operands.len() != 1 {
                return Err("Usage: eukhe provider models <provider> [--json]".to_string());
            }
            Ok(ProviderCommand::Models {
                provider: operands.remove(0),
                output,
            })
        }
        _ => Err(String::new()),
    }
}

/// Run the `provider` command; returns the process exit code.
pub fn run_provider_command(args: &[String]) -> i32 {
    let command = match parse_provider_command(args) {
        Ok(command) => command,
        Err(empty_hint) if empty_hint.is_empty() => {
            eprintln!("Missing provider command.");
            eprintln!(
                "Run \"{} help provider\" for usage.",
                crate::config::APP_NAME
            );
            return 1;
        }
        Err(error) => {
            eprintln!("Error: {error}");
            eprintln!("Run `{} help provider` for usage.", crate::config::APP_NAME);
            return 1;
        }
    };
    let loaded = eukhe_core::durable::create_models(&crate::config::get_agent_dir());
    if !loaded.diagnostics.is_empty() {
        eprintln!(
            "Warning: errors loading models.json:\n{}",
            loaded.diagnostics.join("\n")
        );
    }
    let models = loaded.models;
    match command {
        ProviderCommand::Caps { selection, output } => run_caps(&models, &selection, output),
        ProviderCommand::Models { provider, output } => run_models(&models, &provider, output),
    }
}

/// The capability rows of the selected providers; every provider with
/// chat models is sorted by provider id. Sends nothing.
fn capability_rows(models: &Models, selection: &Selection) -> Result<Vec<Capabilities>, String> {
    match selection {
        Selection::Named(id) => {
            let rows = models.provider_capabilities(id);
            if rows.is_empty() {
                return Err(format!("Unknown provider: {id}"));
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
        eprintln!("Error: Unknown provider: {provider}");
        return 1;
    }
    let Some(model) = chat_models.into_iter().find(|model| {
        matches!(
            models.capabilities(model).support(Capability::ListModels),
            Support::Native { .. }
        )
    }) else {
        eprintln!("provider {provider} does not support list_models");
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
/// provider does not give, columns padded to their widest cell.
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

/// Print `value` as pretty JSON; returns the exit code.
fn print_json<T: serde::Serialize>(value: &T) -> i32 {
    match serde_json::to_string_pretty(value) {
        Ok(text) => {
            println!("{text}");
            0
        }
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
    fn rejects_missing_and_unknown_arguments() {
        assert_eq!(parse_provider_command(&arg(&[])), Err(String::new()));
        assert_eq!(
            parse_provider_command(&arg(&["model"])),
            Err("Unknown provider command: model (did you mean \"models\"?)".to_string())
        );
        assert_eq!(
            parse_provider_command(&arg(&["models"])),
            Err("Usage: eukhe provider models <provider> [--json]".to_string())
        );
        assert_eq!(
            parse_provider_command(&arg(&["caps", "a", "b"])),
            Err("Usage: eukhe provider caps [<provider>] [--json]".to_string())
        );
        assert_eq!(
            parse_provider_command(&arg(&["caps", "--yaml"])),
            Err("unknown option \"--yaml\"".to_string())
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
            },
            ListedModel {
                id: "qwen3-8b".to_string(),
                name: None,
                context_window: None,
                max_output_tokens: None,
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
