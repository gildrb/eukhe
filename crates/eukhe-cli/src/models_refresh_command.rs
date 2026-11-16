//! `eukhe model refresh [<provider>...] [--json]` (also `eukhe models
//! refresh`): asks the providers' own model-listing endpoints for the
//! models they offer now and adds the ones the built-in catalog lacks to
//! the local overlay (`eukhe_core::models::refresh`). The one command that
//! fetches model lists; nothing fetches them on its own.

use std::io::IsTerminal;
use std::time::SystemTime;

use eukhe_core::models::refresh::{local_clock, refresh_models, report_lines, ProviderSelection};

/// How the command prints its report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Output {
    Lines,
    Json,
}

/// The parsed invocation.
#[derive(Debug, PartialEq, Eq)]
struct RefreshCommand {
    selection: ProviderSelection,
    output: Output,
}

/// Why the arguments do not parse.
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
enum RefreshUsageError {
    #[error("unknown option: {0}")]
    UnknownOption(String),
}

/// Parse the operands (providers) and `--json`.
fn parse_refresh_command(args: &[String]) -> Result<RefreshCommand, RefreshUsageError> {
    let mut output = Output::Lines;
    let mut providers = Vec::new();
    for arg in args {
        match arg.as_str() {
            "--json" => output = Output::Json,
            option if option.starts_with('-') => {
                return Err(RefreshUsageError::UnknownOption(option.to_owned()));
            }
            provider => providers.push(provider.to_owned()),
        }
    }
    let selection = if providers.is_empty() {
        ProviderSelection::SignedIn
    } else {
        ProviderSelection::Named(providers)
    };
    Ok(RefreshCommand { selection, output })
}

/// Run `model refresh`; returns the process exit code.
pub fn run_models_refresh_command(args: &[String]) -> i32 {
    let command = match parse_refresh_command(args) {
        Ok(command) => command,
        Err(error) => {
            eprintln!("Error: {error}");
            eprintln!(
                "Run \"{} help model refresh\" for usage.",
                crate::config::APP_NAME
            );
            return 2;
        }
    };
    let agent_dir = crate::config::get_agent_dir();
    let loaded = eukhe_core::durable::create_models(&agent_dir);
    if !loaded.diagnostics.is_empty() {
        eprintln!(
            "Warning: errors loading models.json:\n{}",
            loaded.diagnostics.join("\n")
        );
    }
    let models = loaded.models;
    // No task: any request it sends passes the daemon's budget account.
    eukhe_core::durable::budget::wrap_models_with_budget(
        &models,
        &eukhe_core::durable::budget::BudgetGate::daemon(&agent_dir),
    );
    let Ok(runtime) = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    else {
        eprintln!("Error: could not start the provider runtime.");
        return 1;
    };
    if command.output == Output::Lines && std::io::stderr().is_terminal() {
        eprintln!("Refreshing model lists...");
    }
    let refreshed = match runtime.block_on(refresh_models(
        &agent_dir,
        &models,
        &command.selection,
        SystemTime::now(),
    )) {
        Ok(refreshed) => refreshed,
        Err(error) => {
            eprintln!("Error: {error:#}");
            return 1;
        }
    };
    match command.output {
        Output::Json => match crate::json_out::print_json_document(&refreshed.report) {
            Ok(()) => 0,
            Err(error) => {
                eprintln!("Error: {error}");
                1
            }
        },
        Output::Lines => {
            let clock = local_clock(&refreshed.report.refreshed_at);
            for line in report_lines(&refreshed.report, &clock) {
                println!("{line}");
            }
            0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn arg(words: &[&str]) -> Vec<String> {
        words.iter().map(ToString::to_string).collect()
    }

    #[test]
    fn parses_providers_and_json() {
        assert_eq!(
            (
                parse_refresh_command(&arg(&[])),
                parse_refresh_command(&arg(&["openai-codex", "--json", "anthropic"])),
                parse_refresh_command(&arg(&["--yaml"])),
            ),
            (
                Ok(RefreshCommand {
                    selection: ProviderSelection::SignedIn,
                    output: Output::Lines,
                }),
                Ok(RefreshCommand {
                    selection: ProviderSelection::Named(vec![
                        "openai-codex".to_owned(),
                        "anthropic".to_owned(),
                    ]),
                    output: Output::Json,
                }),
                Err(RefreshUsageError::UnknownOption("--yaml".to_owned())),
            )
        );
    }

    #[test]
    fn models_is_the_model_command() {
        assert_eq!(
            (
                crate::public_command::with_command_alias(arg(&["models", "refresh"])),
                crate::public_command::with_command_alias(arg(&["help", "models", "refresh"])),
                crate::public_command::with_command_alias(arg(&["models-x"])),
                crate::public_command::with_command_alias(arg(&["tiny", "list"])),
            ),
            (
                arg(&["model", "refresh"]),
                arg(&["help", "model", "refresh"]),
                arg(&["models-x"]),
                arg(&["tiny-models", "list"]),
            )
        );
    }
}
