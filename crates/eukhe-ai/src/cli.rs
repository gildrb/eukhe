//! The OAuth login developer CLI. Port of `cli.ts` as a library function:
//! [`run_cli`] runs a command against injected input/output streams and an
//! auth file; [`cli_main`] is the process entry point (stdin/stdout,
//! `auth.json` in the working directory, `Error: …` and exit code 1 on
//! failure) for a binary that wants it.

use std::fmt;
use std::io::Write;
use std::path::Path;
use std::process::ExitCode;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{AbortController, AbortSignal};
use eukhe_types::pi_ai::{JsonObject, JsonValue};
use futures::future::BoxFuture;
use tokio::io::{AsyncBufRead, AsyncBufReadExt};

use crate::auth::{
    AuthEvent, AuthInteraction, AuthPrompt, AuthPromptKind, LoginOptions, ProviderAuthInteraction,
};
use crate::models::Provider;
use crate::providers::all::builtin_providers;
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::js::json_stringify_pretty;

const AUTH_FILE: &str = "auth.json";

/// Line input shared by prompts.
type Input = Arc<tokio::sync::Mutex<Box<dyn AsyncBufRead + Unpin + Send>>>;
/// Console output shared by prompts and notifications.
type Output = Arc<Mutex<Box<dyn Write + Send>>>;

fn providers() -> Vec<Provider> {
    builtin_providers()
        .into_iter()
        .filter(|provider| provider.auth.oauth.is_some())
        .collect()
}

fn write_out(output: &Output, text: &str) -> Result<(), Thrown> {
    let mut output = output.lock().unwrap_or_else(PoisonError::into_inner);
    output
        .write_all(text.as_bytes())
        .and_then(|()| output.flush())
        .map_err(|error| ErrorObject::new(error.to_string()).thrown())
}

/// `console.log`.
fn log(output: &Output, text: &str) -> Result<(), Thrown> {
    write_out(output, &format!("{text}\n"))
}

/// `rl.question`: prints the question and reads one line (without the
/// line terminator; end of input reads as empty).
async fn prompt(input: &Input, output: &Output, question: &str) -> Result<String, Thrown> {
    write_out(output, question)?;
    let mut line = String::new();
    input
        .lock()
        .await
        .read_line(&mut line)
        .await
        .map_err(|error| ErrorObject::new(error.to_string()).thrown())?;
    let trimmed = line.strip_suffix('\n').unwrap_or(&line);
    Ok(trimmed.strip_suffix('\r').unwrap_or(trimmed).to_owned())
}

/// JS `Number.parseInt(value, 10)`.
fn parse_int(value: &str) -> Option<i64> {
    let trimmed = value.trim_start();
    let (negative, digits) = match trimmed.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, trimmed.strip_prefix('+').unwrap_or(trimmed)),
    };
    let end = digits
        .find(|character: char| !character.is_ascii_digit())
        .unwrap_or(digits.len());
    let number: i64 = digits[..end].parse().ok()?;
    Some(if negative { -number } else { number })
}

/// The entry at 1-based `answer`, if any.
fn choose<T>(items: &[T], answer: &str) -> Option<usize> {
    let index = parse_int(answer)? - 1;
    usize::try_from(index)
        .ok()
        .filter(|index| *index < items.len())
}

async fn answer_prompt(
    input: &Input,
    output: &Output,
    auth_prompt: AuthPrompt,
) -> Result<String, Thrown> {
    match auth_prompt.kind {
        AuthPromptKind::Select { message, options } => {
            log(output, &format!("\n{message}"))?;
            for (index, option) in options.iter().enumerate() {
                log(output, &format!("  {}. {}", index + 1, option.label))?;
            }
            let answer = prompt(
                input,
                output,
                &format!("Enter number (1-{}): ", options.len()),
            )
            .await?;
            let selected = choose(&options, &answer)
                .ok_or_else(|| ErrorObject::new("Invalid selection").thrown())?;
            Ok(options[selected].id.clone())
        }
        AuthPromptKind::Text {
            message,
            placeholder,
        }
        | AuthPromptKind::Secret {
            message,
            placeholder,
        }
        | AuthPromptKind::ManualCode {
            message,
            placeholder,
        } => {
            let hint = placeholder
                .filter(|placeholder| !placeholder.is_empty())
                .map(|placeholder| format!(" ({placeholder})"))
                .unwrap_or_default();
            prompt(input, output, &format!("{message}{hint}: ")).await
        }
    }
}

struct CliInteraction {
    input: Input,
    output: Output,
    signal: AbortSignal,
}

impl AuthInteraction for CliInteraction {
    fn signal(&self) -> Option<AbortSignal> {
        Some(self.signal.clone())
    }

    fn prompt(&self, prompt: AuthPrompt) -> BoxFuture<'_, Result<String, Thrown>> {
        Box::pin(answer_prompt(&self.input, &self.output, prompt))
    }

    fn notify(&self, event: AuthEvent) {
        let text = match event {
            AuthEvent::AuthUrl { url, instructions } => {
                let mut text = format!("\nOpen this URL in your browser:\n{url}");
                if let Some(instructions) =
                    instructions.filter(|instructions| !instructions.is_empty())
                {
                    text.push('\n');
                    text.push_str(&instructions);
                }
                text
            }
            AuthEvent::DeviceCode {
                user_code,
                verification_uri,
                ..
            } => format!(
                "\nOpen this URL in your browser:\n{verification_uri}\nEnter code: {user_code}"
            ),
            AuthEvent::Info { message, .. } | AuthEvent::Progress { message } => message,
        };
        // Notifications have no failure channel; a closed console drops them.
        let _ = log(&self.output, &text);
    }
}

impl fmt::Debug for CliInteraction {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("CliInteraction")
            .finish_non_exhaustive()
    }
}

fn load_auth(auth_file: &Path) -> JsonObject {
    std::fs::read_to_string(auth_file)
        .ok()
        .and_then(|text| serde_json::from_str::<JsonValue>(&text).ok())
        .and_then(|value| match value {
            JsonValue::Object(object) => Some(object),
            JsonValue::Null
            | JsonValue::Bool(_)
            | JsonValue::Number(_)
            | JsonValue::String(_)
            | JsonValue::Array(_) => None,
        })
        .unwrap_or_default()
}

fn save_auth(auth_file: &Path, auth: JsonObject) -> Result<(), Thrown> {
    std::fs::write(auth_file, json_stringify_pretty(&JsonValue::Object(auth)))
        .map_err(|error| ErrorObject::new(error.to_string()).thrown())
}

async fn login(
    providers: &[Provider],
    provider_id: &str,
    input: &Input,
    output: &Output,
    auth_file: &Path,
) -> Result<(), Thrown> {
    let provider = providers
        .iter()
        .find(|entry| entry.id == provider_id)
        .ok_or_else(|| ErrorObject::new(format!("Unknown provider: {provider_id}")).thrown())?;
    let oauth = provider
        .auth
        .oauth
        .clone()
        .ok_or_else(|| ErrorObject::new(format!("Unknown provider: {provider_id}")).thrown())?;
    let signal = AbortController::new().signal();
    let interaction = Arc::new(CliInteraction {
        input: Arc::clone(input),
        output: Arc::clone(output),
        signal: signal.clone(),
    });
    // This dev CLI does not persist an installation ID; apps should reuse one
    // across logins.
    let credential = oauth
        .login(
            ProviderAuthInteraction::new(interaction, signal),
            Some(LoginOptions {
                get_device_id: Some(Arc::new(|| uuid::Uuid::new_v4().to_string())),
                agent_name: None,
            }),
        )
        .await?;
    let mut auth = load_auth(auth_file);
    auth.insert(
        provider_id.to_owned(),
        serde_json::to_value(credential)
            .map_err(|error| ErrorObject::new(error.to_string()).thrown())?,
    );
    save_auth(auth_file, auth)?;
    log(
        output,
        &format!("\nCredentials saved to {}", auth_file.display()),
    )
}

fn pad_end(text: &str, width: usize) -> String {
    format!("{text:<width$}")
}

/// Runs one CLI invocation (`args` excludes the program name).
///
/// # Errors
///
/// Unknown commands or providers, invalid selections, login failures, and
/// I/O failures, with the TS messages.
pub async fn run_cli(
    args: &[String],
    input: Box<dyn AsyncBufRead + Unpin + Send>,
    output: Box<dyn Write + Send>,
    auth_file: &Path,
) -> Result<(), Thrown> {
    let input: Input = Arc::new(tokio::sync::Mutex::new(input));
    let output: Output = Arc::new(Mutex::new(output));
    let providers = providers();
    let command = args.first().map(String::as_str);
    match command {
        None | Some("help" | "--help" | "-h") => {
            let provider_list = providers
                .iter()
                .map(|provider| format!("  {} {}", pad_end(&provider.id, 20), provider.name))
                .collect::<Vec<_>>()
                .join("\n");
            log(
                &output,
                &format!(
                    "Usage: npx @earendil-works/pi-ai <command> [provider]\n\nCommands:\n  login [provider]  Login to an OAuth provider\n  list              List available providers\n\nProviders:\n{provider_list}"
                ),
            )
        }
        Some("list") => {
            for provider in &providers {
                log(
                    &output,
                    &format!("{} {}", pad_end(&provider.id, 20), provider.name),
                )?;
            }
            Ok(())
        }
        Some("login") => {
            let mut provider_id = args.get(1).cloned();
            if provider_id.is_none() {
                for (index, provider) in providers.iter().enumerate() {
                    log(&output, &format!("  {}. {}", index + 1, provider.name))?;
                }
                let answer = prompt(
                    &input,
                    &output,
                    &format!("Enter number (1-{}): ", providers.len()),
                )
                .await?;
                provider_id = choose(&providers, &answer).map(|index| providers[index].id.clone());
            }
            let provider_id = provider_id
                .filter(|id| !id.is_empty() && providers.iter().any(|provider| provider.id == *id))
                .ok_or_else(|| {
                    ErrorObject::new(format!(
                        "Unknown provider: {}",
                        args.get(1).map(String::as_str).unwrap_or_default()
                    ))
                    .thrown()
                })?;
            login(&providers, &provider_id, &input, &output, auth_file).await
        }
        Some(other) => Err(ErrorObject::new(format!("Unknown command: {other}")).thrown()),
    }
}

/// Process entry point: runs [`run_cli`] on the process arguments with
/// stdin/stdout and `auth.json`; prints `Error: <message>` to stderr and
/// exits 1 on failure.
pub async fn cli_main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let input = Box::new(tokio::io::BufReader::new(tokio::io::stdin()));
    let output = Box::new(std::io::stdout());
    match run_cli(&args, input, output, Path::new(AUTH_FILE)).await {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("Error: {error}");
            ExitCode::FAILURE
        }
    }
}
