//! `chat`: the chat memory from the command line -- the view the agent sees,
//! its status, the browse page, and history imports. Reading never takes
//! ownership of the chat (a short-lived command must not run the
//! compactor); an import first makes sure the daemon runs, so its
//! always-on supervisor owns the chat and summarizes the imported history
//! in the background.

use std::path::PathBuf;

use crate::config::APP_NAME;

/// The parsed `chat` invocation.
#[derive(Debug, PartialEq, Eq)]
enum ChatCommand {
    View,
    Status { json: bool },
    Browse { out: Option<String> },
    ImportSessions { paths: Vec<String> },
}

/// Why the `chat` arguments do not parse.
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
enum ChatUsageError {
    /// No subcommand.
    #[error("Missing chat command.")]
    Missing,
    #[error(
        "Unknown chat command: {subcommand}{}",
        .suggestion.as_ref().map_or_else(String::new, |s| format!(" (did you mean \"{s}\"?)"))
    )]
    Unknown {
        subcommand: String,
        suggestion: Option<String>,
    },
    #[error("--out requires a file path")]
    OutWithoutPath,
    #[error("unknown option {0:?}")]
    UnknownOption(String),
    #[error("Usage: {app} chat view", app = APP_NAME)]
    ViewUsage,
    #[error("Usage: {app} chat status [--json]", app = APP_NAME)]
    StatusUsage,
    #[error("Usage: {app} chat browse [--out <path>]", app = APP_NAME)]
    BrowseUsage,
    #[error("Usage: {app} chat import sessions <path>...", app = APP_NAME)]
    ImportUsage,
}

/// Parse the subcommand and its flags.
fn parse_chat_command(args: &[String]) -> Result<ChatCommand, ChatUsageError> {
    let children: Vec<&str> = crate::command_registry::get_child_command_specs(&["chat"])
        .into_iter()
        .map(|spec| spec.path[spec.path.len() - 1])
        .collect();
    let Some(subcommand) = args.first() else {
        return Err(ChatUsageError::Missing);
    };
    if !children.contains(&subcommand.as_str()) {
        return Err(ChatUsageError::Unknown {
            subcommand: subcommand.clone(),
            suggestion: eukhe_bend::rules::slash::suggestion(subcommand, &children)
                .map(str::to_owned),
        });
    }
    let mut json = false;
    let mut out: Option<String> = None;
    let mut operands: Vec<String> = Vec::new();
    let mut rest = args[1..].iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--json" => json = true,
            "--out" => {
                let Some(value) = rest.next() else {
                    return Err(ChatUsageError::OutWithoutPath);
                };
                out = Some(value.clone());
            }
            other if other.starts_with('-') => {
                return Err(ChatUsageError::UnknownOption(other.to_owned()))
            }
            other => operands.push(other.to_string()),
        }
    }
    match subcommand.as_str() {
        "view" if operands.is_empty() && !json && out.is_none() => Ok(ChatCommand::View),
        "view" => Err(ChatUsageError::ViewUsage),
        "status" if operands.is_empty() && out.is_none() => Ok(ChatCommand::Status { json }),
        "status" => Err(ChatUsageError::StatusUsage),
        "browse" if operands.is_empty() && !json => Ok(ChatCommand::Browse { out }),
        "browse" => Err(ChatUsageError::BrowseUsage),
        "import" => {
            if json || out.is_some() {
                return Err(ChatUsageError::ImportUsage);
            }
            let mut operands = operands.into_iter();
            match operands.next().as_deref() {
                Some("sessions") => {
                    let paths: Vec<String> = operands.collect();
                    if paths.is_empty() {
                        return Err(ChatUsageError::ImportUsage);
                    }
                    Ok(ChatCommand::ImportSessions { paths })
                }
                _ => Err(ChatUsageError::ImportUsage),
            }
        }
        _ => Err(ChatUsageError::Missing),
    }
}

/// Run the `chat` command; returns the process exit code.
pub fn run_chat_command(args: &[String]) -> i32 {
    let command = match parse_chat_command(args) {
        Ok(command) => command,
        Err(error) => {
            eprintln!("Error: {error}");
            eprintln!("Run \"{} help chat\" for usage.", crate::config::APP_NAME);
            return 2;
        }
    };
    let Ok(runtime) = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
    else {
        eprintln!("Error: could not start the chat runtime.");
        return 1;
    };
    match runtime.block_on(run(command)) {
        Ok(()) => 0,
        Err(error) => {
            eprintln!("Error: {error:#}");
            1
        }
    }
}

async fn run(command: ChatCommand) -> anyhow::Result<()> {
    let agent_dir = crate::config::get_agent_dir();
    let dir = eukhe_core::memory::chat_dir(&agent_dir);
    match command {
        ChatCommand::View => {
            let view = eukhe_core::memory::read_view(&dir).await?;
            println!("{}", view.text);
            Ok(())
        }
        ChatCommand::Status { json } => {
            let view = eukhe_core::memory::read_view(&dir).await?;
            if json {
                let document = serde_json::json!({
                    "dir": dir,
                    "messages": view.messages,
                    "summaries": view.summaries,
                    "viewLines": view.view_lines,
                    "viewBytes": view.view_bytes,
                    "unsummarized": view.unsummarized,
                    "owner": view.live,
                });
                println!(
                    "{}",
                    crate::json_out::json_document(&document).map_err(anyhow::Error::msg)?
                );
            } else {
                println!("Chat:          {}", dir.display());
                println!("Messages:      {}", view.messages);
                println!("Summaries:     {}", view.summaries);
                println!(
                    "View:          {} lines, {} bytes",
                    view.view_lines, view.view_bytes
                );
                println!("Unsummarized:  {}", view.unsummarized);
                println!(
                    "Owner:         {}",
                    if view.live {
                        "running"
                    } else {
                        "none (the next session takes over)"
                    }
                );
            }
            Ok(())
        }
        ChatCommand::Browse { out } => {
            let out = out.map_or_else(
                || dir.join("browse.html"),
                |out| crate::config::expand_tilde_path(&out),
            );
            let summary = eukhe_core::memory::write_browse_page(&dir, &out).await?;
            println!(
                "Wrote {} ({} messages, {} summaries, view {} lines{})",
                out.display(),
                summary.messages,
                summary.nodes,
                summary.view_lines,
                if summary.live_view { ", live" } else { "" }
            );
            Ok(())
        }
        ChatCommand::ImportSessions { paths } => {
            let paths: Vec<PathBuf> = paths
                .iter()
                .map(|path| crate::config::expand_tilde_path(path))
                .collect();
            let memory = open_through_daemon(&agent_dir).await?;
            let report = eukhe_core::memory::import_sessions(&memory, &paths).await?;
            println!(
                "Imported {} messages from {} sessions ({} skipped)",
                report.count, report.sessions, report.skipped
            );
            Ok(())
        }
    }
}

/// Start the daemon when it is not running (its supervisor claims the chat
/// at boot), then open the chat: as the supervisor's client, or as the
/// owner when another process held the chat first.
async fn open_through_daemon(
    agent_dir: &std::path::Path,
) -> anyhow::Result<eukhe_core::memory::Memory> {
    let socket = crate::config::resolve_daemon_socket_path(None);
    let cwd = std::env::current_dir()?;
    let ready = crate::interactive_mode::ensure_daemon_running(
        &socket,
        &cwd,
        eukhe_tui::daemon_build::Caller::Interactive,
    )
    .await?;
    if let Some(notice) = ready.notice() {
        eprintln!("{notice}");
    }
    eukhe_core::memory::Memory::open(
        eukhe_core::memory::chat_dir(agent_dir),
        std::sync::Arc::new(eukhe_core::memory::SettingsSummarizer::in_process(
            agent_dir.to_path_buf(),
        )),
    )
    .await
}
