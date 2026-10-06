//! `chat`: the chat memory from the command line -- the view the agent sees,
//! its status, the browse page, and history imports. Reading never takes
//! ownership of the chat (a short-lived command must not run the
//! compactor); an import first makes sure the daemon runs, so its
//! always-on supervisor owns the chat and summarizes the imported history
//! in the background.

use std::path::PathBuf;

/// The parsed `chat` invocation.
#[derive(Debug, PartialEq, Eq)]
enum ChatCommand {
    View,
    Status { json: bool },
    Browse { out: Option<String> },
    ImportOptmem { dir: Option<String> },
    ImportSessions { paths: Vec<String> },
}

/// Parse the subcommand and its flags; `Err` carries a usage hint (empty
/// when the subcommand is missing).
fn parse_chat_command(args: &[String]) -> Result<ChatCommand, String> {
    let children: Vec<&str> = crate::command_registry::get_child_command_specs(&["chat"])
        .into_iter()
        .map(|spec| spec.path[spec.path.len() - 1])
        .collect();
    let Some(subcommand) = args.first() else {
        return Err(String::new());
    };
    if !children.contains(&subcommand.as_str()) {
        let suggestion = crate::command_registry::find_command_suggestion(subcommand, &children);
        return Err(format!(
            "Unknown chat command: {subcommand}{}",
            suggestion.map_or_else(String::new, |s| format!(" (did you mean \"{s}\"?)"))
        ));
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
                    return Err("--out requires a file path".to_string());
                };
                out = Some(value.clone());
            }
            other if other.starts_with('-') => return Err(format!("unknown option {other:?}")),
            other => operands.push(other.to_string()),
        }
    }
    let app = crate::config::APP_NAME;
    match subcommand.as_str() {
        "view" if operands.is_empty() && !json && out.is_none() => Ok(ChatCommand::View),
        "view" => Err(format!("Usage: {app} chat view")),
        "status" if operands.is_empty() && out.is_none() => Ok(ChatCommand::Status { json }),
        "status" => Err(format!("Usage: {app} chat status [--json]")),
        "browse" if operands.is_empty() && !json => Ok(ChatCommand::Browse { out }),
        "browse" => Err(format!("Usage: {app} chat browse [--out <path>]")),
        "import" => {
            let usage =
                format!("Usage: {app} chat import optmem [<memory-dir>] | {app} chat import sessions <path>...");
            if json || out.is_some() {
                return Err(usage);
            }
            let mut operands = operands.into_iter();
            match operands.next().as_deref() {
                Some("optmem") => {
                    let dir = operands.next();
                    if operands.next().is_some() {
                        return Err(usage);
                    }
                    Ok(ChatCommand::ImportOptmem { dir })
                }
                Some("sessions") => {
                    let paths: Vec<String> = operands.collect();
                    if paths.is_empty() {
                        return Err(usage);
                    }
                    Ok(ChatCommand::ImportSessions { paths })
                }
                _ => Err(usage),
            }
        }
        _ => Err(String::new()),
    }
}

/// Run the `chat` command; returns the process exit code.
pub fn run_chat_command(args: &[String]) -> i32 {
    let command = match parse_chat_command(args) {
        Ok(command) => command,
        Err(empty_hint) if empty_hint.is_empty() => {
            eprintln!("Missing chat command.");
            eprintln!("Run \"{} help chat\" for usage.", crate::config::APP_NAME);
            return 1;
        }
        Err(error) => {
            eprintln!("Error: {error}");
            return 1;
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
                println!(
                    "{}",
                    serde_json::json!({
                        "dir": dir,
                        "messages": view.messages,
                        "summaries": view.summaries,
                        "viewLines": view.view_lines,
                        "viewBytes": view.view_bytes,
                        "unsummarized": view.unsummarized,
                        "owner": view.live,
                    })
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
        ChatCommand::ImportOptmem { dir: memory_dir } => {
            let memory_dir = memory_dir.map_or_else(
                || {
                    std::env::var_os("MEMORY_DIR").map_or_else(
                        || {
                            eukhe_types::platform::home_dir()
                                .unwrap_or_default()
                                .join(".optmem")
                                .join("memory")
                        },
                        PathBuf::from,
                    )
                },
                |dir| crate::config::expand_tilde_path(&dir),
            );
            let memory = open_through_daemon(&agent_dir).await?;
            let report = eukhe_core::memory::import_optmem(&memory, &memory_dir).await?;
            println!(
                "Imported {} OptMem notes as messages {}",
                report.count,
                report.first.map_or_else(String::new, |first| format!(
                    "{first}..{}",
                    first + report.count.saturating_sub(1)
                ))
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
    let ready = crate::interactive_mode::ensure_daemon_running(&socket, &cwd).await?;
    if let Some(notice) = ready.notice() {
        eprintln!("{notice}");
    }
    eukhe_core::memory::Memory::open(
        eukhe_core::memory::chat_dir(agent_dir),
        std::sync::Arc::new(eukhe_core::memory::SettingsSummarizer::new(
            agent_dir.to_path_buf(),
        )),
    )
    .await
}
