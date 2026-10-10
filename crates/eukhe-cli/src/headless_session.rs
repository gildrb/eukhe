//! The headless (print/json/rpc) session assembly: the CLI session flags
//! select a durable session storage (`--no-session` memory, `--fork`,
//! `--resume`, `--continue`, else fresh), the runtime lease guards it, and
//! `eukhe_core::durable::open_session` opens it with the CLI model,
//! thinking, prompt, and chat-memory inputs. `EUKHE_FAUX_SCRIPT` (JSON
//! text; verification harness only, never set by the product) swaps the
//! model collection for the scripted faux provider.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_core::durable::{
    fork_session, most_recent_session_for_cwd, open_session, read_session_cwd, resolve_session,
    EukheSession, ForkPoint, ModelRequest, PromptConfig, ResolvedListing, SessionConfig,
    SessionLocation, SessionRole, SessionStorage, TurnWait, TurnWaitSink,
};
use eukhe_daemon::lease::SessionLease;
use eukhe_durable::harness::types::{AgentChange, FieldChange};
use eukhe_pi_ai::providers::faux_script::{create_faux_script_models, parse_faux_script};

use crate::mode::RunOptions;

/// One opened headless session and the runtime lease guarding its storage
/// (`None` for memory sessions, or when a fresh lease could not be taken).
pub(crate) struct HeadlessSession {
    pub session: Arc<EukheSession>,
    pub lease: Option<SessionLease>,
    pub session_id: String,
    pub cwd: PathBuf,
    /// The fork source, when the session was forked from another one.
    pub parent_session: Option<PathBuf>,
}

/// Which session to open.
pub(crate) enum HeadlessTarget {
    /// The CLI session flags (`--no-session` -> `--fork` -> `--resume` ->
    /// `--continue` -> fresh; TS `createSessionManager`'s order).
    Selected,
    /// A fresh session (the RPC `new_session` replacement), at `cwd` when
    /// given, else the CLI cwd.
    New { cwd: Option<PathBuf> },
    /// An existing session (a durable storage dir or a legacy `.jsonl`
    /// file); `reuse_lease` skips the open guard (the caller already holds
    /// the lease of this very session).
    Open {
        location: PathBuf,
        reuse_lease: bool,
    },
}

/// How the session's chat turn waits surface (print: a stderr notice; rpc:
/// a `chat_turn_wait` frame).
pub(crate) type TurnWaitHook = TurnWaitSink;

/// The print modes' turn-wait sink: a prompt queued behind another window's
/// turn on the shared chat says so on stderr (stdout stays the answer or
/// the JSON stream).
pub(crate) fn stderr_turn_wait() -> TurnWaitHook {
    Arc::new(|wait| match wait {
        TurnWait::Waiting => eprintln!("{}", eukhe_types::daemon::CHAT_TURN_WAIT_NOTICE),
        TurnWait::Cleared => {}
    })
}

/// The sessions directory (the `--session-dir` flag, else the agent dir's
/// `sessions`).
pub(crate) fn sessions_dir(options: &RunOptions) -> PathBuf {
    options
        .session
        .session_dir
        .clone()
        .unwrap_or_else(|| options.config.agent_dir.join("sessions"))
}

/// The selection a target resolves to before anything opens.
pub(crate) enum Selection {
    /// `--no-session`: memory storage.
    Memory,
    /// A fresh durable session at `cwd`.
    Fresh { cwd: PathBuf },
    /// An existing session.
    Open {
        location: SessionLocation,
        reuse_lease: bool,
        /// `--cwd` wins over the stored cwd.
        cwd_override: Option<PathBuf>,
    },
    /// Fork `source` into a fresh session at the CLI cwd.
    Fork { source: SessionLocation },
}

/// Open the session `target` selects.
///
/// # Errors
///
/// The selector, lease, fork, faux-script, or open failure, as the
/// `Error:` text the CLI prints.
pub(crate) async fn open_headless_session(
    options: &RunOptions,
    target: HeadlessTarget,
    turn_wait: Option<TurnWaitHook>,
    cx: &Context,
) -> Result<HeadlessSession, String> {
    let selection = match target {
        HeadlessTarget::Selected => select(options, cx).await?,
        HeadlessTarget::New { cwd } => Selection::Fresh {
            cwd: cwd.unwrap_or_else(|| options.config.cwd.clone()),
        },
        HeadlessTarget::Open {
            location,
            reuse_lease,
        } => Selection::Open {
            location: SessionLocation::from_path(location),
            reuse_lease,
            cwd_override: None,
        },
    };
    let sessions_dir = sessions_dir(options);
    let agent_dir = &options.config.agent_dir;
    match selection {
        Selection::Memory => {
            let session_id = new_session_id();
            let config = session_config(
                options,
                &options.config.cwd,
                &session_id,
                SessionStorage::Memory,
                turn_wait,
            )
            .await?;
            let session = open(config, cx).await?;
            Ok(HeadlessSession {
                session,
                lease: None,
                session_id,
                cwd: options.config.cwd.clone(),
                parent_session: None,
            })
        }
        Selection::Fresh { cwd } => {
            let session_id = new_session_id();
            let dir = sessions_dir.join(&session_id);
            let lease = lease_fresh(&dir, agent_dir);
            let config = session_config(options, &cwd, &session_id, jsonl(&dir), turn_wait).await?;
            let session = open(config, cx).await?;
            Ok(HeadlessSession {
                session,
                lease,
                session_id,
                cwd,
                parent_session: None,
            })
        }
        Selection::Fork { source } => {
            let cwd = options.config.cwd.clone();
            let (session_id, dir, lease) = fork_into_fresh(options, &source, &cwd, cx).await?;
            let config = session_config(options, &cwd, &session_id, jsonl(&dir), turn_wait).await?;
            let session = open(config, cx).await?;
            Ok(HeadlessSession {
                session,
                lease,
                session_id,
                cwd,
                parent_session: Some(source.path().to_path_buf()),
            })
        }
        Selection::Open {
            location,
            reuse_lease,
            cwd_override,
        } => {
            // A legacy `<id>.jsonl` opens as the sibling `<id>/` storage
            // (the daemon worker's rule too).
            let dir = location.storage_dir();
            let session_id = dir
                .file_name()
                .map(|name| name.to_string_lossy().into_owned())
                .unwrap_or_default();
            let cwd =
                stored_cwd(&location, &options.config.cwd, cwd_override.as_deref(), cx).await?;
            // A failed open's early return drops the lease (released).
            let lease = if reuse_lease {
                None
            } else {
                Some(session_open_guard(options.daemon_socket.as_deref(), &dir)?)
            };
            if let SessionLocation::Legacy(file) = &location {
                if !dir.exists() {
                    eukhe_core::durable::import_legacy_session(file, &dir, cx)
                        .await
                        .map_err(|error| {
                            format!(
                                "failed to import legacy session {}: {error}",
                                file.display()
                            )
                        })?;
                }
            }
            let config = session_config(options, &cwd, &session_id, jsonl(&dir), turn_wait).await?;
            let session = open(config, cx).await?;
            if cwd_override.is_some() {
                set_main_cwd(&session, &cwd, cx).await?;
            }
            apply_flag_model(options, &session, cx).await?;
            Ok(HeadlessSession {
                session,
                lease,
                session_id,
                cwd,
                parent_session: None,
            })
        }
    }
}

/// Fork `source` into a fresh session storage whose main conversation runs
/// at `cwd` (TS `forkFrom` into this project), leased before anything
/// writes it (the source is only read, never leased). Returns the new
/// session id, its storage dir, and the lease.
///
/// # Errors
///
/// An empty or invalid source, or the fork failure.
pub(crate) async fn fork_into_fresh(
    options: &RunOptions,
    source: &SessionLocation,
    cwd: &Path,
    cx: &Context,
) -> Result<(String, PathBuf, Option<SessionLease>), String> {
    if let SessionLocation::Legacy(file) = source {
        if eukhe_core::session::manager::read_session_header(file).is_none() {
            return Err(format!(
                "Cannot fork: source session file is empty or invalid: {}",
                file.display()
            ));
        }
    }
    let session_id = new_session_id();
    let dir = sessions_dir(options).join(&session_id);
    let lease = lease_fresh(&dir, &options.config.agent_dir);
    fork_session(source, ForkPoint::Latest, Some(cwd), &dir, cx)
        .await
        .map_err(|error| format!("{error:#}"))?;
    Ok((session_id, dir, lease))
}

/// The CLI flag selection (TS `createSessionManager`: noSession -> fork ->
/// resume -> continue -> create).
///
/// # Errors
///
/// The selector error (with the browse hint), or the different-project
/// refusal of `--resume`.
pub(crate) async fn select(options: &RunOptions, cx: &Context) -> Result<Selection, String> {
    if options.session.no_session {
        return Ok(Selection::Memory);
    }
    let cwd = &options.config.cwd;
    let sessions_dir = sessions_dir(options);
    // Every resolution shape forks -- a GLOBAL session is exactly what
    // --fork is for (another project's session copied into this cwd).
    if let Some(selector) = &options.session.fork {
        let expanded = crate::config::expand_tilde_path(selector);
        let selector = expanded.to_string_lossy();
        let resolved = resolve_session(&selector, cwd, &sessions_dir, cx)
            .await
            .map_err(|error| crate::print_runtime::render_selector_error(&error))?;
        let source = match resolved {
            ResolvedListing::Path(location) => location,
            ResolvedListing::Local(listing) | ResolvedListing::Global(listing) => listing.location,
        };
        return Ok(Selection::Fork { source });
    }
    let cwd_override = options.session.cwd_from_flag.then(|| cwd.clone());
    if let Some(selector) = &options.session.resume {
        let resolved = resolve_session(selector, cwd, &sessions_dir, cx)
            .await
            .map_err(|error| crate::print_runtime::render_selector_error(&error))?;
        return match resolved {
            ResolvedListing::Path(location) => Ok(Selection::Open {
                location: absolute_location(location)?,
                reuse_lease: false,
                cwd_override,
            }),
            ResolvedListing::Local(listing) => Ok(Selection::Open {
                location: absolute_location(listing.location)?,
                reuse_lease: false,
                cwd_override,
            }),
            // Headless modes have no fork prompt; mirror the TS non-TTY path.
            ResolvedListing::Global(listing) => Err(format!(
                "session {selector} belongs to a different project ({}). Pass --fork {selector} to use it here, or run from that project's directory.",
                listing.cwd
            )),
        };
    }
    if options.session.continue_recent {
        if let Some(listing) = most_recent_session_for_cwd(&sessions_dir, cwd, cx).await {
            return Ok(Selection::Open {
                location: absolute_location(listing.location)?,
                reuse_lease: false,
                cwd_override,
            });
        }
    }
    Ok(Selection::Fresh { cwd: cwd.clone() })
}

fn absolute_location(location: SessionLocation) -> Result<SessionLocation, String> {
    let absolute = |path: PathBuf| std::path::absolute(&path).map_err(|error| error.to_string());
    Ok(match location {
        SessionLocation::Durable(dir) => SessionLocation::Durable(absolute(dir)?),
        SessionLocation::Legacy(file) => SessionLocation::Legacy(absolute(file)?),
    })
}

/// The cwd an opened session runs in: the explicit `--cwd` override
/// (main.ts `explicitCwdOverride`), else the stored session cwd, else the
/// fallback. A session stored against a deleted directory must not
/// silently continue somewhere else (main.ts `getMissingSessionCwdIssue`).
pub(crate) async fn stored_cwd(
    location: &SessionLocation,
    fallback_cwd: &Path,
    explicit_cwd_override: Option<&Path>,
    cx: &Context,
) -> Result<PathBuf, String> {
    let session_cwd = match explicit_cwd_override {
        Some(cwd) => cwd.to_path_buf(),
        None => read_session_cwd(location, cx)
            .await
            .filter(|cwd| !cwd.is_empty())
            .map_or_else(|| fallback_cwd.to_path_buf(), PathBuf::from),
    };
    if !session_cwd.exists() {
        return Err(format!(
            "Stored session working directory does not exist: {}\nSession file: {}\nCurrent working directory: {}",
            session_cwd.display(),
            location.path().display(),
            fallback_cwd.display()
        ));
    }
    Ok(session_cwd)
}

fn new_session_id() -> String {
    uuid::Uuid::now_v7().to_string()
}

fn jsonl(dir: &Path) -> SessionStorage {
    SessionStorage::Jsonl {
        dir: dir.to_path_buf(),
        fsync: true,
    }
}

async fn open(config: SessionConfig, cx: &Context) -> Result<Arc<EukheSession>, String> {
    open_session(config, cx)
        .await
        .map(Arc::new)
        .map_err(|error| format!("{error:#}"))
}

/// The open inputs from the CLI flags: model and thinking (a new root's
/// agent), prompt inputs, chat memory, and the faux-script models.
async fn session_config(
    options: &RunOptions,
    cwd: &Path,
    session_id: &str,
    storage: SessionStorage,
    turn_wait: Option<TurnWaitHook>,
) -> Result<SessionConfig, String> {
    let config = &options.config;
    let mut session = SessionConfig::new(&config.agent_dir, cwd, session_id, storage);
    session.role = SessionRole {
        rlm_depth: 0,
        rlm_max_depth: eukhe_daemon::rlm_children::DEFAULT_RLM_MAX_DEPTH,
        parent: None,
    };
    session.thinking = config.thinking.map(thinking_level);
    session.prompt = PromptConfig {
        custom_system_prompt: config.system_prompt.clone(),
        append_system_prompt: (!config.append_system_prompt.is_empty())
            .then(|| config.append_system_prompt.join("\n\n")),
        additional_skill_paths: config
            .skills
            .iter()
            .map(|path| path.display().to_string())
            .collect(),
        additional_prompt_paths: config
            .prompt_templates
            .iter()
            .map(|path| path.display().to_string())
            .collect(),
        ..PromptConfig::default()
    };
    session.turn_wait = turn_wait;
    if let Ok(script) = std::env::var("EUKHE_FAUX_SCRIPT") {
        let script = parse_faux_script(&script)
            .map_err(|error| format!("invalid EUKHE_FAUX_SCRIPT: {error}"))?;
        session.model = Some(ModelRequest {
            provider: Some("faux".to_owned()),
            pattern: script.model.id.clone(),
        });
        let (models, _provider) = create_faux_script_models(script);
        session.models = Some(models);
        // The faux harness keeps the classic continuing conversation
        // (its scripts assert carried context; no chat memory offline).
    } else {
        session.model = flag_model(options);
        // The chat memory: this process owns it when no daemon (or
        // other process) does, else it is the owner's client.
        let memory = eukhe_core::memory::Memory::open(
            eukhe_core::memory::chat_dir(&config.agent_dir),
            Arc::new(eukhe_core::memory::SettingsSummarizer::new(
                config.agent_dir.clone(),
            )),
        )
        .await
        .map_err(|error| format!("cannot open the chat memory: {error:#}"))?;
        session.memory = Some(memory);
        // TS `createAgentSessionServices` builds every CLI session on a
        // manager whose settings closures re-read settings on each
        // resolution; auth construction blocks, so it runs off the
        // async runtime.
        let (cwd, agent_dir) = (cwd.to_path_buf(), config.agent_dir.clone());
        let manager = tokio::task::spawn_blocking(move || {
            crate::mcp_login::cli_mcp_manager(&cwd, &agent_dir)
        })
        .await
        .map_err(|error| format!("MCP manager construction failed: {error}"))?;
        session.mcp = Some(Arc::new(std::sync::Mutex::new(manager)));
    }
    Ok(session)
}

/// `--model` (with `--provider`) as a model request.
fn flag_model(options: &RunOptions) -> Option<ModelRequest> {
    options.config.model.as_ref().map(|pattern| ModelRequest {
        provider: options.config.provider.clone(),
        pattern: pattern.clone(),
    })
}

/// An existing session keeps its agent, except what the flags ask for:
/// `--model` / `--thinking` reconfigure the main conversation, and a main
/// conversation without a model (an imported legacy session that never
/// recorded one) gets the run's model (the faux script's, the flags', or
/// the settings default).
async fn apply_flag_model(
    options: &RunOptions,
    session: &EukheSession,
    cx: &Context,
) -> Result<(), String> {
    let main = session.main();
    let current = main
        .agent(cx)
        .await
        .map_err(|error| format!("{error:#}"))?
        .model;
    let flagged = options.config.model.is_some() || options.config.thinking.is_some();
    if !flagged && current.is_some() {
        return Ok(());
    }
    // `--thinking` alone keeps the session's model.
    let requested = match current {
        Some(model) if options.config.model.is_none() => Some(ModelRequest::from(model)),
        _ => match std::env::var("EUKHE_FAUX_SCRIPT") {
            Ok(script) => parse_faux_script(&script).ok().map(|script| ModelRequest {
                provider: Some("faux".to_owned()),
                pattern: script.model.id,
            }),
            Err(_) => flag_model(options),
        },
    };
    let deps = session.deps();
    let resolved = eukhe_core::durable::resolve_session_model(
        &deps.models,
        &deps.settings.manager(),
        requested.as_ref(),
        options.config.thinking.map(thinking_level),
        cx,
    )
    .await
    .map_err(|error| format!("{error:#}"))?;
    let Some(resolved) = resolved else {
        return Ok(());
    };
    main.configure(
        AgentChange {
            model: FieldChange::Set(resolved.model),
            thinking_level: FieldChange::Set(resolved.thinking),
            ..AgentChange::default()
        },
        cx,
    )
    .await
    .map_err(|error| format!("{error:#}"))
}

/// The CLI `--thinking` level in the pi-ai vocabulary.
fn thinking_level(
    level: eukhe_types::ai::ModelThinkingLevel,
) -> eukhe_types::pi_ai::ModelThinkingLevel {
    use eukhe_types::ai::ModelThinkingLevel as Cli;
    use eukhe_types::pi_ai::ModelThinkingLevel as Pi;
    match level {
        Cli::Off => Pi::Off,
        Cli::Minimal => Pi::Minimal,
        Cli::Low => Pi::Low,
        Cli::Medium => Pi::Medium,
        Cli::High => Pi::High,
        Cli::Xhigh => Pi::Xhigh,
        Cli::Max => Pi::Max,
    }
}

/// Point the main conversation's agent at `cwd`.
async fn set_main_cwd(session: &EukheSession, cwd: &Path, cx: &Context) -> Result<(), String> {
    session
        .main()
        .configure(
            AgentChange {
                cwd: FieldChange::Set(cwd.to_string_lossy().into_owned()),
                ..AgentChange::default()
            },
            cx,
        )
        .await
        .map_err(|error| format!("{error:#}"))
}

/// Lease a fresh storage before anything writes it. A fresh storage's lease
/// cannot be contended (its uuid is new); an acquire failure is
/// environmental (the lease directory), so the session proceeds with a
/// warning instead of failing startup.
fn lease_fresh(dir: &Path, agent_dir: &Path) -> Option<SessionLease> {
    match eukhe_daemon::lease::acquire_runtime_session_lease(dir, agent_dir) {
        Ok(lease) => Some(lease),
        Err(error) => {
            eprintln!("eukhe: could not lease the fresh session: {error:#}");
            None
        }
    }
}

/// Guard an in-process open of a persisted session: probe the daemon's live
/// roster (refuse a session a live daemon worker already hosts,
/// `SessionAlreadyActiveError`), then acquire the runtime lease. Returns the
/// HELD lease -- the caller owns its lifetime.
pub(crate) fn session_open_guard(
    socket_path: Option<&str>,
    session_path: &Path,
) -> Result<SessionLease, String> {
    let socket = crate::interactive_mode::resolve_socket_path(socket_path);
    if let Ok(mut client) = crate::daemon_client::DaemonClient::connect(&socket) {
        let list = client
            .request(eukhe_types::daemon::DaemonCommand::List {
                id: None,
                all: None,
                cwd: None,
                session_dir: None,
                include_client_owned: None,
                rest: serde_json::Map::default(),
            })
            .map_err(|error| format!("Could not check active sessions: {error:#}"))?;
        if list.success {
            let target = eukhe_daemon::lease::canonical_session_path(session_path);
            for row in list
                .data
                .and_then(|data| data.get("sessions").cloned())
                .and_then(|sessions| sessions.as_array().cloned())
                .unwrap_or_default()
            {
                let Some(file) = row.get("sessionFile").and_then(serde_json::Value::as_str) else {
                    continue;
                };
                if eukhe_daemon::lease::canonical_session_path(Path::new(file)) != target {
                    continue;
                }
                let active_session_id = row
                    .get("activeSessionId")
                    .or_else(|| row.get("id"))
                    .and_then(serde_json::Value::as_str)
                    .unwrap_or_default();
                let message = match eukhe_tui::session_open_error::holder_from_roster(
                    std::slice::from_ref(&row),
                    &target,
                ) {
                    Some(holder) => {
                        eukhe_tui::session_open_error::already_active_error(&holder, &target)
                    }
                    None => format!(
                        "Session is already active in {active_session_id}: {}",
                        target.display()
                    ),
                };
                return Err(message);
            }
        }
    }
    // The roster covers only this daemon's sessions; the runtime lease table
    // is the cross-process ownership record. Acquire (not probe) so no
    // window opens between the check and the open.
    let agent_dir = crate::config::get_agent_dir();
    match eukhe_daemon::lease::acquire_runtime_session_lease(session_path, &agent_dir) {
        Ok(lease) => Ok(lease),
        Err(error) => {
            let Some(active) =
                error.downcast_ref::<eukhe_daemon::lease::SessionAlreadyActiveError>()
            else {
                return Err(format!(
                    "could not verify the session file is not held: {error:#}"
                ));
            };
            Err(eukhe_daemon::hold_refusal::refusal_message(
                &eukhe_daemon::hold_refusal::HoldIdentity {
                    pid: active.holder_pid,
                    active_session_id: active.active_session_id.clone(),
                },
                Some(session_path),
            ))
        }
    }
}
