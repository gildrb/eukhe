//! The headless (print/json/rpc) session assembly: the CLI session flags
//! select a durable session storage (`--no-session` memory, `--fork`,
//! `--resume`, `--continue`, else fresh), the runtime lease guards it, and
//! `eukhe_core::durable::open_session` opens it with the CLI model,
//! thinking, prompt, and chat-memory inputs. `EUKHE_FAUX_SCRIPT` (JSON
//! text; verification harness only, never set by the product) swaps the
//! model collection for the scripted faux provider.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_ai::providers::faux_script::{
    create_faux_script_models, parse_faux_script, FauxScriptError,
};
use eukhe_chord::context::Context;
use eukhe_core::durable::{
    fork_session, most_recent_session_for_cwd, open_session, read_session_cwd, resolve_session,
    EukheSession, ForkError, ForkPoint, ImportError, ModelRequest, OpenError, PromptConfig,
    ResolvedListing, SessionConfig, SessionLocation, SessionRole, SessionStorage,
};
use eukhe_core::session::discovery::SessionSelectorError;
use eukhe_daemon::hold_refusal::{refusal_message, HoldIdentity};
use eukhe_daemon::job_notices::HeadlessWakes;
use eukhe_daemon::lease::{SessionAlreadyActiveError, SessionLease};
use eukhe_durable::harness::types::{AgentChange, FieldChange};
use eukhe_durable::session::SessionError;
use eukhe_tui::session_open_error::{already_active_error, SessionHolder};

use crate::mode::RunOptions;

/// Why a headless session did not open. The `Display` is the `Error:` text
/// the CLI prints (and the RPC replacement's wire error).
#[derive(Debug, thiserror::Error)]
pub(crate) enum HeadlessSessionError {
    /// A `--fork` / `--resume` selector matched no session or several
    /// (main.ts formatting: the message plus the browse hint).
    #[error(
        "{}.{}\nOpen eukhe and press left-arrow to browse sessions.",
        .0.message(),
        .0.suggestion().unwrap_or_default()
    )]
    Selector(#[source] SessionSelectorError),
    /// `--resume` named another project's session (headless modes have no
    /// fork prompt).
    #[error(
        "session {selector} belongs to a different project ({cwd}). Pass --fork {selector} to use it here, or run from that project's directory."
    )]
    OtherProject { selector: String, cwd: String },
    /// The selected session path has no absolute form.
    #[error("{0}")]
    AbsolutePath(#[source] std::io::Error),
    /// The session's stored working directory is gone (main.ts
    /// `getMissingSessionCwdIssue`).
    #[error(
        "Stored session working directory does not exist: {}\nSession file: {}\nCurrent working directory: {}",
        .session_cwd.display(),
        .session_file.display(),
        .fallback_cwd.display()
    )]
    MissingCwd {
        session_cwd: PathBuf,
        session_file: PathBuf,
        fallback_cwd: PathBuf,
    },
    #[error("Cannot fork: source session file is not a regular file: {}", .0.display())]
    ForkSourceNotRegular(PathBuf),
    #[error("Cannot fork: source session file is empty or invalid: {}", .0.display())]
    ForkSourceInvalid(PathBuf),
    #[error("{0:#}")]
    Fork(#[source] ForkError),
    /// A fresh storage's lease failed (environmental: its uuid is new).
    #[error("could not lease the fresh session {}: {source:#}", .dir.display())]
    FreshLease {
        dir: PathBuf,
        #[source]
        source: anyhow::Error,
    },
    #[error("failed to import legacy session {}: {source}", .file.display())]
    ImportLegacy {
        file: PathBuf,
        #[source]
        source: ImportError,
    },
    #[error("{0:#}")]
    Open(#[source] OpenError),
    #[error("invalid EUKHE_FAUX_SCRIPT: {0}")]
    FauxScript(#[source] FauxScriptError),
    #[error("cannot open the chat memory: {0:#}")]
    ChatMemory(#[source] anyhow::Error),
    #[error("MCP manager construction failed: {0}")]
    McpManager(#[source] tokio::task::JoinError),
    /// The `--budget-*` limits did not become the session's budget.
    #[error("cannot set the session's budget: {0}")]
    Budget(#[source] eukhe_core::durable::budget::BudgetError),
    #[error("cannot set the session's budget: {0}")]
    BudgetTask(#[source] tokio::task::JoinError),
    /// Reading or reconfiguring the main conversation's agent failed.
    #[error("{0:#}")]
    Agent(#[source] SessionError),
    #[error("{0:#}")]
    Model(#[source] eukhe_core::durable::ModelsError),
    /// The daemon roster probe failed.
    #[error("Could not check active sessions: {0:#}")]
    ActiveSessionsCheck(#[source] anyhow::Error),
    /// A live daemon session hosts the session (its roster row).
    #[error("{}", already_active_error(.holder, .session_path))]
    HeldByDaemonSession {
        holder: SessionHolder,
        session_path: PathBuf,
    },
    /// A live daemon row hosts the session but names no holder.
    #[error("Session is already active in {active_session_id}: {}", .session_path.display())]
    ListedActive {
        active_session_id: String,
        session_path: PathBuf,
    },
    /// Another live process holds the session's runtime lease.
    #[error("{}", hold_refusal(.source, .session_path))]
    Held {
        #[source]
        source: SessionAlreadyActiveError,
        session_path: PathBuf,
    },
    #[error("could not verify the session file is not held: {0:#}")]
    LeaseCheck(#[source] anyhow::Error),
}

/// The co-existence refusal for a session another process leases.
fn hold_refusal(active: &SessionAlreadyActiveError, session_path: &Path) -> String {
    refusal_message(
        &HoldIdentity {
            pid: active.holder_pid,
            active_session_id: active.active_session_id.clone(),
        },
        Some(session_path),
    )
}

/// One opened headless session and the runtime lease guarding its storage
/// (`None` for memory sessions and for an open that reuses the caller's
/// lease).
pub(crate) struct HeadlessSession {
    pub session: Arc<EukheSession>,
    pub lease: Option<SessionLease>,
    pub session_id: String,
    pub cwd: PathBuf,
    /// The fork source, when the session was forked from another one.
    pub parent_session: Option<PathBuf>,
    /// The session's job-settled wake (its in-flight notices count toward
    /// quiescence).
    pub wakes: HeadlessWakes,
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
    cx: &Context,
) -> Result<HeadlessSession, HeadlessSessionError> {
    // The `--budget-*` limits are for the session the command line names
    // or starts; a session an RPC client switches to keeps its own.
    let budget = match &target {
        HeadlessTarget::Selected | HeadlessTarget::New { .. } => options.config.budget,
        HeadlessTarget::Open { .. } => None,
    };
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
    let opened = match selection {
        Selection::Memory => {
            let session_id = new_session_id();
            let (session, wakes) = open(
                options,
                &options.config.cwd,
                &session_id,
                SessionStorage::Memory,
                cx,
            )
            .await?;
            HeadlessSession {
                session,
                lease: None,
                session_id,
                cwd: options.config.cwd.clone(),
                parent_session: None,
                wakes,
            }
        }
        Selection::Fresh { cwd } => {
            let session_id = new_session_id();
            let dir = sessions_dir.join(&session_id);
            let lease = lease_fresh(&dir, agent_dir)?;
            let (session, wakes) = open(options, &cwd, &session_id, jsonl(&dir), cx).await?;
            HeadlessSession {
                session,
                lease: Some(lease),
                session_id,
                cwd,
                parent_session: None,
                wakes,
            }
        }
        Selection::Fork { source } => {
            let cwd = options.config.cwd.clone();
            let (session_id, dir, lease) = fork_into_fresh(options, &source, &cwd, cx).await?;
            let (session, wakes) = open(options, &cwd, &session_id, jsonl(&dir), cx).await?;
            HeadlessSession {
                session,
                lease: Some(lease),
                session_id,
                cwd,
                parent_session: Some(source.path().to_path_buf()),
                wakes,
            }
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
                .map_or_default(|name| name.to_string_lossy().into_owned());
            let cwd =
                stored_cwd(&location, &options.config.cwd, cwd_override.as_deref(), cx).await?;
            // A failed open's early return drops the lease (released).
            let lease = if reuse_lease {
                None
            } else {
                Some(session_open_guard(options.daemon_socket.as_deref(), &dir).await?)
            };
            if let SessionLocation::Legacy(file) = &location {
                if !dir.exists() {
                    eukhe_core::durable::import_legacy_session(file, &dir, cx)
                        .await
                        .map_err(|source| HeadlessSessionError::ImportLegacy {
                            file: file.clone(),
                            source,
                        })?;
                }
            }
            let (session, wakes) = open(options, &cwd, &session_id, jsonl(&dir), cx).await?;
            if cwd_override.is_some() {
                set_main_cwd(&session, &cwd, cx).await?;
            }
            apply_flag_model(options, &session, cx).await?;
            HeadlessSession {
                session,
                lease,
                session_id,
                cwd,
                parent_session: None,
                wakes,
            }
        }
    };
    if let Some(limits) = budget {
        let gate = opened.session.budget();
        let kept = tokio::task::spawn_blocking(move || match gate.report() {
            Some(report) => Ok(Some(report)),
            None => gate.set(limits).map(|_| None),
        })
        .await
        .map_err(HeadlessSessionError::BudgetTask)?
        .map_err(HeadlessSessionError::Budget)?;
        // A session that has a budget keeps it: the flags change nothing,
        // and the run says so.
        if let Some(report) = kept {
            eprintln!(
                "eukhe: this session already has a budget, the --budget flags change nothing ({})",
                eukhe_tui::budget_text::report_detail(
                    &report,
                    eukhe_tui::budget_text::now_ms(),
                    " · "
                )
            );
        }
    }
    Ok(opened)
}

/// Fork `source` into a fresh session storage whose main conversation runs
/// at `cwd` (TS `forkFrom` into this project), leased before anything
/// writes it (the source is only read, never leased). Returns the new
/// session id, its storage dir, and the lease.
///
/// # Errors
///
/// An empty or invalid source, the fresh lease failure, or the fork
/// failure.
pub(crate) async fn fork_into_fresh(
    options: &RunOptions,
    source: &SessionLocation,
    cwd: &Path,
    cx: &Context,
) -> Result<(String, PathBuf, SessionLease), HeadlessSessionError> {
    if let SessionLocation::Legacy(file) = source {
        // A FIFO (or any other non-regular file) blocks the header read
        // forever; a missing file falls through to the empty-or-invalid
        // error below.
        let non_regular = tokio::fs::metadata(file)
            .await
            .is_ok_and(|metadata| !metadata.is_file());
        if non_regular {
            return Err(HeadlessSessionError::ForkSourceNotRegular(file.clone()));
        }
        if eukhe_core::session::manager::read_session_header(file).is_none() {
            return Err(HeadlessSessionError::ForkSourceInvalid(file.clone()));
        }
    }
    let session_id = new_session_id();
    let dir = sessions_dir(options).join(&session_id);
    let lease = lease_fresh(&dir, &options.config.agent_dir)?;
    fork_session(source, ForkPoint::Latest, Some(cwd), &dir, cx)
        .await
        .map_err(HeadlessSessionError::Fork)?;
    Ok((session_id, dir, lease))
}

/// The session a `--fork <selector>` names (a path, a local or a global
/// session id prefix; a leading `~` expands against the home dir). Every
/// resolution shape forks -- a GLOBAL session is exactly what `--fork` is
/// for (another project's session copied into this cwd).
///
/// # Errors
///
/// The selector error, with the browse hint.
pub(crate) async fn resolve_fork_source(
    options: &RunOptions,
    selector: &str,
    cx: &Context,
) -> Result<SessionLocation, HeadlessSessionError> {
    let expanded = crate::config::expand_tilde_path(selector);
    let selector = expanded.to_string_lossy();
    let resolved = resolve_session(&selector, &options.config.cwd, &sessions_dir(options), cx)
        .await
        .map_err(HeadlessSessionError::Selector)?;
    Ok(match resolved {
        ResolvedListing::Path(location) => location,
        ResolvedListing::Local(listing) | ResolvedListing::Global(listing) => listing.location,
    })
}

/// The CLI flag selection (TS `createSessionManager`: noSession -> fork ->
/// resume -> continue -> create).
///
/// # Errors
///
/// The selector error (with the browse hint), or the different-project
/// refusal of `--resume`.
pub(crate) async fn select(
    options: &RunOptions,
    cx: &Context,
) -> Result<Selection, HeadlessSessionError> {
    if options.session.no_session {
        return Ok(Selection::Memory);
    }
    let cwd = &options.config.cwd;
    let sessions_dir = sessions_dir(options);
    // Every resolution shape forks -- a GLOBAL session is exactly what
    // --fork is for (another project's session copied into this cwd).
    if let Some(selector) = &options.session.fork {
        let source = resolve_fork_source(options, selector, cx).await?;
        return Ok(Selection::Fork { source });
    }
    let cwd_override = options.session.cwd_from_flag.then(|| cwd.clone());
    if let Some(selector) = &options.session.resume {
        let resolved = resolve_session(selector, cwd, &sessions_dir, cx)
            .await
            .map_err(HeadlessSessionError::Selector)?;
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
            ResolvedListing::Global(listing) => Err(HeadlessSessionError::OtherProject {
                selector: selector.clone(),
                cwd: listing.cwd,
            }),
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

fn absolute_location(location: SessionLocation) -> Result<SessionLocation, HeadlessSessionError> {
    let absolute =
        |path: PathBuf| std::path::absolute(path).map_err(HeadlessSessionError::AbsolutePath);
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
) -> Result<PathBuf, HeadlessSessionError> {
    let session_cwd = match explicit_cwd_override {
        Some(cwd) => cwd.to_path_buf(),
        None => read_session_cwd(location, cx)
            .await
            .filter(|cwd| !cwd.is_empty())
            .map_or_else(|| fallback_cwd.to_path_buf(), PathBuf::from),
    };
    if !session_cwd.exists() {
        return Err(HeadlessSessionError::MissingCwd {
            session_cwd,
            session_file: location.path().to_path_buf(),
            fallback_cwd: fallback_cwd.to_path_buf(),
        });
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

/// Open a session with the CLI inputs ([`session_config`]), its
/// job-settled wake, and its subagent runtime, like a daemon worker's: a
/// settled background job or kernel command, or a child's report, wakes
/// the session into its next turn. Children run as daemon child sessions
/// ([`crate::headless_children`]; the supervisor starts on the first
/// spawn).
async fn open(
    options: &RunOptions,
    cwd: &Path,
    session_id: &str,
    storage: SessionStorage,
    cx: &Context,
) -> Result<(Arc<EukheSession>, HeadlessWakes), HeadlessSessionError> {
    let session_file = match &storage {
        SessionStorage::Jsonl { dir, .. } => Some(dir.clone()),
        SessionStorage::Memory => None,
    };
    let mut config = session_config(options, cwd, session_id, storage).await?;
    let children = crate::headless_children::HeadlessChildren::new(
        options,
        session_id,
        cwd,
        session_file.as_deref(),
        config.role.rlm_depth,
        config.role.rlm_max_depth,
    );
    config.children = Some(children.host());
    children.register_agent_messaging(&mut config);
    let wakes = HeadlessWakes::default();
    wakes.wire(&mut config);
    let session = open_session(config, cx)
        .await
        .map(Arc::new)
        .map_err(HeadlessSessionError::Open)?;
    wakes.bind(&session);
    children.bind(&session);
    Ok((session, wakes))
}

/// The open inputs from the CLI flags: model and thinking (a new root's
/// agent), prompt inputs, chat memory, and the faux-script models.
async fn session_config(
    options: &RunOptions,
    cwd: &Path,
    session_id: &str,
    storage: SessionStorage,
) -> Result<SessionConfig, HeadlessSessionError> {
    let config = &options.config;
    let mut session = SessionConfig::new(&config.agent_dir, cwd, session_id, storage);
    session.role = SessionRole {
        rlm_depth: 0,
        rlm_max_depth: eukhe_daemon::rlm_children::DEFAULT_RLM_MAX_DEPTH,
        parent: None,
        worker: false,
    };
    session.thinking = config.thinking.map(thinking_level);
    session.host = options.app_mode.session_host();
    session.prompt = PromptConfig {
        custom_system_prompt: config.system_prompt.clone(),
        append_system_prompt: config.append_system_prompt.clone(),
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
        no_skills: config.no_skills,
        no_prompt_templates: config.no_prompt_templates,
        no_context_files: config.no_context_files,
        ..PromptConfig::default()
    };
    if let Ok(script) = std::env::var("EUKHE_FAUX_SCRIPT") {
        let script = parse_faux_script(&script).map_err(HeadlessSessionError::FauxScript)?;
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
        // The chat memory (`memory.chat`, on by default): the session's own
        // chat, which this process owns when no daemon (or other process)
        // does, else it is the owner's client.
        let chat_memory =
            eukhe_core::settings::SettingsManager::create(cwd, &config.agent_dir).get_memory_chat();
        if chat_memory {
            let memory = eukhe_core::memory::Memory::open(
                eukhe_core::memory::session_chat_dir(&config.agent_dir, session_id),
                Arc::new(
                    eukhe_core::memory::SettingsSummarizer::in_process(config.agent_dir.clone())
                        .for_session(session_id),
                ),
            )
            .await
            .map_err(HeadlessSessionError::ChatMemory)?;
            session.memory = Some(memory);
        }
        // TS `createAgentSessionServices` builds every CLI session on a
        // manager whose settings closures re-read settings on each
        // resolution; auth construction blocks, so it runs off the
        // async runtime.
        let (cwd, agent_dir) = (cwd.to_path_buf(), config.agent_dir.clone());
        let manager = tokio::task::spawn_blocking(move || {
            crate::mcp_login::cli_mcp_manager(&cwd, &agent_dir)
        })
        .await
        .map_err(HeadlessSessionError::McpManager)?;
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
) -> Result<(), HeadlessSessionError> {
    let main = session.main();
    let current = main
        .agent(cx)
        .await
        .map_err(HeadlessSessionError::Agent)?
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
    .map_err(HeadlessSessionError::Model)?;
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
    .map_err(HeadlessSessionError::Agent)
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
async fn set_main_cwd(
    session: &EukheSession,
    cwd: &Path,
    cx: &Context,
) -> Result<(), HeadlessSessionError> {
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
        .map_err(HeadlessSessionError::Agent)
}

/// Lease a fresh storage before anything writes it. A fresh storage's lease
/// cannot be contended (its uuid is new), so an acquire failure is
/// environmental (the lease directory); the session fails closed rather
/// than run unguarded.
fn lease_fresh(dir: &Path, agent_dir: &Path) -> Result<SessionLease, HeadlessSessionError> {
    eukhe_daemon::lease::acquire_runtime_session_lease(dir, agent_dir).map_err(|source| {
        HeadlessSessionError::FreshLease {
            dir: dir.to_path_buf(),
            source,
        }
    })
}

/// Guard an in-process open of a persisted session: probe the daemon's live
/// roster (refuse a session a live daemon worker already hosts,
/// `SessionAlreadyActiveError`), then acquire the runtime lease. Returns the
/// HELD lease -- the caller owns its lifetime.
pub(crate) async fn session_open_guard(
    socket_path: Option<&str>,
    session_path: &Path,
) -> Result<SessionLease, HeadlessSessionError> {
    let socket = crate::interactive_mode::resolve_socket_path(socket_path);
    let connection = match eukhe_client::daemon_client::DaemonClient::connect_probe(
        &socket,
        crate::daemon_command::HELLO_TIMEOUT_MS,
    )
    .await
    {
        Ok(connection) => Some(connection),
        // No daemon: the lease below is the whole guard.
        Err(error) if eukhe_client::daemon_client::is_connect_failure(&error) => None,
        Err(error) => {
            return Err(HeadlessSessionError::ActiveSessionsCheck(
                crate::daemon_command::connect_error(error, &socket),
            ))
        }
    };
    if let Some((client, mut events)) = connection {
        let list = eukhe_types::daemon::DaemonCommand::List {
            id: None,
            all: None,
            cwd: None,
            session_dir: None,
            include_client_owned: None,
            rest: serde_json::Map::default(),
        };
        let list = crate::daemon_command::request(
            &client,
            &mut events,
            list,
            eukhe_client::daemon_client::DEFAULT_REQUEST_TIMEOUT_MS,
        )
        .await
        .map_err(HeadlessSessionError::ActiveSessionsCheck)?;
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
                return Err(
                    match eukhe_tui::session_open_error::holder_from_roster(
                        std::slice::from_ref(&row),
                        &target,
                    ) {
                        Some(holder) => HeadlessSessionError::HeldByDaemonSession {
                            holder,
                            session_path: target,
                        },
                        None => HeadlessSessionError::ListedActive {
                            active_session_id: active_session_id.to_owned(),
                            session_path: target,
                        },
                    },
                );
            }
        }
    }
    // The roster covers only this daemon's sessions; the runtime lease table
    // is the cross-process ownership record. Acquire (not probe) so no
    // window opens between the check and the open.
    let agent_dir = crate::config::get_agent_dir();
    match eukhe_daemon::lease::acquire_runtime_session_lease(session_path, &agent_dir) {
        Ok(lease) => Ok(lease),
        Err(error) => match error.downcast::<SessionAlreadyActiveError>() {
            Ok(source) => Err(HeadlessSessionError::Held {
                source,
                session_path: session_path.to_path_buf(),
            }),
            Err(error) => Err(HeadlessSessionError::LeaseCheck(error)),
        },
    }
}

#[cfg(test)]
mod tests;
