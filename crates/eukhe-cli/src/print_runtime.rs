//! The headless runtimes: print/json (single-shot prompts -> answer over an
//! `eukhe_core::durable::EukheSession`, the pi-durable print pattern:
//! submit, wait for the submission, wait for the conversation to go idle),
//! the RPC mode's session factory, and the ACP daemon create.

use std::future::Future;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_bend::rules::headless::{ExitCause, ExitFacts, Primary, RunEnd};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_core::durable::goals::{autonomous_state, configure_autonomous, seed_initial_goal};
use eukhe_core::durable::pending::PendingWork;
use eukhe_core::durable::{
    classify_session_command, execute_session_command, EukheSession, SessionCommandError,
};
use eukhe_daemon::rpc::error::RpcModeError;
use eukhe_daemon::rpc::session::RpcEngineError;
use eukhe_daemon::worker::durable_host::{CoalesceMode, EventTranslator};
use eukhe_durable::harness::types::InputSubmissionDraft;
use eukhe_durable::harness::{watch_events, AgentEventStream, Conversation};
use eukhe_durable::session::SessionError;
use eukhe_types::daemon::{SessionEvent, StreamUpdate};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::{ImageContent, UserContent, UserContentBlock};
use futures::FutureExt;

use crate::headless_autonomous::{autonomous_exit_stderr, autonomous_runtime_config};
use crate::headless_session::{
    open_headless_session, sessions_dir, HeadlessSession, HeadlessSessionError, HeadlessTarget,
    Selection,
};
use crate::headless_terminal::{select_terminal_result, RunFailure};
use crate::headless_wait::{still_running, wait_quiescent, HeadlessWaitError, RunWatch, Settled};
use crate::mode::{AppMode, MissingSubsystem, RunOptions};

/// Why a headless mode (print/json, ACP, RPC) failed before it could
/// answer; [`PrintRuntime`] prints it as `Error: <error>` and exits 1.
#[derive(Debug, thiserror::Error)]
enum HeadlessModeError {
    /// The mode's tokio runtime did not start.
    #[error("{0}")]
    Runtime(#[source] std::io::Error),
    #[error(transparent)]
    Session(#[from] HeadlessSessionError),
    /// A durable session operation failed (the event watch, the
    /// autonomous and goal setup, a submission, the transcript read, the
    /// close).
    #[error("{0:#}")]
    Durable(#[from] SessionError),
    #[error("{0}")]
    Wait(#[from] HeadlessWaitError),
    /// The compiled core refused the exit facts (an inconsistent build).
    #[error("{0}")]
    Exit(#[source] eukhe_bend::Error),
    /// No daemon supervisor could be reached or spawned for ACP.
    #[error("{0:#}")]
    Daemon(#[source] anyhow::Error),
    /// The ACP transport over the daemon session failed.
    #[error("{0:#}")]
    Acp(#[source] anyhow::Error),
    #[error("{0}")]
    Rpc(#[from] RpcModeError),
    #[error("system prompt input: {0}")]
    SystemPrompt(#[source] serde_json::Error),
    #[error("appended system prompt input: {0}")]
    AppendedSystemPrompt(#[source] serde_json::Error),
    /// The session resolved no model: a run with prompts must fail loudly.
    #[error(
        "No model is available for this run.\n\nLog in to a provider in an interactive session (run `eukhe`, then `/login`), or pass --provider and --model."
    )]
    NoModel,
}

/// The runtime: print/json, rpc, acp, daemon, and interactive dispatch.
pub struct PrintRuntime;

impl crate::mode::Runtime for PrintRuntime {
    fn run(&self, options: &RunOptions) -> Result<i32, MissingSubsystem> {
        // `model list` takes the full runtime path in every mode and exits
        // (TS main: listModels runs after session assembly, before any mode
        // transport, and exits 0).
        if options.list_models.is_some() {
            crate::list_models::run(options);
            return Ok(0);
        }
        match options.app_mode {
            // Runtime failures print themselves and exit non-zero; the typed
            // MissingSubsystem channel stays reserved for unwired subsystems.
            AppMode::Print | AppMode::Json => match run_print_mode(options) {
                Ok(code) => Ok(code),
                Err(error) => {
                    eprintln!("Error: {error}");
                    Ok(1)
                }
            },
            // The interactive TUI attaches through the daemon (spawning a
            // supervisor when none is running); the daemon mode runs the
            // supervisor in-process.
            AppMode::Interactive => match crate::interactive_mode::run_interactive_mode(options) {
                Ok(code) => Ok(code),
                Err(error) => {
                    eprintln!("Error: {error:#}");
                    Ok(1)
                }
            },
            AppMode::Daemon => {
                match crate::daemon_mode::run_daemon_mode(options.daemon_socket.as_deref()) {
                    Ok(code) => Ok(code),
                    Err(error) => {
                        eprintln!("Error: {error:#}");
                        Ok(1)
                    }
                }
            }
            // ACP mode: a thin JSON-RPC stdio transport over a daemon
            // session.
            AppMode::Acp => match run_on_runtime(acp_mode_main(options)) {
                Ok(code) => Ok(code),
                Err(error) => {
                    eprintln!("Error: {error}");
                    Ok(1)
                }
            },
            // RPC mode: the TS `modes/rpc` JSONL command surface over the
            // same in-process durable session the print mode uses.
            AppMode::Rpc => match run_on_runtime(rpc_mode_main(options)) {
                Ok(code) => Ok(code),
                Err(error) => {
                    eprintln!("Error: {error}");
                    Ok(1)
                }
            },
        }
    }
}

fn run_on_runtime(
    future: impl Future<Output = Result<i32, HeadlessModeError>>,
) -> Result<i32, HeadlessModeError> {
    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .map_err(HeadlessModeError::Runtime)?
        .block_on(future)
}

/// The ACP headless mode (TS main.ts, `useDaemonClient`): ensure a
/// supervisor is listening (spawning one detached), create the daemon
/// session the CLI session flags select, and serve the ACP surface over it
/// until the client disconnects. Any startup failure is an `Error:` exit 1
/// before the first ACP frame.
async fn acp_mode_main(options: &RunOptions) -> Result<i32, HeadlessModeError> {
    // Flag > env > default: the same `EUKHE_DAEMON_SOCKET` contract as
    // every other mode.
    let socket_path = eukhe_client::paths::resolve_daemon_socket_path(
        options.daemon_socket.as_deref().map(std::path::Path::new),
    );
    // An editor starts ACP, not the user at a terminal: it never replaces
    // a running daemon.
    let ready = crate::interactive_mode::ensure_daemon_running(
        &socket_path,
        &options.config.cwd,
        eukhe_client::daemon_build::Caller::Background,
    )
    .await
    .map_err(HeadlessModeError::Daemon)?;
    // ACP speaks JSON-RPC on stdout; the notice goes to the client's stderr.
    if let Some(notice) = ready.notice() {
        eprintln!("{notice}");
    }
    let (actual_cwd, create) = daemon_acp_create(options, &BACKGROUND_CONTEXT).await?;
    eukhe_daemon::acp::daemon::run_daemon_attached_acp_mode(
        eukhe_daemon::acp::daemon::DaemonAcpOptions {
            socket_path,
            actual_cwd,
            product_version: crate::config::version().to_string(),
            create,
        },
    )
    .await
    .map_err(HeadlessModeError::Acp)
}

/// The ACP daemon session's create (TS main.ts `defaultSessionConfig` +
/// the startup create): the session the flags select (a durable storage
/// dir or a not-yet-imported legacy file; `--fork` forks into a fresh
/// storage here first), client-owned only for `--no-session`, plus the
/// session's cwd. The worker opens and leases the selected session itself.
async fn daemon_acp_create(
    options: &RunOptions,
    cx: &Context,
) -> Result<(PathBuf, eukhe_types::daemon::DaemonCommand), HeadlessModeError> {
    use eukhe_types::daemon::DaemonSessionLifecycle;
    let config = &options.config;
    let (cwd, session_path, lifecycle) = match crate::headless_session::select(options, cx).await? {
        Selection::Memory => (
            config.cwd.clone(),
            None,
            DaemonSessionLifecycle::ClientOwned,
        ),
        Selection::Fresh { cwd } => (cwd, None, DaemonSessionLifecycle::Resident),
        Selection::Open {
            location,
            cwd_override,
            ..
        } => (
            crate::headless_session::stored_cwd(
                &location,
                &config.cwd,
                cwd_override.as_deref(),
                cx,
            )
            .await?,
            Some(location.path().to_path_buf()),
            DaemonSessionLifecycle::Resident,
        ),
        Selection::Fork { source } => {
            // The fork's lease drops here: the daemon worker takes the
            // storage's lease when it opens it.
            let (_, dir, _lease) =
                crate::headless_session::fork_into_fresh(options, &source, &config.cwd, cx).await?;
            (
                config.cwd.clone(),
                Some(dir),
                DaemonSessionLifecycle::Resident,
            )
        }
    };
    // The CLI session flags, under the TS `runtimeConfigFromArgs` names.
    // `--api-key` stays off: the create config is persisted.
    let mut create_config = serde_json::json!({
        "cwd": cwd.display().to_string(),
        "sessionDir": sessions_dir(options).display().to_string(),
    });
    if let Some(provider) = &config.provider {
        create_config["provider"] = serde_json::json!(provider);
    }
    if let Some(model) = &config.model {
        create_config["model"] = serde_json::json!(model);
    }
    if let Some(thinking) = config.thinking {
        create_config["thinking"] = serde_json::json!(thinking.wire_name());
    }
    // A string is prompt text; `{"file": "<path>"}` is a file to read.
    if let Some(system_prompt) = &config.system_prompt {
        create_config["systemPrompt"] =
            serde_json::to_value(system_prompt).map_err(HeadlessModeError::SystemPrompt)?;
    }
    if !config.append_system_prompt.is_empty() {
        create_config["appendSystemPrompt"] = serde_json::to_value(&config.append_system_prompt)
            .map_err(HeadlessModeError::AppendedSystemPrompt)?;
    }
    for (key, paths) in [
        ("skills", &config.skills),
        ("promptTemplates", &config.prompt_templates),
    ] {
        if !paths.is_empty() {
            create_config[key] = paths
                .iter()
                .map(|path| path.display().to_string())
                .collect::<Vec<_>>()
                .into();
        }
    }
    if let Some(autonomous) = &config.autonomous {
        create_config["autonomous"] = serde_json::json!(autonomous_runtime_config(autonomous));
    }
    // Verification seam (the interactive mode's contract): a scripted daemon
    // session from a script FILE path. The product never sets it.
    if let Some(script) = std::env::var_os("EUKHE_FAUX_SCRIPT") {
        create_config["script"] = serde_json::Value::String(script.to_string_lossy().to_string());
    }
    // Verification seam: a scripted parent session's children run this
    // script FILE. The product never sets it.
    if let Some(child_script) = std::env::var_os("EUKHE_FAUX_CHILD_SCRIPT") {
        create_config["childScript"] =
            serde_json::Value::String(child_script.to_string_lossy().to_string());
    }
    let create = eukhe_types::daemon::DaemonCommand::Create {
        id: None,
        session_path: session_path.map(|path| path.display().to_string()),
        continue_recent: None,
        no_session: options.session.no_session.then_some(true),
        name: None,
        config: Some(create_config),
        runtime_metadata: None,
        lifecycle: Some(lifecycle),
        env: None,
        launch_env: None,
        rest: serde_json::Map::default(),
    };
    Ok((cwd, create))
}

/// The RPC headless mode: the TS `modes/rpc` JSONL command surface over
/// stdio, on durable sessions this module's factory opens.
async fn rpc_mode_main(options: &RunOptions) -> Result<i32, HeadlessModeError> {
    let config = &options.config;
    eukhe_daemon::rpc::run_rpc_mode(eukhe_daemon::rpc::RpcOptions {
        engine_factory: rpc_engine_factory(options),
        autonomous_config: config.autonomous.as_ref().map(autonomous_runtime_config),
        initial_goal: config
            .initial_goal
            .as_ref()
            .map(|goal| (goal.objective.clone(), goal.token_budget.map(u64::from))),
    })
    .await
    .map_err(HeadlessModeError::Rpc)
}

/// The session factory the RPC mode drives: the startup selection (the CLI
/// session flags) and the `new_session` / `switch_session` / `fork`
/// replacements (TS `runtimeHost` replacement flows): eukhe-cli owns the
/// assembly, the mode owns the swap.
fn rpc_engine_factory(options: &RunOptions) -> eukhe_daemon::rpc::session::RpcEngineFactory {
    let options = options.clone();
    Arc::new(move |request| {
        let options = options.clone();
        async move {
            use eukhe_daemon::rpc::session::RpcEngineRequest;
            let target = match request {
                RpcEngineRequest::Startup => HeadlessTarget::Selected,
                RpcEngineRequest::New { cwd } => HeadlessTarget::New { cwd },
                RpcEngineRequest::Open {
                    session_path,
                    reuse_lease,
                } => HeadlessTarget::Open {
                    location: session_path,
                    reuse_lease,
                },
            };
            let opened = open_headless_session(&options, target, &BACKGROUND_CONTEXT)
                .await
                .map_err(RpcEngineError::new)?;
            Ok(eukhe_daemon::rpc::session::RpcEngineHandle {
                session: opened.session,
                session_lease: opened.lease,
            })
        }
        .boxed()
    })
}

/// Print/json mode on its own runtime, the session lease owned outside it.
fn run_print_mode(options: &RunOptions) -> Result<i32, HeadlessModeError> {
    with_print_runtime(options, |options, lease| {
        Box::pin(print_mode_main(options, lease))
    })
}

/// Own the print lease through runtime shutdown, including errors and
/// unwinding: the runtime drop joins blocking writers and cancels the
/// async tasks still holding the session (a detached host request, an
/// event stream the close never reached), and only then does the lease
/// release. The operation seam lets the regression exercise a writer
/// pending at shutdown.
fn with_print_runtime<Ctx>(
    context: &Ctx,
    run: impl for<'a> FnOnce(
        &'a Ctx,
        &'a mut Option<eukhe_daemon::lease::SessionLease>,
    ) -> std::pin::Pin<
        Box<dyn Future<Output = Result<i32, HeadlessModeError>> + 'a>,
    >,
) -> Result<i32, HeadlessModeError> {
    // Declared before the runtime so unwinding also drops the runtime (and
    // stops its tasks) before the lease releases.
    let mut lease = None;
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .map_err(HeadlessModeError::Runtime)?;
    let result = runtime.block_on(run(context, &mut lease));
    drop(runtime);
    drop(lease);
    result
}

/// Print/json mode: open the selected session, run every prompt, print the
/// result, close the session. The opened session's lease moves into
/// `lease`, which the caller releases after the runtime stops.
async fn print_mode_main(
    options: &RunOptions,
    lease: &mut Option<eukhe_daemon::lease::SessionLease>,
) -> Result<i32, HeadlessModeError> {
    let cx = &*BACKGROUND_CONTEXT;
    let mut opened = open_headless_session(options, HeadlessTarget::Selected, cx).await?;
    *lease = opened.lease.take();
    let result = run_prompts(&opened, options, cx).await;
    let HeadlessSession { session, .. } = opened;
    // Every other holder (the event stream, the prompt loop) is gone.
    if let Ok(session) = Arc::try_unwrap(session) {
        session.close(cx).await?;
    }
    result
}

/// The prompts of this invocation: the combined initial message (with the
/// `@file` images; TS `initialImages`), then the later CLI messages.
fn prompts(options: &RunOptions) -> impl Iterator<Item = (&str, Vec<ImageContent>)> {
    let images = options.initial_images.clone();
    options
        .initial_message
        .iter()
        .map(move |prompt| (prompt.as_str(), images.clone()))
        .chain(
            options
                .messages
                .iter()
                .map(|prompt| (prompt.as_str(), Vec::new())),
        )
}

/// The prompt as TS `AgentSession.prompt` sends it: a text block, then the
/// images.
fn user_content(prompt: &str, images: Vec<ImageContent>) -> UserContent {
    let mut blocks = vec![UserContentBlock::Text(
        eukhe_types::pi_ai::TextContent::new(prompt),
    )];
    blocks.extend(images.into_iter().map(UserContentBlock::Image));
    UserContent::Blocks(blocks)
}

/// How the prompt loop ended.
enum PromptsEnd {
    /// Every prompt ran and the session went quiescent after each.
    Completed,
    /// A session command failed (its raw error); later prompts did not run.
    CommandFailed(SessionCommandError),
    /// The wait limit elapsed while this still ran; later prompts did not
    /// run.
    GaveUp(PendingWork),
}

/// Run the prompts, stream json events when requested, and decide the exit
/// code: session commands run through the durable executor (a failure
/// prints its raw error, TS print-mode's catch); every other prompt is
/// submitted and waited for, then the session runs until it is quiescent
/// (goal and autonomous continuations, compaction, and every turn a
/// settled job or subagent wakes) or the wait limit elapses. Text mode
/// prints the terminal result; both modes print failures to stderr. The
/// compiled Bend core decides the exit code (`headless_exit`): 0 only for
/// a run that answered.
async fn run_prompts(
    opened: &HeadlessSession,
    options: &RunOptions,
    cx: &Context,
) -> Result<i32, HeadlessModeError> {
    let session = &opened.session;
    let json_mode = options.app_mode == AppMode::Json;
    let conversation = session.main();
    // A run with prompts needs a model: a session that resolved none must
    // fail loudly (exit 1), never idle through every prompt in silence.
    if prompts(options).next().is_some() {
        let agent = conversation
            .agent(cx)
            .await
            .map_err(HeadlessModeError::Durable)?;
        if agent.model.is_none() {
            if json_mode {
                crate::json_out::print_json_error(
                    "error",
                    "login_required",
                    "No model is available for this run.",
                );
                return Ok(1);
            }
            return Err(HeadlessModeError::NoModel);
        }
    }
    let harness = session.harness();
    let events = if json_mode {
        println!("{}", session_header(opened));
        Some(JsonEvents::start(session, &conversation, cx).await?)
    } else {
        None
    };
    let watch = RunWatch::start(opened, &conversation, cx).await?;
    let ended = drive_prompts(opened, &conversation, &watch, options, cx).await;
    // The run's disclosure rows (a reported overflow outcome) commit from
    // the compaction observer after the run settles: both modes report them.
    session.deps().observers_settled().await;
    if let Some(events) = events {
        events.finish().await;
    }
    let mut facts = ExitFacts {
        command_failed: false,
        gave_up: false,
        run: RunEnd::NoRun,
        primary: Primary::Nothing,
        compaction_failed: false,
        autonomous_failed: false,
    };
    match ended? {
        PromptsEnd::Completed => {}
        // The rejected prompt wait (TS print-mode's catch): the raw command
        // error on stderr, no terminal selection.
        PromptsEnd::CommandFailed(error) => {
            eprintln!("{error}");
            facts.command_failed = true;
        }
        PromptsEnd::GaveUp(work) => {
            eprintln!(
                "eukhe: stopped waiting after {} ms (--wait-limit-ms); still running: {}",
                options.config.wait_limit.as_millis(),
                still_running(&work)
            );
            facts.gave_up = true;
        }
    }
    let mut run_detail = None;
    let mut primary_message = None;
    if !facts.command_failed {
        (facts.run, run_detail) = watch.last_run(opened, cx).await?;
        // Text mode prints the primary (a settled answer to stdout) and the
        // trailing compaction outcomes to stderr; a failed primary's text
        // goes to stderr in both modes.
        let result = select_terminal_result(&conversation, cx).await?;
        if let Some(primary) = &result.primary {
            facts.primary = primary.kind();
            match primary.failure() {
                Some(RunFailure::Message(stderr)) => {
                    eprintln!("{stderr}");
                    primary_message = Some(stderr);
                }
                Some(RunFailure::Silent) => {}
                None if json_mode => {}
                // The answer is the model's text: remote data, never
                // terminal instructions, so the escapes and controls come
                // out before it reaches stdout (JSON keeps the raw bytes).
                None => println!("{}", crate::sanitize::text(&primary.stdout_text())),
            }
        }
        for outcome in result.compaction_outcomes {
            if !json_mode {
                eprintln!("{}", outcome.content);
            }
            if outcome.outcome == "failed" {
                facts.compaction_failed = true;
            }
        }
        // The TS print-mode autonomous contract applies to both output
        // modes.
        let autonomous = autonomous_state(harness, conversation.id(), cx).await?;
        if let Some(stderr) = autonomous_exit_stderr(&autonomous.to_runtime()) {
            eprintln!("{stderr}");
            facts.autonomous_failed = true;
        }
    }
    watch.finish().await;
    let exit = eukhe_bend::rules::headless::exit(&facts).map_err(HeadlessModeError::Exit)?;
    match exit.cause {
        // The run's failure text, unless the failed primary already
        // printed it.
        ExitCause::RunFailed(_) if run_detail.is_some() && run_detail == primary_message => {}
        ExitCause::RunFailed(_) => eprintln!(
            "eukhe: the run ended without an answer: {}",
            run_detail.as_deref().unwrap_or("no reason recorded")
        ),
        ExitCause::Unfinished => eprintln!("eukhe: the run ended without a final answer"),
        ExitCause::CompactionFailed if json_mode => eprintln!("eukhe: compaction failed"),
        ExitCause::Answered
        | ExitCause::CommandFailed
        | ExitCause::GaveUp
        | ExitCause::ProviderError
        | ExitCause::Aborted
        | ExitCause::SlashFailed
        | ExitCause::CompactionFailed
        | ExitCause::AutonomousFailed => {}
    }
    Ok(i32::from(exit.code))
}

/// The prompt loop: each prompt, then the wait for quiescence.
async fn drive_prompts(
    opened: &HeadlessSession,
    conversation: &Conversation,
    watch: &RunWatch,
    options: &RunOptions,
    cx: &Context,
) -> Result<PromptsEnd, HeadlessModeError> {
    let session = &opened.session;
    let harness = session.harness();
    let config = &options.config;
    let quiescent = || wait_quiescent(opened, watch, config.wait_limit, cx);
    // The CLI autonomous flags enable the run on the main conversation (no
    // status row, as TS `createAgentSession({ autonomous })`); a run without
    // flags keeps the session's state (`/autonomous` rewrites it live).
    if let Some(autonomous) = &config.autonomous {
        configure_autonomous(
            harness,
            conversation.id(),
            autonomous_runtime_config(autonomous),
            cx,
        )
        .await?;
    }
    // The CLI `--goal` seed: a fresh conversation starts the goal and
    // queues its continuation; a resumed or already-seeded one keeps its
    // persisted goal.
    if let Some(goal) = &config.initial_goal {
        seed_initial_goal(
            harness,
            conversation.id(),
            &goal.objective,
            goal.token_budget.map(u64::from),
            cx,
        )
        .await?;
        if let Settled::GaveUp(work) = quiescent().await? {
            return Ok(PromptsEnd::GaveUp(work));
        }
    }
    let resources = &session.deps().resources;
    for (prompt, images) in prompts(options) {
        // TS `_finishSubmissionNormalization` order: skill commands expand
        // first (`/skill:<name>` into its `<skill>` block), prompt
        // templates second.
        let (prompt, _) = eukhe_core::skills::expand_skill_command(prompt, &resources.skills);
        let prompt = eukhe_core::skills::expand_prompt_template(&prompt, &resources.prompts);
        // Session commands never reach the model loop.
        if let Some(command) = classify_session_command(&prompt) {
            let outcome = execute_session_command(session, conversation, &command, cx).await;
            if let Some(error) = outcome.error {
                return Ok(PromptsEnd::CommandFailed(error));
            }
        } else {
            let submission = conversation
                .submit(
                    InputSubmissionDraft {
                        request_id: None,
                        content: user_content(&prompt, images),
                        when_busy: None,
                        origin: InputOrigin::User,
                        entry: None,
                    },
                    cx,
                )
                .await?;
            submission.wait(cx).await?;
        }
        // Continuations (goal, autonomous), queued input, compaction, and
        // the turns settled jobs and subagents wake run before the next
        // prompt.
        if let Settled::GaveUp(work) = quiescent().await? {
            return Ok(PromptsEnd::GaveUp(work));
        }
    }
    Ok(PromptsEnd::Completed)
}

/// The json stream's leading identity line (the TS session header shape and
/// field order: `type`, `version`, `id`, `timestamp`, `cwd`,
/// `parentSession?`, `rlmDepth`).
fn session_header(opened: &HeadlessSession) -> serde_json::Value {
    header_for(
        &opened.session_id,
        &opened.cwd,
        opened.parent_session.as_deref(),
    )
}

fn header_for(
    session_id: &str,
    cwd: &std::path::Path,
    parent_session: Option<&std::path::Path>,
) -> serde_json::Value {
    let mut header = serde_json::Map::new();
    header.insert("type".into(), "session".into());
    header.insert("version".into(), 3.into());
    header.insert("id".into(), session_id.into());
    header.insert("timestamp".into(), crate::util_time::now_iso8601().into());
    header.insert("cwd".into(), cwd.display().to_string().into());
    if let Some(parent) = parent_session {
        header.insert("parentSession".into(), parent.display().to_string().into());
    }
    header.insert("rlmDepth".into(), 0.into());
    serde_json::Value::Object(header)
}

/// The json mode's event stream: the main conversation's durable events in
/// today's wire shapes (the daemon worker's translator), one line each,
/// `message_update` reduced to its change ([`json_line`]).
struct JsonEvents {
    stream: AgentEventStream,
    translator: Arc<Mutex<EventTranslator>>,
}

impl JsonEvents {
    async fn start(
        session: &EukheSession,
        conversation: &Conversation,
        cx: &Context,
    ) -> Result<Self, SessionError> {
        let stream = watch_events(session.harness(), conversation.id(), cx).await?;
        let translator = Arc::new(Mutex::new(EventTranslator::new(
            stream.snapshot(),
            CoalesceMode::Immediate,
        )));
        let listener_translator = Arc::clone(&translator);
        stream.start(Arc::new(move |batch, _cx| {
            let frames = listener_translator
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .translate_batch(&batch);
            for frame in &frames {
                print_event(frame);
            }
            futures::future::ready(Ok(())).boxed()
        }))?;
        Ok(Self { stream, translator })
    }

    /// Let every committed batch reach the listener, print the translator's
    /// parked frame, and stop.
    async fn finish(self) {
        self.stream.delivered().await;
        self.stream.stop().await;
        let parked = self
            .translator
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .flush();
        if let Some(frame) = parked {
            print_event(&frame);
        }
    }
}

/// Print one session event as its JSON line.
fn print_event(event: &SessionEvent) {
    match json_line(event) {
        Ok(line) => println!("{line}"),
        Err(error) => eprintln!("a session event does not serialize: {error}"),
    }
}

/// One session event's json-mode line (omp `printableEvent`): a
/// `message_update` carries only its change (omp's line has no
/// `outputTokens` either). The accumulated partial it holds would
/// re-serialize the whole in-flight message per frame (a long turn's stream
/// grows quadratically); the settled message follows whole in
/// `message_end`. A whole-message replacement keeps its message (and its
/// count): that message is its change.
fn json_line(event: &SessionEvent) -> serde_json::Result<String> {
    if let SessionEvent::MessageUpdate {
        assistant_message_event: update,
        ..
    } = event
    {
        match update {
            StreamUpdate::Start
            | StreamUpdate::TextStart
            | StreamUpdate::TextDelta { .. }
            | StreamUpdate::TextEnd
            | StreamUpdate::ThinkingStart
            | StreamUpdate::ThinkingDelta { .. }
            | StreamUpdate::ThinkingEnd
            | StreamUpdate::ToolcallStart
            | StreamUpdate::ToolcallDelta { .. }
            | StreamUpdate::ToolcallEnd => {
                return serde_json::to_string(&UpdateLine {
                    assistant_message_event: update,
                });
            }
            StreamUpdate::Message => {}
        }
    }
    serde_json::to_string(event)
}

/// A json-mode `message_update`: `type`, then the change.
#[derive(serde::Serialize)]
#[serde(tag = "type", rename = "message_update", rename_all = "camelCase")]
struct UpdateLine<'a> {
    assistant_message_event: &'a StreamUpdate,
}

#[cfg(test)]
mod tests;
