//! The headless runtimes: print/json (single-shot prompts -> answer over an
//! `eukhe_core::durable::EukheSession`, the pi-durable print pattern:
//! submit, wait for the submission, wait for the conversation to go idle),
//! the RPC mode's session factory, and the ACP daemon create.

use std::future::Future;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_core::durable::goals::{
    autonomous_state, seed_initial_goal, set_autonomous, AutonomousChange,
};
use eukhe_core::durable::{classify_session_command, execute_session_command, EukheSession};
use eukhe_core::session::discovery::SessionSelectorError;
use eukhe_daemon::worker::durable_host::{CoalesceMode, EventTranslator};
use eukhe_durable::harness::types::InputSubmissionDraft;
use eukhe_durable::harness::{watch_events, AgentEventStream, Conversation};
use eukhe_types::pi_ai::{ImageContent, UserContent, UserContentBlock};
use futures::FutureExt;

use crate::headless_autonomous::{autonomous_exit_stderr, autonomous_runtime_config};
use crate::headless_session::{
    open_headless_session, sessions_dir, stderr_turn_wait, HeadlessSession, HeadlessTarget,
    Selection,
};
use crate::headless_terminal::{select_terminal_result, RunFailure};
use crate::mode::{AppMode, MissingSubsystem, RunOptions};

/// The runtime: print/json, rpc, acp, daemon, and interactive dispatch.
pub struct PrintRuntime;

impl crate::mode::Runtime for PrintRuntime {
    fn run(&self, options: &RunOptions) -> Result<i32, MissingSubsystem> {
        // `model list` takes the full runtime path in every mode and exits
        // (TS main: listModels runs after session assembly, before any mode
        // transport, and exits 0).
        if options.list_models.is_some() {
            return match crate::list_models::run(options) {
                Ok(code) => Ok(code),
                Err(message) => {
                    eprintln!("Error: {message}");
                    Ok(1)
                }
            };
        }
        match options.app_mode {
            // Runtime failures print themselves and exit non-zero; the typed
            // MissingSubsystem channel stays reserved for unwired subsystems.
            AppMode::Print | AppMode::Json => match run_print_mode(options) {
                Ok(code) => Ok(code),
                Err(message) => {
                    eprintln!("Error: {message}");
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

fn run_on_runtime(future: impl Future<Output = Result<i32, String>>) -> Result<i32, String> {
    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .map_err(|error| error.to_string())?
        .block_on(future)
}

/// The ACP headless mode (TS main.ts, `useDaemonClient`): ensure a
/// supervisor is listening (spawning one detached), create the daemon
/// session the CLI session flags select, and serve the ACP surface over it
/// until the client disconnects. Any startup failure is an `Error:` exit 1
/// before the first ACP frame.
async fn acp_mode_main(options: &RunOptions) -> Result<i32, String> {
    // The disclosure prints on the ACP client's stderr before any
    // transport starts.
    crate::telemetry_notice::print_if_due(&options.config);
    // Flag > env > default: the same `EUKHE_DAEMON_SOCKET` contract as
    // every other mode.
    let socket_path = crate::config::resolve_daemon_socket_path(options.daemon_socket.as_deref());
    let ready = crate::interactive_mode::ensure_daemon_running(&socket_path, &options.config.cwd)
        .await
        .map_err(|error| format!("{error:#}"))?;
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
    .map_err(|error| format!("{error:#}"))
}

/// The ACP daemon session's create (TS main.ts `defaultSessionConfig` +
/// the startup create): the session the flags select (a durable storage
/// dir or a not-yet-imported legacy file; `--fork` forks into a fresh
/// storage here first), client-owned only for `--no-session`, plus the
/// session's cwd. The worker opens and leases the selected session itself.
async fn daemon_acp_create(
    options: &RunOptions,
    cx: &Context,
) -> Result<(PathBuf, eukhe_types::daemon::DaemonCommand), String> {
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
        // The telemetry execution mode (TS main.ts `executionMode: appMode`).
        "executionMode": "acp",
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
    if let Some(system_prompt) = &config.system_prompt {
        create_config["systemPrompt"] = serde_json::json!(system_prompt);
    }
    if !config.append_system_prompt.is_empty() {
        create_config["appendSystemPrompt"] = serde_json::json!(config.append_system_prompt);
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
        telemetry_disabled: crate::mode::create_telemetry_disabled(config),
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
async fn rpc_mode_main(options: &RunOptions) -> Result<i32, String> {
    crate::telemetry_notice::print_if_due(&options.config);
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
    .map_err(|error| format!("{error:#}"))
}

/// The session factory the RPC mode drives: the startup selection (the CLI
/// session flags) and the `new_session` / `switch_session` / `fork`
/// replacements (TS `runtimeHost` replacement flows): eukhe-cli owns the
/// assembly, the mode owns the swap.
fn rpc_engine_factory(options: &RunOptions) -> eukhe_daemon::rpc::session::RpcEngineFactory {
    let options = options.clone();
    Arc::new(move |request, turn_wait| {
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
            let opened =
                open_headless_session(&options, target, Some(turn_wait), &BACKGROUND_CONTEXT)
                    .await?;
            Ok(eukhe_daemon::rpc::session::RpcEngineHandle {
                session: opened.session,
                session_lease: opened.lease,
            })
        }
        .boxed()
    })
}

/// Render a selector failure with the main.ts formatting: the error message
/// plus the browse hint.
pub(crate) fn render_selector_error(error: &SessionSelectorError) -> String {
    format!(
        "{}.{}\nOpen eukhe and press left-arrow to browse sessions.",
        error.message(),
        error.suggestion().unwrap_or_default()
    )
}

/// Print/json mode on its own runtime, the session lease owned outside it.
fn run_print_mode(options: &RunOptions) -> Result<i32, String> {
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
    ) -> std::pin::Pin<Box<dyn Future<Output = Result<i32, String>> + 'a>>,
) -> Result<i32, String> {
    // Declared before the runtime so unwinding also drops the runtime (and
    // stops its tasks) before the lease releases.
    let mut lease = None;
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .map_err(|error| error.to_string())?;
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
) -> Result<i32, String> {
    // Every headless mode discloses immediately.
    crate::telemetry_notice::print_if_due(&options.config);
    let cx = &*BACKGROUND_CONTEXT;
    let mut opened = open_headless_session(
        options,
        HeadlessTarget::Selected,
        Some(stderr_turn_wait()),
        cx,
    )
    .await?;
    *lease = opened.lease.take();
    let result = run_prompts(&opened, options, cx).await;
    let HeadlessSession { session, .. } = opened;
    // Every other holder (the event stream, the prompt loop) is gone.
    if let Ok(session) = Arc::try_unwrap(session) {
        session
            .close(cx)
            .await
            .map_err(|error| format!("{error:#}"))?;
    }
    result
}

/// The prompts of this invocation: the combined initial message (with the
/// `@file` images; TS `initialImages`), then the later CLI messages.
fn prompts(options: &RunOptions) -> impl Iterator<Item = (&str, Vec<ImageContent>)> {
    let images = options
        .initial_images
        .iter()
        .map(|image| ImageContent {
            data: image.data.clone(),
            mime_type: image.mime_type.clone(),
        })
        .collect::<Vec<_>>();
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

fn user_content(prompt: &str, images: Vec<ImageContent>) -> UserContent {
    if images.is_empty() {
        return UserContent::Text(prompt.to_owned());
    }
    let mut blocks = vec![UserContentBlock::Text(
        eukhe_types::pi_ai::TextContent::new(prompt),
    )];
    blocks.extend(images.into_iter().map(UserContentBlock::Image));
    UserContent::Blocks(blocks)
}

/// Run the prompts, stream json events when requested, and decide the exit
/// code: session commands run through the durable executor (a failure
/// prints its raw error and exits 1 without later prompts, TS print-mode's
/// catch); every other prompt is submitted and waited for, then the
/// conversation runs idle (goal and autonomous continuations, compaction).
/// Text mode prints the terminal result; both modes apply the autonomous
/// exit contract.
async fn run_prompts(
    opened: &HeadlessSession,
    options: &RunOptions,
    cx: &Context,
) -> Result<i32, String> {
    let session = &opened.session;
    let json_mode = options.app_mode == AppMode::Json;
    let conversation = session.main();
    let harness = session.harness();
    let events = if json_mode {
        println!("{}", session_header(opened));
        Some(JsonEvents::start(session, &conversation, cx).await?)
    } else {
        None
    };
    let failure = drive_prompts(session, &conversation, options, cx).await;
    if let Some(events) = events {
        events.finish().await;
    }
    let failure = failure?;
    // The rejected prompt wait (TS print-mode's catch): the raw command
    // error on stderr, exit 1, no terminal selection.
    if let Some(error) = failure {
        eprintln!("{error}");
        return Ok(1);
    }
    let mut exit_code = 0;
    // The TS print-mode exit contract: json mode never derives the exit
    // code from the terminal selection (the event stream carries
    // everything); text mode prints the primary (an error primary to
    // stderr with exit 1, a settled answer to stdout) and the trailing
    // compaction outcomes to stderr.
    if !json_mode {
        let result = select_terminal_result(&conversation, cx).await?;
        if let Some(primary) = result.primary {
            match primary.failure() {
                Some(RunFailure::Message(stderr)) => {
                    exit_code = 1;
                    eprintln!("{stderr}");
                }
                Some(RunFailure::Silent) => exit_code = 1,
                None => println!("{}", primary.stdout_text()),
            }
        }
        for outcome in result.compaction_outcomes {
            eprintln!("{}", outcome.content);
            if outcome.outcome == "failed" {
                exit_code = 1;
            }
        }
    }
    // The TS print-mode autonomous contract applies to both output modes.
    let autonomous = autonomous_state(harness, conversation.id(), cx)
        .await
        .map_err(|error| format!("{error:#}"))?;
    if let Some(stderr) = autonomous_exit_stderr(&autonomous.to_runtime()) {
        eprintln!("{stderr}");
        exit_code = 1;
    }
    Ok(exit_code)
}

/// The prompt loop. `Ok(Some(error))` is a failed session command.
async fn drive_prompts(
    session: &EukheSession,
    conversation: &Conversation,
    options: &RunOptions,
    cx: &Context,
) -> Result<Option<String>, String> {
    let harness = session.harness();
    let config = &options.config;
    // The CLI autonomous flags enable the run on the main conversation; a
    // run without flags keeps the session's state (`/autonomous` rewrites
    // it live).
    if let Some(autonomous) = &config.autonomous {
        set_autonomous(
            harness,
            conversation.id(),
            AutonomousChange::On(autonomous_runtime_config(autonomous)),
            cx,
        )
        .await
        .map_err(|error| format!("{error:#}"))?;
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
        .await
        .map_err(|error| format!("{error:#}"))?;
        idle(conversation, cx).await?;
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
                return Ok(Some(error));
            }
        } else {
            let submission = conversation
                .submit(
                    InputSubmissionDraft {
                        request_id: None,
                        content: user_content(&prompt, images),
                        when_busy: None,
                    },
                    cx,
                )
                .await
                .map_err(|error| format!("{error:#}"))?;
            submission
                .wait(cx)
                .await
                .map_err(|error| format!("{error:#}"))?;
        }
        // Continuations (goal, autonomous), queued input, and compaction
        // run before the next prompt.
        idle(conversation, cx).await?;
    }
    Ok(None)
}

async fn idle(conversation: &Conversation, cx: &Context) -> Result<(), String> {
    conversation
        .wait_for_idle(cx)
        .await
        .map_err(|error| format!("{error:#}"))
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
/// today's wire shapes (the daemon worker's translator), one line each.
struct JsonEvents {
    stream: AgentEventStream,
    translator: Arc<Mutex<EventTranslator>>,
}

impl JsonEvents {
    async fn start(
        session: &EukheSession,
        conversation: &Conversation,
        cx: &Context,
    ) -> Result<Self, String> {
        let stream = watch_events(session.harness(), conversation.id(), cx)
            .await
            .map_err(|error| format!("{error:#}"))?;
        let translator = Arc::new(Mutex::new(EventTranslator::new(
            stream.snapshot(),
            CoalesceMode::Immediate,
        )));
        let listener_translator = Arc::clone(&translator);
        stream
            .start(Arc::new(move |batch, _cx| {
                let frames = listener_translator
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .translate_batch(&batch);
                for frame in frames {
                    println!("{frame}");
                }
                futures::future::ready(Ok(())).boxed()
            }))
            .map_err(|error| format!("{error:#}"))?;
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
            println!("{frame}");
        }
    }
}

#[cfg(test)]
mod tests;
