//! Interactive mode wiring: resolve the daemon socket, ensure a supervisor is
//! listening (spawning one detached, TS `daemon-launch.ts` semantics), pick
//! the session from the CLI session flags, and hand off to the eukhe-tui
//! interactive loop. The session keeps running in the worker after the UI
//! exits; reattaching later restores it from the same session file.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use anyhow::{anyhow, Context, Result};

use crate::config;
use crate::mode::RunOptions;
use eukhe_tui::interactive::{InteractiveOptions, ModelSelection, SessionSelection, UiMode};

// The daemon-ensure concern (the socket probe, the stale-daemon shutdown,
// the detached supervisor spawn, and the startup poll window with its
// consts) moved to the child module at the same tree position
// (interactive_mode::daemon); the pub re-exports keep the print
// runtime's and the integration tests' paths stable.
mod daemon;

pub(crate) use daemon::CliLauncher;
pub use daemon::{ensure_daemon_running, ensure_daemon_running_with, DaemonReady};

// The first-run onboarding concern (the startup-model probe, the
// settings sink over the eukhe-tui trait, and the startup task assembly)
// moved to the child module at the same tree position
// (interactive_mode::onboarding); the task binding keeps the startup
// assembly's bare call in scope, and the cfg(test) binding keeps the
// unit battery's struct literals in scope.
mod onboarding;

use onboarding::onboarding_task;
#[cfg(test)]
use onboarding::SettingsOnboardingSink;

// The inline unit battery moved to the child module at the same tree
// position (interactive_mode::tests); its use-super glob keeps resolving
// through the facade's bindings and the pub contract.
#[cfg(test)]
mod tests;

/// Run the interactive TUI attached to the daemon. Returns the exit code.
pub fn run_interactive_mode(options: &RunOptions) -> Result<i32> {
    let socket_path = resolve_socket_path(options.daemon_socket.as_deref());
    let tui_options = build_tui_options(
        options,
        socket_path,
        std::sync::Arc::new(std::sync::Mutex::new(
            eukhe_tui::prompt_stash::PromptStashStore::default(),
        )),
    )?;
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .context("build the interactive runtime")?;
    runtime.block_on(async {
        // A kept daemon of another version is announced by the session
        // view itself (from its hello); the agents view gets it as its
        // status line.
        let daemon_notice = ensure_daemon_running(&tui_options.socket_path, &tui_options.cwd)
            .await?
            .notice();
        // `eukhe agents` and bare `--resume` open the agents view
        // (TS `agentsViewRequested`); the view then opens sessions, and a
        // session exits back into the view until the user exits it. TS gates
        // the explicit `agents` request on completed onboarding (a fresh
        // install shows the first-run notice first); bare `--resume` opens
        // the view regardless. `--continue` joins them when a candidate
        // session exists: the view opens preselected on the newest saved
        // session for the cwd (the notice names it) so the user confirms
        // what continues instead of a blind newest-resume.
        let continue_view = continue_recent_view(options, tui_options.onboarding.is_some());
        let agents_view = should_open_agents_view(
            options,
            tui_options.onboarding.is_some(),
            continue_view.is_some(),
        );
        if agents_view {
            let (anchor, notice) = continue_view.map_or((None, daemon_notice), |view| {
                (Some(view.session_id), Some(view.notice))
            });
            run_agents_view_flow(tui_options, anchor, None, notice).await
        } else {
            let outcome =
                eukhe_tui::interactive::run_interactive(tui_options.clone(), UiMode::Terminal)
                    .await?;
            // TS `main.ts`: a direct session run closes into the agents view
            // when the exit came through agents-back or `/resume`
            // (`launchAgentsView` anchored on the session just left); every
            // other exit (ctrl+c/ctrl+d, `/quit`) ends the process.
            if outcome.return_to_agents_view {
                // A startup attach that fell back to the view has no session
                // identity to anchor on; its notice seeds the view's status
                // line instead.
                let anchor = (!outcome.session_id.is_empty()).then(|| outcome.session_id.clone());
                let return_chat = return_chat_of(&outcome);
                run_agents_view_flow(tui_options, anchor, return_chat, outcome.agents_view_notice)
                    .await
            } else {
                print_resume_hint(outcome.resume_hint.as_deref());
                Ok(())
            }
        }
    })?;
    // tmux (verified on 3.2a) can drop the pane's final output when the
    // process dies immediately after writing it: the just-printed resume
    // hint -- and the tail of the exit flush -- races the pane-death
    // handling and the dead pane comes up blank. Holding the process
    // briefly after the last write lets the terminal apply it first. The
    // TS product wins this race only by exiting slower (its input drain
    // plus node teardown); the bound stays far inside the exit-within-1s
    // contract.
    std::thread::sleep(Duration::from_millis(300));
    Ok(0)
}

/// TS `shutdown` prints the dim resume hint (`formatResumeHint`) to stdout
/// after the TUI is restored; agents-view returns suppress it. Dim is the
/// TS `chalk.dim` styling (`ESC[2m` ... `ESC[22m`). The print is the last
/// exit-path write before the fixed pre-exit delay below, and on a slow
/// terminal it blocks behind the flush still draining the pty: its
/// completion is exit-path progress (the exit guard's watchdog holds its
/// force-quit while progress lands -- a draining terminal is not a stalled
/// shutdown), and the stamp it leaves carries the fixed delay inside the
/// guard's grace window.
fn print_resume_hint(hint: Option<&str>) {
    if let Some(hint) = hint {
        println!("\x1b[2m{hint}\x1b[22m");
    }
    eukhe_tui::exit_guard::note_exit_progress();
}

/// The agents-view loop: open the view, run the session it opens, and return
/// to the view when the session detaches through agents-back or bare
/// `/resume` (TS `InteractiveMode.run` returning `agents_view`). Every other
/// session exit -- ctrl+c/ctrl+d, `/quit`, `/exit` -- ends the whole app (TS
/// `shutdown()` exits the process instead of reopening the view). A
/// `/resume <selector>` chain runs its target before the loop decides again.
/// `return_chat` is the live session id of the chat the view is entered
/// from: escape on the empty global view returns to it (a startup launch
/// straight into the view has none, and escape there exits).
async fn run_agents_view_flow(
    base: InteractiveOptions,
    anchor: Option<String>,
    return_chat: Option<String>,
    notice: Option<String>,
) -> Result<()> {
    let mut anchor = anchor;
    let mut return_chat = return_chat;
    // The flow's roster connection (TS `AgentsViewPersistentState.rosterClient`):
    // every view run in this loop reuses it, and a chat run hands it back,
    // so a switch back from a chat skips the connect + hello handshake.
    let mut roster_link: Option<eukhe_tui::agents_view::AgentsViewLink> = None;
    // The view/session loop's carried state (TS `AgentsViewPersistentState`):
    // a stack of scope frames (the scope plus the return chat each was
    // opened from), the typed query, the drilled-in row's ancestors to
    // re-expand, and the selected row's identity and key.
    let mut frames: Vec<(
        eukhe_tui::agents_view::AgentsViewScope,
        Option<SessionSelection>,
    )> = Vec::new();
    let mut query: Option<String> = None;
    // The view/session loop's carried incident notice state (TS
    // `persistentState.incidentNoticeState`): a dismissal survives the
    // next view run, and the 30s poll continues from the consumed offset.
    let mut incident_notice_state: Option<eukhe_tui::incident_notices::IncidentNoticeState> = None;
    let mut expanded_ancestors: Vec<String> = Vec::new();
    let mut selected_row_identity: Option<String> = None;
    let mut selected_key: Option<eukhe_tui::agents_view::AgentsViewSelectionKey> = None;
    let mut status_message: Option<String> = notice;
    loop {
        // The live settings theme (a chat's `/settings` switch carries
        // back), re-read per view run; its warnings join the view's notice.
        let theme_name = base
            .client_settings
            .as_ref()
            .and_then(|settings| settings.theme())
            .unwrap_or_else(|| base.theme.clone());
        let resolved_theme = eukhe_tui::theme_catalog::load_client_theme(
            base.client_settings.as_deref(),
            &theme_name,
        );
        if !resolved_theme.warnings.is_empty() {
            let warnings = resolved_theme.warnings.join("\n");
            status_message = Some(match status_message.take() {
                Some(notice) => format!("{notice}\n{warnings}"),
                None => warnings,
            });
        }
        let view_options = eukhe_tui::agents_view::AgentsViewOptions {
            socket_path: base.socket_path.clone(),
            cwd: base.cwd.clone(),
            session_dir: base.session_dir.clone(),
            theme: resolved_theme.theme,
            version: base.version.clone(),
            anchor_session_id: anchor.clone(),
            return_active_session_id: return_chat.clone(),
            scope: frames.last().map(|(scope, _)| scope.clone()),
            query: query.clone(),
            expanded_ancestors: expanded_ancestors.clone(),
            selected_row_identity: selected_row_identity.clone(),
            selected_key: selected_key.clone(),
            status_message: status_message.take(),
            // The view dispatches every action through the same effective
            // bindings as the session it opened from (TS
            // `AgentsViewMode.keybindings`).
            keybindings: base.keybindings.clone(),
            // TS `AgentsViewMode` constructs its TUI with the live
            // `settingsManager.getShowHardwareCursor()` (default false).
            show_hardware_cursor: base
                .client_settings
                .as_ref()
                .is_some_and(|settings| settings.show_hardware_cursor()),
            screen_mode: current_screen_mode(&base),
            // TS `persistentState.incidentNoticeState`: the incident
            // notice state survives leaving and re-entering the view (a
            // dismissed incident never comes back, and the poll does not
            // re-read consumed bytes).
            incident_notice_state: incident_notice_state.take(),
            // TS `AgentsViewModeOptions.config`: the flow's own create
            // config -- the base a saved reply's resume derives from.
            create_config: base.create_config(),
        };
        let view_run = eukhe_tui::agents_view::run_agents_view(
            view_options,
            eukhe_tui::agents_view::AgentsViewUiMode::Terminal,
            roster_link.take(),
        )
        .await?;
        let view = view_run.outcome;
        // A handoff to a chat parked the connection for this loop's next
        // view run; a selection-less exit closed it already.
        roster_link = view_run.link;
        // A dropped scope root or the view's parent key pops the frame (TS
        // `resolveAgentsViewScopeFrames` / the `scope_back` arm), so a later
        // agents-back lands in the parent scope; both clear the query.
        let scope_frame_popped = view.scope_dropped || view.scope_popped;
        if scope_frame_popped {
            frames.pop();
        }
        let Some(selection) = view.selection else {
            return Ok(());
        };
        expanded_ancestors = view.expanded_ancestors.clone();
        selected_row_identity = view.selected_row_identity.clone();
        selected_key = view.selected_key.clone();
        status_message = view.status_message.clone();
        incident_notice_state = Some(view.incident_notice_state);
        query = if scope_frame_popped { None } else { view.query };
        // The opened row's depth metadata rides the session run (TS
        // `sessionDepth`/`sessionHasChildren`): a drilled-in child renders
        // its `depth N` tray label.
        let mut session_options = base.clone();
        session_options.session = selection;
        session_options.session_rlm_depth = view.opened_rlm_depth;
        session_options.session_has_children = view.opened_has_children;
        session_options.screen_mode = current_screen_mode(&base);
        // The scoped panel's own exit (the parent key or escape) reopened
        // the scope root's chat: it starts with the dock focused on the
        // panel's own group (the Subagents item), not the prompt bar --
        // a plain row open keeps the editor's focus.
        session_options.restore_dock_focus = view.scope_back;
        // The opened session's own directory rides the options: the
        // session run anchors its cwd (and the file-completion base) on
        // the attached session's directory, not the launch directory the
        // view opened from (TS `getCurrentCwd`).
        if let Some(cwd) = view.opened_cwd {
            session_options.cwd = cwd;
        }
        let outcome =
            eukhe_tui::interactive::run_interactive(session_options, UiMode::Terminal).await?;
        if !outcome.session_id.is_empty() {
            anchor = Some(outcome.session_id.clone());
        }
        return_chat = return_chat_of(&outcome);
        if let Some(notice) = &outcome.agents_view_notice {
            status_message = Some(notice.clone());
        }
        if !outcome.return_to_agents_view {
            print_resume_hint(outcome.resume_hint.as_deref());
            if let Some(link) = roster_link.take() {
                link.close();
            }
            return Ok(());
        }
        if let Some(scope) = outcome.agents_view_scope {
            // The session's subagent summary line opened the agents view
            // scoped to its subtree: push a frame with the session as the
            // return chat (TS `transitionAgentsViewScope` push arm) and
            // clear the query -- the scope already narrows the list, and a
            // filter typed to find the session would hide the subtree.
            frames.retain(|(frame, _)| frame.session_id != scope.session_id);
            frames.push((
                scope,
                Some(SessionSelection::Attach(outcome.active_session_id.clone())),
            ));
            query = None;
        }
        // `/resume <selector>` routes straight to that session before the
        // loop reopens the view.
        let mut pending = outcome.selection_request;
        while let Some(selection) = pending.take() {
            let mut next = base.clone();
            next.session = selection;
            next.screen_mode = current_screen_mode(&base);
            let outcome = eukhe_tui::interactive::run_interactive(next, UiMode::Terminal).await?;
            if !outcome.session_id.is_empty() {
                anchor = Some(outcome.session_id.clone());
            }
            return_chat = return_chat_of(&outcome);
            if let Some(notice) = &outcome.agents_view_notice {
                status_message = Some(notice.clone());
            }
            if !outcome.return_to_agents_view {
                print_resume_hint(outcome.resume_hint.as_deref());
                if let Some(link) = roster_link.take() {
                    link.close();
                }
                return Ok(());
            }
            if let Some(scope) = outcome.agents_view_scope {
                frames.retain(|(frame, _)| frame.session_id != scope.session_id);
                frames.push((
                    scope,
                    Some(SessionSelection::Attach(outcome.active_session_id.clone())),
                ));
                query = None;
            }
            pending = outcome.selection_request;
        }
    }
}

/// The live session a chat run left through agents-back or `/resume`: the
/// view's escape returns to it. Empty when a startup attach fell back.
fn return_chat_of(outcome: &eukhe_tui::interactive::InteractiveOutcome) -> Option<String> {
    (!outcome.active_session_id.is_empty()).then(|| outcome.active_session_id.clone())
}

/// The `terminal.fullscreen` mode a surface mounts with: read at each
/// mount, since `/settings` can switch it while a chat runs.
fn current_screen_mode(base: &InteractiveOptions) -> eukhe_tui::screen_mode::ScreenMode {
    base.client_settings
        .as_ref()
        .map_or(base.screen_mode, |settings| {
            eukhe_tui::screen_mode::ScreenMode::from_fullscreen_setting(settings.fullscreen())
        })
}

/// `--daemon-socket` value, the `EUKHE_DAEMON_SOCKET` environment,
/// or the per-user default socket path (precedence in that order).
#[must_use]
pub fn resolve_socket_path(daemon_socket: Option<&str>) -> PathBuf {
    config::resolve_daemon_socket_path(daemon_socket)
}

fn build_tui_options(
    options: &RunOptions,
    socket_path: PathBuf,
    prompt_stash: std::sync::Arc<std::sync::Mutex<eukhe_tui::prompt_stash::PromptStashStore>>,
) -> Result<InteractiveOptions> {
    let config = &options.config;
    let session_dir = options
        .session
        .session_dir
        .clone()
        .or_else(|| Some(config.agent_dir.join("sessions")));
    // The user's `<agentDir>/binds.cfg` (a legacy `keybindings.json` is
    // imported into it once) over the shipped default binds drives the TUI.
    let keybindings = eukhe_tui::keybindings::KeybindingsManager::create(&config.agent_dir);
    // Test seam: a scripted faux daemon session (same contract as the print
    // runtime). Verification harness only; never set by the product.
    let script_path = std::env::var_os("EUKHE_FAUX_SCRIPT").map(PathBuf::from);
    // TS `createSessionManager`'s flag order (fork -> resume -> create):
    // a fork copies its source into a fresh file client-side, and the
    // daemon opens the fork -- never the source -- through the create
    // `sessionPath` (TS `getInteractiveDaemonSessionPath`).
    let session = match &options.session.fork {
        Some(selector) => fork_startup_selection(options, selector)?,
        None => session_selection(&options.session, session_dir.as_deref()),
    };
    // The chat markdown code-block indent reads the effective settings on
    // startup (TS `getCodeBlockIndent` -> `getMarkdownThemeWithSettings`).
    let settings = eukhe_core::settings::SettingsManager::create(&config.cwd, &config.agent_dir);
    let code_block_indent = settings.get_code_block_indent();
    let show_images = settings.get_show_images();
    let screen_mode =
        eukhe_tui::screen_mode::ScreenMode::from_fullscreen_setting(settings.get_fullscreen());
    // The `/tree` selector's initial filter and the branch-summary prompt
    // skip read the same settings the TS interactive mode reads at
    // startup.
    let tree_filter_mode = settings.get_tree_filter_mode();
    let branch_summary_skip_prompt = settings.get_branch_summary_skip_prompt();
    // The `/model` picker catalog: a startup snapshot of the available
    // models (same registry as the startup-model chain; the picker works
    // off the snapshot until the daemon's `get_model_catalog` response
    // lands). models.json entries are part of
    // the available catalog, so configured custom models list in the
    // picker; the picker itself owns the TS selector order.
    let auth = eukhe_core::auth::AuthStorage::create(&config.agent_dir);
    let registry =
        eukhe_core::models::ModelRegistry::create(auth, config.agent_dir.join("models.json"));
    let catalog: Vec<eukhe_types::ai::Model> =
        registry.get_available().into_iter().cloned().collect();
    let configured_providers: std::collections::HashSet<String> =
        catalog.iter().map(|model| model.provider.clone()).collect();
    let recent = settings.get_recent_models();
    let default_thinking_level = settings
        .get_default_thinking_level()
        .map(|level| level.model_level().wire_name().to_string());
    // `/login` + `/logout`: the provider auth flows (the API-key store,
    // the MCP device flow, the Prime Inference login, the provider
    // catalog) -- one handle serves the commands and the onboarding flow's
    // sign-in steps.
    let provider_auth = eukhe_tui::provider_auth::ProviderAuthCommandsHandle(std::sync::Arc::new(
        crate::provider_login::ProviderAuth::new(config.cwd.clone(), config.agent_dir.clone()),
    ));
    let onboarding = onboarding_task(options, Some(provider_auth.clone()));
    let tui_options_value = InteractiveOptions {
        code_block_indent,
        tree_filter_mode,
        branch_summary_skip_prompt,
        model_catalog: catalog,
        model_configured_providers: configured_providers,
        model_recent_models: recent,
        default_thinking_level,
        socket_path,
        cwd: config.cwd.clone(),
        session_dir,
        script_path,
        // Explicit CLI model flags ride every create request (TS
        // runtime-config propagation): the daemon worker must treat them as
        // authoritative, not fall back to a process-wide model.
        model_selection: ModelSelection {
            provider: config.provider.clone(),
            model: config.model.clone(),
            api_key: config.api_key.clone(),
            // The `--thinking` flag rides the same create-config path:
            // the worker clamps it to the model's supported levels.
            thinking: config.thinking,
        },
        // The raw `--models` patterns ride the create config (TS
        // `runtimeConfigFromArgs`); the daemon owns the resolution.
        models: config.models.clone(),
        no_session: options.session.no_session,
        session,
        initial_message: options.initial_message.clone(),
        show_images,
        screen_mode,
        // TS startup reads the settings theme (`getTheme() || "eukhe"`).
        theme: settings.get_theme().unwrap_or_default(),
        // The client-settings seam the interactive commands persist
        // through (`/settings`); themes register from the resource system
        // and the `--theme`/`--no-themes` flags.
        client_settings: Some(crate::client_settings::CliClientSettings::new(
            config.cwd.clone(),
            config.agent_dir.clone(),
            crate::client_settings::CliThemeFlags {
                paths: config.themes.clone(),
                no_themes: config.no_themes,
            },
        )),
        version: crate::config::version().to_string(),
        // TS `shouldRunOnboarding`: the settings flag alone mounts the
        // task; the carried startup-model state decides the branch and
        // gates the completion marker, and the auth handle serves the
        // not-ready branch's sign-in steps.
        onboarding,
        // `/mcp login` / `/mcp logout`: the client-side auth flows run in
        // this process (the TS interactive client's placement) and persist
        // through the shared auth store the daemon's sessions read.
        client_auth: Some(eukhe_tui::client_auth::ClientAuthCommandsHandle(
            std::sync::Arc::new(crate::mcp_login::TerminalMcpAuth::new(
                config.cwd.clone(),
                config.agent_dir.clone(),
            )),
        )),
        // `/login` + `/logout`: the provider auth flows (the API-key store,
        // the MCP device flow, the provider catalog).
        provider_auth: Some(provider_auth),
        keybindings,
        // The process-wide prompt stash store (TS `ClientPromptStashStore`
        // lives in `main.ts`'s invocation scope): one store per process, so
        // the agents-view loop (view -> chat -> view) keeps every stashed
        // draft alive across its chat runs.
        prompt_stash,
        // RLM depth metadata comes from the agents view when it opens a row
        // (TS `sessionDepth`/`sessionHasChildren`); a direct CLI session is
        // a root run. A direct launch never reopens from the scoped panel,
        // so the dock's focus restore stays off (the editor owns it).
        session_rlm_depth: None,
        session_has_children: false,
        restore_dock_focus: false,
        // Dictation into the draft: a recorder program on PATH, and the
        // `dictation` role in this cwd and agent dir.
        dictation: Some(eukhe_tui::dictation::Dictation {
            recorder: std::sync::Arc::new(eukhe_tui::dictation::SubprocessRecorder::platform()),
            transcriber: std::sync::Arc::new(crate::tiny_command::RoleTranscriber {
                cwd: config.cwd.clone(),
                agent_dir: config.agent_dir.clone(),
            }),
        }),
    };
    Ok(tui_options_value)
}

/// Map the CLI session flags onto the TUI session selection (the TS order:
/// explicit `--resume` selector, then a fresh session). `--continue` never
/// maps to a resume: it surfaces its candidate through the agents view
/// ([`continue_recent_view`]) and falls through to the fresh-session run
/// here.
fn session_selection(
    session: &crate::mode::SessionOptions,
    session_dir: Option<&Path>,
) -> SessionSelection {
    if let Some(selector) = &session.resume {
        let default_dir = config::get_agent_dir().join("sessions");
        let dir = session_dir.unwrap_or(&default_dir);
        return resolve_resume_selector(selector, dir);
    }
    SessionSelection::New
}

/// TS `createSessionManager`'s fork arm for the interactive launch: resolve
/// the selector and fork the source into a fresh session storage
/// client-side (the same fork print mode runs), then hand the daemon the
/// fork -- never the source -- as the create `sessionPath` (TS
/// `getInteractiveDaemonSessionPath`). No daemon-active guard applies: the
/// fork reads the source and writes a brand-new storage, so a session a
/// live worker already hosts forks fine (TS parity). The fork's lease drops
/// here: the daemon worker takes the storage's lease when it opens it.
///
/// # Errors
///
/// The selector error (with the browse hint), an empty or invalid source,
/// or the fork failure.
fn fork_startup_selection(options: &RunOptions, selector: &str) -> Result<SessionSelection> {
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    runtime.block_on(async {
        let cx = &*eukhe_chord::context::BACKGROUND_CONTEXT;
        let source = crate::headless_session::resolve_fork_source(options, selector, cx)
            .await
            .map_err(anyhow::Error::msg)?;
        let (_, dir, _lease) =
            crate::headless_session::fork_into_fresh(options, &source, &options.config.cwd, cx)
                .await
                .map_err(anyhow::Error::msg)?;
        Ok(SessionSelection::Resume(dir))
    })
}

/// TS `shouldOpenAgentsViewForDaemonInteractive`: a selector, continuation,
/// or fork opens its target session directly instead of the agents view.
/// The selector (`--resume <id>`) and `--continue` launches never reach the
/// view with `--fork` anyway (the shared flag validation refuses the
/// combination at startup), so only the explicit `agents` request needs the
/// guard; bare `--resume` still opens the view, as does a `--continue` with
/// a saved candidate.
fn should_open_agents_view(
    options: &RunOptions,
    onboarding_pending: bool,
    continue_view: bool,
) -> bool {
    options.session.resume_bare
        || (options.agents_view_requested && !onboarding_pending && options.session.fork.is_none())
        || continue_view
}

/// The `--continue` launch's agents-view target: the newest saved session
/// for the cwd (the candidate TS `SessionManager.continueRecent` silently
/// reopens) plus the status-line notice that names it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ContinueRecentView {
    /// The candidate's session id: the view preselects (anchors on) its row.
    session_id: String,
    notice: String,
}

/// Resolve the `--continue` launch into an agents-view opening. The launch
/// never blind-resumes the newest session: on a shared session dir that
/// could be any session (an orchestrator's), and reopening it would revive
/// its context and scheduled jobs without the user ever naming it. The view
/// shows the candidate preselected and the user confirms what continues (a
/// sanctioned divergence: TS `SessionManager.continueRecent` reopens the
/// candidate silently). `None` falls through to the direct fresh-session
/// run: not a bare `--continue` launch (an explicit `--resume` selector or
/// `--no-session` owns the selection first, the TS flag order), a pending
/// onboarding (the first-run notice owns the startup, like the explicit
/// `agents` request), or no saved session for the cwd (the fresh-session
/// fallback TS `continueRecent` itself takes).
fn continue_recent_view(
    options: &RunOptions,
    onboarding_pending: bool,
) -> Option<ContinueRecentView> {
    if !options.session.continue_recent
        || options.session.resume.is_some()
        || options.session.no_session
        || onboarding_pending
    {
        return None;
    }
    let session_dir = options
        .session
        .session_dir
        .clone()
        .unwrap_or_else(|| options.config.agent_dir.join("sessions"));
    let cwd = options.config.cwd.clone();
    let path =
        eukhe_core::session::discovery::find_most_recent_session_for_cwd(&session_dir, &cwd)?;
    let header = eukhe_core::session::manager::read_session_header(&path)?;
    Some(ContinueRecentView {
        session_id: header.id.clone(),
        notice: format!(
            "Most recent session for this directory: {} -- Enter continues it, or pick another session.",
            header.id
        ),
    })
}

/// `--resume <selector>`: an existing session file path, a `<id>.jsonl` under
/// the sessions dir, or a live daemon session id (attach).
fn resolve_resume_selector(selector: &str, session_dir: &Path) -> SessionSelection {
    let path = config::expand_tilde_path(selector);
    if path.is_file() {
        return SessionSelection::Resume(path);
    }
    let candidate = session_dir.join(format!("{selector}.jsonl"));
    if candidate.is_file() {
        return SessionSelection::Resume(candidate);
    }
    SessionSelection::Attach(selector.to_string())
}
