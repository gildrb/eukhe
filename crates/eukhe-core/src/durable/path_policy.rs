//! The path policy of a session (`laws/path_policy/` (G1)) and
//! the gate the document tools pass every path access through.
//!
//! [`session_policy`] builds the one [`PathPolicy`] the `bash` tool and
//! the document tools judge paths by. Its protected and secret sets come
//! from the state list ([`crate::state_list`]) and the settings loaders:
//!
//! - the agent dir, the work root and the executables' dir, each with
//!   every entry directly in it: the global scope's files live in the agent
//!   dir (`settings.json`, `config.cfg`, `subagent.cfg`, `models.json`,
//!   `auth.json`, `binds.cfg`);
//! - the run dir and the auto-start dirs, with everything under them;
//! - the profile dir ([`PROFILE_DIR`], `agents/<agent>.cfg`);
//! - the project config dir of the session (`<cwd>/.eukhe`) and every
//!   `.eukhe` dir below the workspace root ([`CONFIG_DIR_NAME`]);
//! - every settings file the session loads and re-reads
//!   ([`EukheSettings::watched`]);
//! - every `.git` dir below the workspace root (its config and hooks name
//!   programs git runs), and every directory on `PATH` (a file put there
//!   replaces a command).
//!
//! The secret set holds the state list's credentials and the credential
//! stores other programs keep in the home dir.
//!
//! The own set (spec I3) holds what no agent may write: eukhe's own
//! config and credentials (the agent dir and its direct entries, the
//! profile dir, every settings file the session reads), the session
//! record (the sessions dir and `sessions-archive`), and the files a
//! check under acceptance protects.
//!
//! [`DocumentsGate`] is the gate of one document tool call: every access
//! runs unasked but a write to an own path, which is refused, and an
//! irreversible access the editor attached through ACP rejects.
//! [`RecordingGate`] also keeps the irreversible accesses it let run.

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, PoisonError};

use eukhe_docs::{Access, AccessGate, AccessRefusal};
use eukhe_types::effects::EffectClass;
use eukhe_types::path_policy::{
    OwnKind, OwnPath, OwnRule, OwnWrite, PathClass, PathPolicy, PathRule, RealPath,
};
use eukhe_types::shell::ShellEffects;

use eukhe_chord::context::Context;
use eukhe_durable::types::ConversationId;

use super::acceptance::protected_files;
use super::editor_permission::{self, EDITOR_REFUSED};
use super::settings::EukheSettings;
use super::{EditorPermissionSink, HostDeps};
use crate::settings::{resolve_session_dir, CONFIG_DIR_NAME, PROFILE_DIR};
use crate::state_list::{state_list, Install, StateKind, StatePart};

/// The archive of the session record, in the agent dir.
const SESSIONS_ARCHIVE: &str = "sessions-archive";

/// The credential stores other programs keep in the home dir: ssh keys,
/// cloud and registry credentials, password stores (the AWS files are
/// Eukhe's credentials: the state list names them).
const HOME_SECRETS: &[&str] = &[
    ".ssh",
    ".azure",
    ".config/gcloud",
    ".config/gh",
    ".docker/config.json",
    ".kube",
    ".gnupg",
    ".password-store",
    ".local/share/keyrings",
    ".netrc",
    ".git-credentials",
    ".npmrc",
    ".pypirc",
    ".cargo/credentials",
    ".cargo/credentials.toml",
];

/// The environment variables that move a credential store away from its
/// home-dir place (the gcloud config dir).
const SECRET_ENV: &[&str] = &["CLOUDSDK_CONFIG"];

/// Where a session's files are: what [`policy`] reads besides the
/// workspace.
pub(crate) struct Layout<'a> {
    pub(crate) agent_dir: &'a Path,
    pub(crate) settings: &'a EukheSettings,
    pub(crate) home: Option<&'a Path>,
    /// The running executable's path; `None` when it does not resolve.
    pub(crate) executable: Option<&'a Path>,
    /// The `PATH` value; `None` when unset.
    pub(crate) path: Option<&'a OsStr>,
    /// The value of an environment variable; `None` when unset.
    pub(crate) env: &'a dyn Fn(&str) -> Option<OsString>,
    /// The files the session's checks under acceptance protect.
    pub(crate) protect: &'a [PathBuf],
}

/// The policy of `workspace` (its one root) over `layout`.
pub(crate) fn policy(layout: &Layout<'_>, workspace: &Path) -> PathPolicy {
    let mut protected = vec![
        PathRule::Tree(layout.agent_dir.join(PROFILE_DIR)),
        PathRule::Tree(layout.settings.cwd().join(CONFIG_DIR_NAME)),
        PathRule::Named(OsString::from(CONFIG_DIR_NAME)),
        PathRule::Named(OsString::from(".git")),
    ];
    let mut secret = Vec::new();
    let state = state_list(&Install {
        agent_dir: layout.agent_dir,
        home: layout.home,
        executable: layout.executable,
        cwd: workspace,
        env: layout.env,
    });
    for StatePart { kind, path } in state {
        match kind {
            // The dir and its entries: a write deeper (a session's
            // artifacts, another run's copy) is outside as any other.
            StateKind::AgentDir | StateKind::WorkRoot | StateKind::Executables => {
                protected.push(PathRule::Dir(path));
            }
            StateKind::RunDir | StateKind::AutoStart => protected.push(PathRule::Tree(path)),
            StateKind::Credentials => secret.push(path),
        }
    }
    protected.extend(
        layout
            .settings
            .watched()
            .iter()
            .cloned()
            .map(PathRule::Tree),
    );
    protected.extend(
        layout
            .path
            .into_iter()
            .flat_map(std::env::split_paths)
            .map(|dir| PathRule::Dir(workspace.join(dir))),
    );

    secret.extend(
        layout
            .home
            .into_iter()
            .flat_map(|home| HOME_SECRETS.iter().map(|entry| home.join(entry))),
    );
    secret.extend(
        SECRET_ENV
            .iter()
            .filter_map(|name| (layout.env)(name))
            .filter(|value| !value.is_empty())
            .map(|value| workspace.join(value)),
    );
    // The OS temp dir is scratch: every session writes its probe
    // scripts and files there, and a write outside the workspace is
    // irreversible. Its writes are inside.
    let mut roots = vec![workspace.to_path_buf()];
    let temp = std::env::temp_dir();
    if temp != workspace {
        roots.push(temp);
    }
    PathPolicy::new(roots, protected, secret).with_own(own(layout))
}

/// The own rules of `layout` (spec I3).
fn own(layout: &Layout<'_>) -> Vec<OwnRule> {
    let rule = |path, kind| OwnRule { path, kind };
    let sessions = resolve_session_dir(None, &layout.settings.manager(), layout.agent_dir)
        .map_or_else(|_| layout.agent_dir.join("sessions"), |dir| dir.path);
    let mut own = vec![
        rule(
            OwnPath::Dir(layout.agent_dir.to_path_buf()),
            OwnKind::Config,
        ),
        rule(
            OwnPath::Tree(layout.agent_dir.join(PROFILE_DIR)),
            OwnKind::Config,
        ),
    ];
    own.extend(
        layout
            .settings
            .watched()
            .iter()
            .map(|file| rule(OwnPath::Tree(file.clone()), OwnKind::Config)),
    );
    own.push(rule(OwnPath::Tree(sessions), OwnKind::SessionRecord));
    own.push(rule(
        OwnPath::Tree(layout.agent_dir.join(SESSIONS_ARCHIVE)),
        OwnKind::SessionRecord,
    ));
    own.extend(
        layout
            .protect
            .iter()
            .map(|file| rule(OwnPath::Tree(file.clone()), OwnKind::CheckFile)),
    );
    own
}

/// The path policy of a call of a session (its agent dir and settings)
/// working in `workspace` (the call's agent cwd, never a cwd the model
/// can change), whose checks protect `protect`.
pub(crate) fn session_policy(
    agent_dir: &Path,
    settings: &EukheSettings,
    workspace: &Path,
    protect: &[PathBuf],
) -> PathPolicy {
    let home = eukhe_types::platform::home_dir();
    let executable = std::env::current_exe().ok();
    let path = std::env::var_os("PATH");
    policy(
        &Layout {
            agent_dir,
            settings,
            home: home.as_deref(),
            executable: executable.as_deref(),
            path: path.as_deref(),
            env: &|name| std::env::var_os(name),
            protect,
        },
        workspace,
    )
}

/// The path policy of a call of the session `deps` in `conversation_id`
/// (none for a request outside a conversation) working in `workspace`:
/// [`session_policy`] with the files the checks of that conversation and
/// of the session's root protect. A check that cannot be read protects
/// nothing (logged).
pub(crate) async fn call_policy(
    deps: &HostDeps,
    conversation_id: Option<ConversationId>,
    workspace: &Path,
    cx: &Context,
) -> PathPolicy {
    let mut protect = Vec::new();
    if let Some(harness) = deps.harness.get() {
        let root = deps.harness.root().map(|root| root.id());
        let mut conversations: Vec<ConversationId> = conversation_id.into_iter().collect();
        conversations.extend(root.filter(|root| Some(*root) != conversation_id));
        for conversation in conversations {
            match protected_files(&harness, conversation, &deps.cwd, cx).await {
                Ok(files) => protect.extend(files),
                Err(error) => tracing::warn!(%error, "the protected files of a check are unread"),
            }
        }
    }
    session_policy(&deps.agent_dir, &deps.settings, workspace, &protect)
}

/// The effects of `access` to `real` under `policy`, judged on `real` as
/// it is (no second resolution: a loop stays a loop): a search of a
/// directory that holds a secret reads the secret.
pub(crate) fn effects(policy: &PathPolicy, access: Access, real: &RealPath) -> ShellEffects {
    let judged = eukhe_shell::paths::judge(policy, real);
    match access {
        Access::Search if judged.holds_secret => ShellEffects::read_of(PathClass::Secret),
        Access::Read | Access::List | Access::Search => ShellEffects::read_of(judged.class),
        Access::Write => ShellEffects::write_to(judged.class),
    }
}

/// The gate of one document tool call (or one kernel `fs.*` request):
/// every access runs but a write to an own path, and an irreversible
/// access the editor rejects.
pub(crate) struct DocumentsGate {
    pub(crate) policy: PathPolicy,
    /// The editor's say on an irreversible access (spec I12); `None`:
    /// nothing asks.
    pub(crate) editor: Option<EditorAsk>,
}

/// How a [`DocumentsGate`] asks the editor about its call's accesses.
pub(crate) struct EditorAsk {
    pub(crate) sink: EditorPermissionSink,
    /// The tool call the accesses belong to; `None` for a kernel request.
    pub(crate) call: Option<String>,
    /// The start of each question's id (the call's id, else a fresh one),
    /// then the count of questions asked.
    pub(crate) prefix: String,
    pub(crate) asked: AtomicU64,
    /// The runtime the question waits on (the gate's checks run on a
    /// blocking thread).
    pub(crate) runtime: tokio::runtime::Handle,
}

/// Why a [`DocumentsGate`] refused an access. The effects open the
/// refusal, as a `bash` step's stop line names them.
#[derive(Debug, thiserror::Error)]
pub(crate) enum DocumentsRefusal {
    /// The write reaches an own path.
    #[error("({}) refused: {own}", effects.names())]
    Own {
        effects: ShellEffects,
        own: OwnWrite,
    },
    /// The editor rejected the irreversible access.
    #[error("({}) refused: {EDITOR_REFUSED}", effects.names())]
    Editor { effects: ShellEffects },
}

impl AccessGate for DocumentsGate {
    fn check(&self, access: Access, real: &RealPath, _display: &str) -> Result<(), AccessRefusal> {
        if access == Access::Write {
            let judged = eukhe_shell::paths::judge(&self.policy, real).class;
            if let Some(own) = eukhe_shell::paths::own_write(&self.policy, real, judged) {
                return Err(AccessRefusal::new(DocumentsRefusal::Own {
                    effects: ShellEffects::write_to(judged),
                    own,
                }));
            }
        }
        let Some(editor) = &self.editor else {
            return Ok(());
        };
        let effects = effects(&self.policy, access, real);
        let verb = match access {
            Access::Read => "read",
            Access::List => "list",
            Access::Search => "search",
            Access::Write => "write",
        };
        let asked = editor.asked.fetch_add(1, Ordering::Relaxed);
        let allowed = editor.runtime.block_on(editor_permission::allows(
            Some(std::sync::Arc::clone(&editor.sink)),
            format!("{}:fs{asked}", editor.prefix),
            editor.call.clone(),
            eukhe_shell::visible(&format!("{verb} {}", real.path().display())),
            EffectClass::of_shell(effects),
        ));
        if allowed {
            Ok(())
        } else {
            Err(AccessRefusal::new(DocumentsRefusal::Editor { effects }))
        }
    }
}

/// One access a call made that passed its gate and is irreversible (spec
/// I1): what it did, for people, and its classes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AccessRan {
    pub(crate) command: String,
    pub(crate) classes: Vec<EffectClass>,
}

/// A [`DocumentsGate`] that keeps every irreversible access it lets run,
/// in order, for the ledger.
pub(crate) struct RecordingGate {
    gate: DocumentsGate,
    ran: Mutex<Vec<AccessRan>>,
}

impl RecordingGate {
    pub(crate) fn new(gate: DocumentsGate) -> Self {
        Self {
            gate,
            ran: Mutex::new(Vec::new()),
        }
    }

    /// The irreversible accesses it let run, in order.
    pub(crate) fn into_ran(self) -> Vec<AccessRan> {
        self.ran
            .into_inner()
            .unwrap_or_else(PoisonError::into_inner)
    }
}

impl AccessGate for RecordingGate {
    fn check(&self, access: Access, real: &RealPath, display: &str) -> Result<(), AccessRefusal> {
        self.gate.check(access, real, display)?;
        let classes = EffectClass::of_shell(effects(&self.gate.policy, access, real));
        if eukhe_bend::rules::irreversible::is_irreversible(&classes) {
            let verb = match access {
                Access::Read => "read",
                Access::List => "list",
                Access::Search => "search",
                Access::Write => "write",
            };
            self.ran
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(AccessRan {
                    command: eukhe_shell::visible(&format!("{verb} {}", real.path().display())),
                    classes,
                });
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
