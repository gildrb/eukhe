//! The path policy of a session (docs/tools.md S7, `laws/path_policy.bend` (G1)) and
//! the gate the document tools pass every path access through.
//!
//! [`session_policy`] builds the one [`PathPolicy`] the `bash` tool and
//! the document tools judge paths by. Its protected set comes from the
//! settings loaders, not from a hand list:
//!
//! - the agent dir and every entry directly in it: the global scope's
//!   files live there (`settings.json`, `config.cfg`, `subagent.cfg`,
//!   `models.json`, `auth.json`, `binds.cfg`);
//! - the profile dir ([`PROFILE_DIR`], `agents/<agent>.cfg`);
//! - the project config dir of the session (`<cwd>/.eukhe`) and every
//!   `.eukhe` dir below the workspace root ([`CONFIG_DIR_NAME`]);
//! - every settings file the session loads and re-reads
//!   ([`EukheSettings::watched`]);
//! - every `.git` dir below the workspace root (its config and hooks name
//!   programs git runs), and every directory on `PATH` (a file put there
//!   replaces a command).
//!
//! The secret set holds `auth.json`, the Prime CLI config and the
//! credential stores other programs keep in the home dir.
//!
//! [`DocumentsGate`] is the gate of one document tool call: a read or
//! write of a secret, and every access the user's auto set
//! (`shell.autoEffects`) does not allow, ask the user through the
//! session's approval sink, as a `bash` step does.

use std::ffi::{OsStr, OsString};
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};

use eukhe_bend::rules::shell::Gate;
use eukhe_docs::{Access, AccessGate};
use eukhe_shell::Refusal;
use eukhe_types::path_policy::{PathClass, PathPolicy, PathRule, RealPath};
use eukhe_types::shell::{AutoSet, ShellApprovalRequest, ShellEffects};

use super::deps::ShellApprovalSink;
use super::settings::EukheSettings;
use super::shell::RefusalText;
use crate::settings::{CONFIG_DIR_NAME, PROFILE_DIR};

/// The credential stores other programs keep in the home dir: ssh keys,
/// cloud and registry credentials, password stores.
const HOME_SECRETS: &[&str] = &[
    ".ssh",
    ".aws",
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
/// home-dir place (the AWS shared files, the gcloud config dir).
const SECRET_ENV: &[&str] = &[
    "AWS_SHARED_CREDENTIALS_FILE",
    "AWS_CONFIG_FILE",
    "CLOUDSDK_CONFIG",
];

/// Where a session's files are: what [`policy`] reads besides the
/// workspace.
pub(crate) struct Layout<'a> {
    pub(crate) agent_dir: &'a Path,
    pub(crate) settings: &'a EukheSettings,
    pub(crate) home: Option<&'a Path>,
    /// The `PATH` value; `None` when unset.
    pub(crate) path: Option<&'a OsStr>,
    /// The value of a [`SECRET_ENV`] variable; `None` when unset.
    pub(crate) env: &'a dyn Fn(&str) -> Option<OsString>,
}

/// The policy of `workspace` (its one root) over `layout`.
pub(crate) fn policy(layout: &Layout<'_>, workspace: &Path) -> PathPolicy {
    let mut protected = vec![
        PathRule::Dir(layout.agent_dir.to_path_buf()),
        PathRule::Tree(layout.agent_dir.join(PROFILE_DIR)),
        PathRule::Tree(layout.settings.cwd().join(CONFIG_DIR_NAME)),
        PathRule::Named(OsString::from(CONFIG_DIR_NAME)),
        PathRule::Named(OsString::from(".git")),
    ];
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
    let mut secret = vec![
        layout.agent_dir.join(crate::auth::AUTH_FILE_NAME),
        crate::auth::default_prime_cli_config_path(),
    ];
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
    PathPolicy::new(vec![workspace.to_path_buf()], protected, secret)
}

/// The path policy of a call of a session (its agent dir and settings)
/// working in `workspace` (the call's agent cwd, never a cwd the model
/// can change).
pub(crate) fn session_policy(
    agent_dir: &Path,
    settings: &EukheSettings,
    workspace: &Path,
) -> PathPolicy {
    let home = eukhe_types::platform::home_dir();
    let path = std::env::var_os("PATH");
    policy(
        &Layout {
            agent_dir,
            settings,
            home: home.as_deref(),
            path: path.as_deref(),
            env: &|name| std::env::var_os(name),
        },
        workspace,
    )
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

/// The gate of one document tool call (or one kernel `fs.*` request).
pub(crate) struct DocumentsGate {
    pub(crate) policy: PathPolicy,
    pub(crate) auto: AutoSet,
    /// The session's approval sink; `None`: no client can answer, and
    /// every access that asks is refused.
    pub(crate) sink: Option<ShellApprovalSink>,
    /// The call's id: each question's id is the call id and its number.
    pub(crate) call: String,
    pub(crate) asked: AtomicU64,
    /// The runtime the sink's answer arrives on; the gate runs on a
    /// blocking thread of it.
    pub(crate) runtime: tokio::runtime::Handle,
}

impl AccessGate for DocumentsGate {
    fn check(&self, access: Access, real: &RealPath, _display: &str) -> Result<(), String> {
        let effects = effects(&self.policy, access, real);
        if eukhe_bend::rules::shell::allows(self.auto, effects) == Gate::Unasked {
            return Ok(());
        }
        // The effects open the refusal, as a `bash` step's stop line names
        // them: the model learns which effect needs the user's approval.
        let refused = |refusal: RefusalText| Err(format!("({}) {refusal}", effects.names()));
        let Some(sink) = &self.sink else {
            return refused(RefusalText::of(Refusal::Unanswered));
        };
        let step = self.asked.fetch_add(1, Ordering::Relaxed);
        let verb = match access {
            Access::Read => "read",
            Access::List => "list",
            Access::Search => "search",
            Access::Write => "write",
        };
        let request = ShellApprovalRequest {
            request_id: format!("{}:{step}", self.call),
            step,
            command: eukhe_shell::visible(&format!("{verb} {}", real.path().display())),
            effects,
        };
        RefusalText::of_answer(self.runtime.block_on(sink(request))).map_or(Ok(()), refused)
    }
}

#[cfg(test)]
mod tests;
