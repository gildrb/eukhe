//! The tool trust a child's copy keeps from its parent's workspace.
//!
//! mise keys its trust by the config file's path: a `mise.toml` the user
//! trusted in the parent's workspace is untrusted in the child's copy, so
//! every mise-activated command there fails ("Config files in
//! .../tree/mise.toml are not trusted"). At the create the host asks mise
//! which config roots of the parent are trusted (`mise trust --show`,
//! without input, bounded in time) and records the copy's config files
//! under them ([`carried`]); the child's tools get them as
//! `MISE_TRUSTED_CONFIG_PATHS` ([`tool_env`]). A config the parent does
//! not trust stays untrusted in the copy, and nothing is written to mise's
//! own trust store.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::path::{Component, Path, PathBuf};
use std::process::Stdio;
use std::time::Duration;

use tokio::process::Command;

/// The variable that lists the config files mise trusts beside its store.
pub(super) const TRUSTED_CONFIG_PATHS: &str = "MISE_TRUSTED_CONFIG_PATHS";

/// The program asked for the parent's trust.
pub(super) const MISE: &str = "mise";

/// How long the trust query may take before the copy carries no trust.
const SHOW_TIMEOUT: Duration = Duration::from_secs(10);

/// The directory whose trust covers the mise config file `path` (relative
/// to the workspace): the directory of `mise.toml`, `.mise.toml`,
/// `mise.local.toml` and `mise.<env>.toml`, the directory above
/// `mise/config.toml`, `.mise/config.toml` and `.config/mise.toml`, two
/// above `.config/mise/config.toml`, three above
/// `.config/mise/conf.d/<name>.toml`; `None` for any other file.
#[must_use]
pub(super) fn config_root(path: &Path) -> Option<PathBuf> {
    let names: Vec<&OsStr> = path
        .components()
        .map(|part| match part {
            Component::Normal(name) => Some(name),
            Component::Prefix(_)
            | Component::RootDir
            | Component::CurDir
            | Component::ParentDir => None,
        })
        .collect::<Option<_>>()?;
    let (file, dirs) = names.split_last()?;
    let file = file.to_str()?;
    let up = match (dirs, file) {
        ([.., config, mise, conf], _)
            if *config == ".config" && *mise == "mise" && *conf == "conf.d" && is_toml(file) =>
        {
            3
        }
        ([.., config, mise], "config.toml" | "config.local.toml")
            if *config == ".config" && *mise == "mise" =>
        {
            2
        }
        ([.., config], "mise.toml") if *config == ".config" => 1,
        ([.., mise], "config.toml" | "config.local.toml")
            if *mise == "mise" || *mise == ".mise" =>
        {
            1
        }
        (_, file) if is_root_config(file) => 0,
        _ => return None,
    };
    let root: PathBuf = dirs.get(..dirs.len().checked_sub(up)?)?.iter().collect();
    Some(root)
}

fn is_toml(name: &str) -> bool {
    Path::new(name)
        .extension()
        .is_some_and(|extension| extension == "toml")
}

/// `mise.toml`, `.mise.toml`, and their `.local`/`.<env>` forms.
fn is_root_config(name: &str) -> bool {
    let bare = name.strip_prefix('.').unwrap_or(name);
    bare.strip_prefix("mise")
        .and_then(|rest| rest.strip_suffix(".toml"))
        .is_some_and(|middle| middle.is_empty() || (middle.len() > 1 && middle.starts_with('.')))
}

/// The directories `mise trust --show` reports trusted: its lines are
/// `<dir>: trusted` or `<dir>: untrusted`, `~` standing for `home`.
#[must_use]
pub(super) fn trusted_dirs(show: &str, home: Option<&Path>) -> BTreeSet<PathBuf> {
    show.lines()
        .filter_map(|line| line.trim().rsplit_once(": "))
        .filter(|(_, status)| *status == "trusted")
        .filter_map(|(dir, _)| match (dir.strip_prefix('~'), home) {
            (Some(rest), Some(home)) => Some(home.join(rest.trim_start_matches('/'))),
            (Some(_), None) => None,
            (None, _) => Some(PathBuf::from(dir)),
        })
        .collect()
}

/// The copy's config files (under `tree`) whose originals the parent's
/// workspace `parent` trusts: of `paths` (the copied paths, relative),
/// each mise config file whose root `program trust --show` reports
/// trusted when asked in that root. A program that is missing, fails or
/// takes past [`SHOW_TIMEOUT`] carries nothing.
#[tracing::instrument(level = "debug", skip(paths))]
pub(super) async fn carried(
    program: &OsStr,
    parent: &Path,
    tree: &Path,
    paths: &BTreeSet<PathBuf>,
) -> Vec<PathBuf> {
    let mut roots: BTreeMap<PathBuf, Vec<&PathBuf>> = BTreeMap::new();
    for path in paths {
        if let Some(root) = config_root(path) {
            roots.entry(root).or_default().push(path);
        }
    }
    let home = std::env::var_os("HOME").map(PathBuf::from);
    let mut carried = Vec::new();
    for (root, files) in roots {
        let dir = parent.join(&root);
        let Some(show) = show(program, &dir).await else {
            continue;
        };
        let trusted = trusted_dirs(&show, home.as_deref());
        if trusted.iter().any(|trusted| same_dir(trusted, &dir)) {
            carried.extend(files.into_iter().map(|file| tree.join(file)));
        }
    }
    carried
}

/// `a` and `b` name one directory (as given, else resolved).
fn same_dir(a: &Path, b: &Path) -> bool {
    a == b
        || matches!(
            (a.canonicalize(), b.canonicalize()),
            (Ok(a), Ok(b)) if a == b
        )
}

/// The output of `program trust --show` run in `dir` without input;
/// `None` when it does not start, fails or overruns.
async fn show(program: &OsStr, dir: &Path) -> Option<String> {
    let output = Command::new(program)
        .args(["trust", "--show"])
        .current_dir(dir)
        .stdin(Stdio::null())
        .stderr(Stdio::null())
        .kill_on_drop(true)
        .output();
    match tokio::time::timeout(SHOW_TIMEOUT, output).await {
        Ok(Ok(output)) if output.status.success() => {
            Some(String::from_utf8_lossy(&output.stdout).into_owned())
        }
        Ok(Ok(output)) => {
            tracing::debug!(dir = %dir.display(), status = %output.status, "mise trust --show failed: the copy carries no trust");
            None
        }
        Ok(Err(error)) => {
            tracing::debug!(dir = %dir.display(), %error, "mise did not run: the copy carries no trust");
            None
        }
        Err(_elapsed) => {
            tracing::warn!(dir = %dir.display(), "mise trust --show overran: the copy carries no trust");
            None
        }
    }
}

/// The variable a command in `dir` gets so mise trusts the copy's config
/// files its parent trusted: `trusted` joined with `:`, then `inherited`
/// (the host's own value); `None` when `trusted` is empty.
#[must_use]
pub(super) fn trusted_value(trusted: &[PathBuf], inherited: Option<&OsStr>) -> Option<String> {
    if trusted.is_empty() {
        return None;
    }
    let mut parts: Vec<String> = trusted
        .iter()
        .map(|path| path.to_string_lossy().into_owned())
        .collect();
    if let Some(inherited) = inherited.filter(|value| !value.is_empty()) {
        parts.push(inherited.to_string_lossy().into_owned());
    }
    Some(parts.join(":"))
}
