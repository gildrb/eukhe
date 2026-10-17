//! Where the kernel runs (docs/harness.md S3): a local child process, or the
//! same stub under a wrapper command that reaches a container, a VM or a
//! remote machine (`docker exec -i <c>`, `podman exec -i <c>`,
//! `docker run -i --rm -v ...`, `ssh -T <host>`).
//!
//! The NDJSON protocol does not change: the wrapper carries the kernel's
//! stdin and stdout. What follows the transport:
//! - the command line (the wrapper's argv, then the kernel command);
//! - the environment: a wrapped kernel gets an explicit allow-list, never
//!   the whole host environment;
//! - the owner: a wrapped kernel watches its stdin (EOF ends it), not a
//!   host pid it cannot see;
//! - the paths: the sandbox's paths map to the host's through the shared
//!   mounts (`path_map`), and an `fs.*` host request whose path is outside
//!   every mount is rejected; "outside" is checked on the host's disk, so
//!   a symlink in a mount that points out of every mount is rejected too.

use std::io::ErrorKind;
use std::path::{Component, Path, PathBuf};

use serde::Deserialize;
use serde_json::{Map, Value};

/// The interpreter a wrapped kernel runs when the setting names none.
const DEFAULT_SANDBOX_PYTHON: &str = "python3";

/// The kernel's environment entries that hold a host path: a wrapped
/// kernel gets them mapped into the sandbox, or not at all.
const PATH_VALUED_ENV: [&str; 2] = ["EUKHE_CODING_AGENT_DIR", "EUKHE_BASH_SHELL"];

/// The environment entry that selects the runtime's owner watch.
pub const KERNEL_OWNER_ENV: &str = "EUKHE_KERNEL_OWNER";

/// [`KERNEL_OWNER_ENV`]'s value for a wrapped kernel: EOF on stdin is the
/// owner's end.
pub const KERNEL_OWNER_STDIN: &str = "stdin";

/// How the wrapper takes the kernel command.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum WrapperCommand {
    /// The wrapper runs its trailing arguments as an argv (`docker exec`,
    /// `podman exec`, `docker run`): the kernel command goes as
    /// `sh -c <script>`.
    #[default]
    Argv,
    /// The wrapper joins its trailing arguments into one remote shell line
    /// (`ssh`): the kernel command goes as one quoted script.
    Shell,
}

/// One shared mount: the same directory at `sandbox` in the sandbox and at
/// `host` on the host.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct PathMount {
    pub sandbox: PathBuf,
    pub host: PathBuf,
}

/// The `kernelTransport` setting: absent is a local child process.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct KernelTransportSettings {
    /// The wrapper's argv; the kernel command follows it.
    pub argv_prefix: Vec<String>,
    #[serde(default)]
    pub command: WrapperCommand,
    /// The interpreter in the sandbox (with eukhe-runtime installed).
    #[serde(default)]
    pub python: Option<String>,
    /// The shared mounts.
    #[serde(default)]
    pub path_map: Vec<PathMount>,
    /// Names of host environment variables passed into the sandbox.
    #[serde(default)]
    pub env: Vec<String>,
}

/// Why a `kernelTransport` setting is refused.
#[derive(Debug, thiserror::Error)]
pub enum KernelTransportError {
    #[error("kernelTransport is not valid: {0}")]
    Invalid(#[from] serde_json::Error),
    #[error("kernelTransport.argvPrefix is empty: name the wrapper command")]
    EmptyPrefix,
    #[error("kernelTransport.pathMap entry {} must be absolute on both sides", .0.display())]
    RelativeMount(PathBuf),
    #[error("kernelTransport.env entry {0:?} is not an environment variable name")]
    BadEnvName(String),
}

/// A path the kernel transport cannot map.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum PathMapError {
    #[error("{} is outside every path the kernel shares with the host", .0.display())]
    Outside(PathBuf),
    #[error("{0} is relative to the sandbox's home, which the host does not share")]
    Home(String),
    #[error("the request has no absolute cwd")]
    NoCwd,
    #[error("cannot resolve {} on the host: {}", .0.display(), .1)]
    Unresolved(PathBuf, String),
}

/// The shared mounts of a wrapped kernel.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PathMap {
    mounts: Vec<PathMount>,
}

/// One side of a [`PathMount`].
#[derive(Debug, Clone, Copy)]
enum Side {
    Sandbox,
    Host,
}

impl PathMount {
    fn side(&self, side: Side) -> &Path {
        match side {
            Side::Sandbox => &self.sandbox,
            Side::Host => &self.host,
        }
    }
}

impl PathMap {
    #[must_use]
    pub fn new(mounts: Vec<PathMount>) -> Self {
        Self { mounts }
    }

    /// The host path of the absolute sandbox path `sandbox`.
    ///
    /// # Errors
    ///
    /// [`PathMapError::Outside`] when no mount holds it.
    pub fn to_host(&self, sandbox: &Path) -> Result<PathBuf, PathMapError> {
        self.translate(sandbox, Side::Sandbox, Side::Host)
    }

    /// The sandbox path of the absolute host path `host`.
    ///
    /// # Errors
    ///
    /// [`PathMapError::Outside`] when no mount holds it.
    pub fn to_sandbox(&self, host: &Path) -> Result<PathBuf, PathMapError> {
        self.translate(host, Side::Host, Side::Sandbox)
    }

    /// The mount holding `path` on `side`: the deepest one, so a nested
    /// mount wins over its parent.
    fn mount_of(&self, path: &Path, side: Side) -> Option<(usize, PathBuf)> {
        let normal = normalize(path);
        self.mounts
            .iter()
            .enumerate()
            .filter_map(|(index, mount)| {
                normal
                    .strip_prefix(mount.side(side))
                    .ok()
                    .map(|rest| (index, rest.to_path_buf()))
            })
            .max_by_key(|(index, _)| self.mounts[*index].side(side).components().count())
    }

    fn translate(&self, path: &Path, from: Side, to: Side) -> Result<PathBuf, PathMapError> {
        if !path.is_absolute() {
            return Err(PathMapError::Outside(path.to_path_buf()));
        }
        let (index, rest) = self
            .mount_of(path, from)
            .ok_or_else(|| PathMapError::Outside(path.to_path_buf()))?;
        let base = self.mounts[index].side(to);
        Ok(if rest.as_os_str().is_empty() {
            base.to_path_buf()
        } else {
            base.join(rest)
        })
    }

    /// One path argument of an `fs.*` request, from the sandbox's view to
    /// the host's. An internal URL passes. A relative path that stays in
    /// the mount of `sandbox_cwd` passes as written (the host resolves it
    /// against the mapped cwd); any other path becomes its host path.
    /// The path the host opens must stay in a mount after its symlinks
    /// resolve.
    fn path_arg_to_host(&self, sandbox_cwd: &Path, text: &str) -> Result<String, PathMapError> {
        if text.contains("://") {
            return Ok(text.to_owned());
        }
        if text.starts_with('~') {
            return Err(PathMapError::Home(text.to_owned()));
        }
        let written = Path::new(text);
        let joined = sandbox_cwd.join(written);
        let host = self.to_host(&joined)?;
        let as_written = !written.is_absolute()
            && self
                .mount_of(&joined, Side::Sandbox)
                .map(|(index, _)| index)
                == self
                    .mount_of(sandbox_cwd, Side::Sandbox)
                    .map(|(index, _)| index);
        if as_written {
            // The host opens the text as written in the mapped cwd: check
            // that path, with a `..` after a symlink resolved on disk.
            self.require_inside_on_disk(&self.to_host(sandbox_cwd)?.join(written), &joined)?;
            Ok(text.to_owned())
        } else {
            self.require_inside_on_disk(&host, &joined)?;
            Ok(host.to_string_lossy().into_owned())
        }
    }

    /// [`PathMapError::Outside`] (naming the sandbox path `sandbox`) when
    /// the host path `host`, with its existing part resolved on disk, is
    /// in no mount's resolved host directory.
    fn require_inside_on_disk(&self, host: &Path, sandbox: &Path) -> Result<(), PathMapError> {
        let resolved = resolve_on_disk(host)?;
        let mounts = self
            .mounts
            .iter()
            .map(|mount| resolve_on_disk(&mount.host))
            .collect::<Result<Vec<PathBuf>, PathMapError>>()?;
        if mounts.iter().any(|mount| resolved.starts_with(mount)) {
            Ok(())
        } else {
            Err(PathMapError::Outside(sandbox.to_path_buf()))
        }
    }

    /// Map the `cwd` and the path arguments of one `fs.*` host request
    /// (`data`: `{type, cwd, args}`) from the sandbox's paths to the
    /// host's.
    ///
    /// # Errors
    ///
    /// A cwd or a path outside every mount (also after its symlinks
    /// resolve on the host), one relative to the sandbox's home, or one
    /// the host cannot resolve.
    pub fn fs_request_to_host(
        &self,
        request_type: &str,
        data: &mut Map<String, Value>,
    ) -> Result<(), PathMapError> {
        let sandbox_cwd = data
            .get("cwd")
            .and_then(Value::as_str)
            .map(PathBuf::from)
            .filter(|cwd| cwd.is_absolute())
            .ok_or(PathMapError::NoCwd)?;
        let host_cwd = self.to_host(&sandbox_cwd)?;
        self.require_inside_on_disk(&host_cwd, &sandbox_cwd)?;
        data.insert(
            "cwd".to_owned(),
            Value::String(host_cwd.to_string_lossy().into_owned()),
        );
        let Some(Value::Object(args)) = data.get_mut("args") else {
            return Ok(());
        };
        for (key, value) in args.iter_mut() {
            match fs_argument(request_type, key) {
                FsArgument::Path => self.map_path_value(&sandbox_cwd, value)?,
                FsArgument::Patch => {
                    if let Value::String(patch) = value {
                        *patch = self.patch_to_host(&sandbox_cwd, patch)?;
                    }
                }
                FsArgument::Other => {}
            }
        }
        Ok(())
    }

    /// A path argument: one path, `;`-separated paths, or a list of them.
    fn map_path_value(&self, sandbox_cwd: &Path, value: &mut Value) -> Result<(), PathMapError> {
        match value {
            Value::String(text) => {
                let mapped: Result<Vec<String>, PathMapError> = text
                    .split(';')
                    .map(|part| {
                        let trimmed = part.trim();
                        if trimmed.is_empty() {
                            Ok(part.to_owned())
                        } else {
                            self.path_arg_to_host(sandbox_cwd, trimmed)
                        }
                    })
                    .collect();
                *text = mapped?.join(";");
                Ok(())
            }
            Value::Array(items) => items
                .iter_mut()
                .try_for_each(|item| self.map_path_value(sandbox_cwd, item)),
            Value::Null | Value::Bool(_) | Value::Number(_) | Value::Object(_) => Ok(()),
        }
    }

    /// An `edit` patch: the path of each `[PATH]`/`[PATH#TAG]` section
    /// header and of each `MV DEST` row.
    fn patch_to_host(&self, sandbox_cwd: &Path, patch: &str) -> Result<String, PathMapError> {
        let mut out = String::with_capacity(patch.len());
        for line in patch.split_inclusive('\n') {
            let body = line.trim_end_matches(['\n', '\r']);
            let ending = &line[body.len()..];
            let trimmed = body.trim();
            if let Some(inner) = trimmed.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
                let (section, tag) = match inner.rsplit_once('#') {
                    Some((section, tag))
                        if tag.len() == 4 && tag.bytes().all(|byte| byte.is_ascii_hexdigit()) =>
                    {
                        (section, Some(tag))
                    }
                    Some(_) | None => (inner, None),
                };
                let mapped = self.path_arg_to_host(sandbox_cwd, section.trim())?;
                out.push('[');
                out.push_str(&mapped);
                if let Some(tag) = tag {
                    out.push('#');
                    out.push_str(tag);
                }
                out.push(']');
            } else if let Some(dest) = trimmed.strip_prefix("MV ") {
                let dest = dest.trim();
                let unquoted = dest
                    .strip_prefix('"')
                    .and_then(|d| d.strip_suffix('"'))
                    .unwrap_or(dest);
                let mapped = self.path_arg_to_host(sandbox_cwd, unquoted)?;
                out.push_str("MV ");
                if mapped.contains(' ') {
                    out.push('"');
                    out.push_str(&mapped);
                    out.push('"');
                } else {
                    out.push_str(&mapped);
                }
            } else {
                out.push_str(body);
            }
            out.push_str(ending);
        }
        Ok(out)
    }

    /// Map the host paths of an `fs.*` reply (`absolute`, `destination`)
    /// back to the sandbox's paths. A path no mount holds stays as the
    /// host wrote it.
    pub fn fs_reply_to_sandbox(&self, reply: &mut Value) {
        match reply {
            Value::Object(fields) => {
                for (key, value) in fields.iter_mut() {
                    let host_path = matches!(key.as_str(), "absolute" | "destination")
                        .then(|| value.as_str().map(PathBuf::from))
                        .flatten();
                    match host_path {
                        Some(host) => {
                            if let Ok(sandbox) = self.to_sandbox(&host) {
                                *value = Value::String(sandbox.to_string_lossy().into_owned());
                            }
                        }
                        None => self.fs_reply_to_sandbox(value),
                    }
                }
            }
            Value::Array(items) => items
                .iter_mut()
                .for_each(|item| self.fs_reply_to_sandbox(item)),
            Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => {}
        }
    }
}

/// What one `fs.*` argument holds; the keys are the functions' dialects
/// (`durable/documents/contract.rs`): the canonical key and its aliases.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FsArgument {
    Path,
    Patch,
    Other,
}

fn fs_argument(request_type: &str, key: &str) -> FsArgument {
    const PATH: [&str; 5] = ["path", "file_path", "filepath", "file", "filename"];
    const PATCH: [&str; 5] = ["input", "patch", "diff", "edits", "payload"];
    let more_paths: &[&str] = if request_type == "fs.grep" {
        &["paths", "dir", "directory"]
    } else if request_type == "fs.glob" {
        &["pattern", "patterns", "glob", "dir", "directory"]
    } else {
        &[]
    };
    if request_type == "fs.edit" && PATCH.contains(&key) {
        FsArgument::Patch
    } else if PATH.contains(&key) || more_paths.contains(&key) {
        FsArgument::Path
    } else {
        FsArgument::Other
    }
}

/// `path` with `.` and `..` resolved lexically (no filesystem access).
fn normalize(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            Component::ParentDir => {
                out.pop();
            }
            Component::CurDir => {}
            Component::Prefix(_) | Component::RootDir | Component::Normal(_) => {
                out.push(component);
            }
        }
    }
    out
}

/// The absolute `path` as the host's filesystem resolves it: its longest
/// existing ancestor canonicalized (symlinks and `..` resolved on disk),
/// then the rest of `path` resolved lexically.
fn resolve_on_disk(path: &Path) -> Result<PathBuf, PathMapError> {
    let components: Vec<Component<'_>> = path.components().collect();
    for existing in (1..=components.len()).rev() {
        let ancestor: PathBuf = components[..existing].iter().collect();
        match std::fs::canonicalize(&ancestor) {
            Ok(real) => {
                let rest: PathBuf = components[existing..].iter().collect();
                return Ok(normalize(&real.join(rest)));
            }
            Err(error)
                if matches!(error.kind(), ErrorKind::NotFound | ErrorKind::NotADirectory) => {}
            Err(error) => {
                return Err(PathMapError::Unresolved(
                    path.to_path_buf(),
                    error.to_string(),
                ))
            }
        }
    }
    Err(PathMapError::Outside(path.to_path_buf()))
}

/// A wrapped kernel: the wrapper, the interpreter in the sandbox, the
/// shared mounts and the host variables it may see.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelWrapper {
    pub argv_prefix: Vec<String>,
    pub command: WrapperCommand,
    pub python: String,
    pub path_map: PathMap,
    pub env: Vec<String>,
}

/// Where the kernel runs.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum KernelTransport {
    /// A child process of the host in its own process group, with the
    /// host's environment.
    #[default]
    Local,
    /// The kernel command runs under `argv_prefix`; the paths map through
    /// `path_map`.
    Wrapped(KernelWrapper),
}

impl KernelTransport {
    /// The transport the `kernelTransport` setting names: `None` (or JSON
    /// `null`) is [`KernelTransport::Local`].
    ///
    /// # Errors
    ///
    /// The setting does not parse, names no wrapper, has a relative mount
    /// or an entry of `env` that is not a variable name.
    pub fn from_setting(value: Option<&Value>) -> Result<Self, KernelTransportError> {
        let Some(value) = value.filter(|value| !value.is_null()) else {
            return Ok(Self::Local);
        };
        let settings: KernelTransportSettings = serde_json::from_value(value.clone())?;
        if settings.argv_prefix.is_empty() {
            return Err(KernelTransportError::EmptyPrefix);
        }
        if let Some(mount) = settings
            .path_map
            .iter()
            .find(|mount| !mount.sandbox.is_absolute() || !mount.host.is_absolute())
        {
            return Err(KernelTransportError::RelativeMount(mount.sandbox.clone()));
        }
        if let Some(name) = settings.env.iter().find(|name| !is_env_name(name)) {
            return Err(KernelTransportError::BadEnvName(name.clone()));
        }
        Ok(Self::Wrapped(KernelWrapper {
            argv_prefix: settings.argv_prefix,
            command: settings.command,
            python: settings
                .python
                .unwrap_or_else(|| DEFAULT_SANDBOX_PYTHON.to_owned()),
            path_map: PathMap::new(
                settings
                    .path_map
                    .into_iter()
                    .map(|mount| PathMount {
                        sandbox: normalize(&mount.sandbox),
                        host: normalize(&mount.host),
                    })
                    .collect(),
            ),
            env: settings.env,
        }))
    }
}

fn is_env_name(name: &str) -> bool {
    let mut bytes = name.bytes();
    bytes
        .next()
        .is_some_and(|first| first == b'_' || first.is_ascii_alphabetic())
        && bytes.all(|byte| byte == b'_' || byte.is_ascii_alphanumeric())
}

/// The kernel command of a wrapped kernel, before it reaches the wrapper.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WrappedLaunch {
    /// The full argv: the wrapper's, then the kernel command.
    pub argv: Vec<String>,
    /// Kernel environment entries left out: their host path is outside
    /// every mount.
    pub unmapped_env: Vec<String>,
}

impl KernelWrapper {
    /// The argv that starts the kernel in the sandbox: `cd` to the mapped
    /// `cwd`, then `exec env <entries> <python> -P -m rlm.repl`. The
    /// entries are `kernel_env` (path-valued ones mapped, unmappable ones
    /// left out), the allow-listed host variables, the stdin owner mode,
    /// and `PYTHONPATH` with the mapped `python_paths` in front of the
    /// sandbox's own.
    ///
    /// # Errors
    ///
    /// The cwd is outside every mount.
    pub fn launch(
        &self,
        cwd: &Path,
        kernel_env: &[(String, String)],
        host_env: impl Fn(&str) -> Option<String>,
        python_paths: &[PathBuf],
    ) -> Result<WrappedLaunch, PathMapError> {
        let sandbox_cwd = self.path_map.to_sandbox(cwd)?;
        let mut unmapped_env = Vec::new();
        let mut assignments: Vec<String> = Vec::new();
        for (key, value) in kernel_env {
            if PATH_VALUED_ENV.contains(&key.as_str()) {
                match self.path_map.to_sandbox(Path::new(value)) {
                    Ok(mapped) => {
                        assignments.push(shell_quote(&format!("{key}={}", mapped.display())));
                    }
                    Err(_) => unmapped_env.push(key.clone()),
                }
            } else {
                assignments.push(shell_quote(&format!("{key}={value}")));
            }
        }
        for name in &self.env {
            if let Some(value) = host_env(name) {
                assignments.push(shell_quote(&format!("{name}={value}")));
            }
        }
        assignments.push(shell_quote(&format!(
            "{KERNEL_OWNER_ENV}={KERNEL_OWNER_STDIN}"
        )));
        let sandbox_paths: Vec<String> = python_paths
            .iter()
            .filter_map(|path| self.path_map.to_sandbox(path).ok())
            .map(|path| path.to_string_lossy().into_owned())
            .collect();
        if !sandbox_paths.is_empty() {
            assignments.push(format!(
                "PYTHONPATH={}\"${{PYTHONPATH:+:$PYTHONPATH}}\"",
                shell_quote(&sandbox_paths.join(":"))
            ));
        }
        let script = format!(
            "cd {} && exec env {} {} -P -m rlm.repl",
            shell_quote(&sandbox_cwd.to_string_lossy()),
            assignments.join(" "),
            shell_quote(&self.python),
        );
        let mut argv = self.argv_prefix.clone();
        match self.command {
            WrapperCommand::Argv => argv.extend(["sh".to_owned(), "-c".to_owned(), script]),
            WrapperCommand::Shell => argv.push(script),
        }
        Ok(WrappedLaunch { argv, unmapped_env })
    }
}

/// `text` as one POSIX shell word.
fn shell_quote(text: &str) -> String {
    if !text.is_empty()
        && text
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"_-./=:,+@%".contains(&byte))
    {
        return text.to_owned();
    }
    format!("'{}'", text.replace('\'', "'\\''"))
}

#[cfg(test)]
mod tests;
