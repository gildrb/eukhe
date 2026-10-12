//! The language-server table (data, `data/lsp-defaults.json`, ported from
//! omp2), root-marker discovery, file-type matching, and local executable
//! resolution. Executables are only ever found, never downloaded: a
//! project's `node_modules/.bin` first, then `PATH`.

use std::collections::BTreeMap;
use std::ffi::OsStr;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::path::{Path, PathBuf};
use std::sync::{Arc, LazyLock};

use serde::Deserialize;
use serde_json::Value;

const DEFAULT_TABLE: &str = include_str!("../data/lsp-defaults.json");
const LANGUAGE_IDS: &str = include_str!("../data/language-ids.json");

static BUILTIN: LazyLock<ServerTable> = LazyLock::new(|| {
    ServerTable::from_json(DEFAULT_TABLE).expect("the bundled LSP server table parses")
});

static EXTENSION_LANGUAGE_IDS: LazyLock<BTreeMap<String, String>> = LazyLock::new(|| {
    serde_json::from_str(LANGUAGE_IDS).expect("the bundled LSP language-id table parses")
});

/// One server declaration.
#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub(crate) struct ServerSpec {
    pub(crate) command: String,
    #[serde(default)]
    pub(crate) args: Vec<String>,
    /// Extensions (`.rs`, case-insensitive) or exact file names
    /// (`Dockerfile`).
    pub(crate) file_types: Vec<String>,
    /// Files whose presence in the root or an ancestor admits the server;
    /// `*` matches within one name (`*.csproj`).
    pub(crate) root_markers: Vec<String>,
    #[serde(default)]
    pub(crate) init_options: Option<Value>,
    #[serde(default)]
    pub(crate) settings: Option<Value>,
    /// Linters are not admitted (omp2 roster rule).
    #[serde(default)]
    pub(crate) is_linter: bool,
    /// Initialize timeout override.
    #[serde(default)]
    pub(crate) warmup_timeout_ms: Option<u64>,
}

/// The server declarations, by name.
#[derive(Debug, Clone)]
pub struct ServerTable {
    servers: BTreeMap<String, Arc<ServerSpec>>,
}

impl ServerTable {
    /// The bundled table (54 servers).
    #[must_use]
    pub fn builtin() -> Self {
        BUILTIN.clone()
    }

    /// A table from JSON in the bundled format (`{"name": {"command": ...}}`).
    ///
    /// # Errors
    ///
    /// The JSON does not match the declaration format.
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        let servers: BTreeMap<String, ServerSpec> = serde_json::from_str(json)?;
        Ok(Self {
            servers: servers
                .into_iter()
                .map(|(name, spec)| (name, Arc::new(spec)))
                .collect(),
        })
    }

    /// The non-linter declarations whose root markers match `root` or one
    /// of its ancestors, in name order.
    pub(crate) fn roster(&self, root: &Path) -> Vec<RosterEntry> {
        self.servers
            .iter()
            .filter(|(_, spec)| !spec.is_linter && has_marker_ancestor(root, &spec.root_markers))
            .map(|(name, spec)| RosterEntry {
                name: name.clone(),
                spec: Arc::clone(spec),
            })
            .collect()
    }
}

/// One server admitted for a root.
#[derive(Debug, Clone)]
pub(crate) struct RosterEntry {
    pub(crate) name: String,
    pub(crate) spec: Arc<ServerSpec>,
}

impl RosterEntry {
    /// Whether the server handles `path`: extension equality (dot- and
    /// case-insensitive) or exact file-name equality for entries without a
    /// leading dot.
    pub(crate) fn handles(&self, path: &Path) -> bool {
        let Some(name) = path.file_name().and_then(OsStr::to_str) else {
            return false;
        };
        let file_name = name.to_ascii_lowercase();
        let extension = Path::new(name)
            .extension()
            .and_then(OsStr::to_str)
            .map(str::to_ascii_lowercase);
        self.spec.file_types.iter().any(|file_type| {
            let normalized = file_type.to_ascii_lowercase();
            match normalized.strip_prefix('.') {
                Some(dotless) => extension.as_deref() == Some(dotless),
                None => {
                    extension.as_deref() == Some(normalized.as_str()) || normalized == file_name
                }
            }
        })
    }

    /// The executable and arguments to start for `root`.
    pub(crate) fn launch(&self, root: &Path) -> Result<Launch, MissingExecutable> {
        let executable = resolve_executable(
            &self.spec.command,
            root,
            std::env::var_os("PATH").as_deref(),
        )
        .ok_or_else(|| MissingExecutable {
            command: self.spec.command.clone(),
        })?;
        let pid = std::process::id().to_string();
        let args = self
            .spec
            .args
            .iter()
            .map(|arg| {
                if arg == "$PID" {
                    pid.clone()
                } else {
                    arg.clone()
                }
            })
            .collect();
        Ok(Launch { executable, args })
    }

    /// Identity of a started server for the pool: executable, arguments,
    /// settings, and initialization options.
    pub(crate) fn fingerprint(&self, launch: &Launch) -> u64 {
        let mut hasher = DefaultHasher::new();
        launch.executable.hash(&mut hasher);
        launch.args.hash(&mut hasher);
        // `Value` has no `Hash`; its JSON text is a stable stand-in.
        self.spec
            .settings
            .as_ref()
            .map(Value::to_string)
            .hash(&mut hasher);
        self.spec
            .init_options
            .as_ref()
            .map(Value::to_string)
            .hash(&mut hasher);
        hasher.finish()
    }
}

/// A resolved server command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Launch {
    pub(crate) executable: PathBuf,
    pub(crate) args: Vec<String>,
}

/// The server's executable is neither in the project's `node_modules/.bin`
/// nor on `PATH`.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{command} is not installed (looked in node_modules/.bin and PATH)")]
pub(crate) struct MissingExecutable {
    pub(crate) command: String,
}

/// The LSP language id of `path` (omp `detectLanguageId`).
pub(crate) fn language_id(path: &Path) -> String {
    let base = path
        .file_name()
        .and_then(OsStr::to_str)
        .unwrap_or_default()
        .to_ascii_lowercase();
    if base == "dockerfile" || base.starts_with("dockerfile.") || base == "containerfile" {
        return "dockerfile".to_owned();
    }
    if base == ".emacs" {
        return "emacs-lisp".to_owned();
    }
    if base == "makefile" || base == "gnumakefile" {
        return "makefile".to_owned();
    }
    if base == "justfile" {
        return "just".to_owned();
    }
    let extension = path
        .extension()
        .and_then(OsStr::to_str)
        .unwrap_or_default()
        .to_ascii_lowercase();
    if base == "cmakelists.txt" || extension == "cmake" {
        return "cmake".to_owned();
    }
    EXTENSION_LANGUAGE_IDS
        .get(&extension)
        .cloned()
        .unwrap_or_else(|| "plaintext".to_owned())
}

/// Whether `directory` or one of its ancestors holds one of `markers`.
fn has_marker_ancestor(directory: &Path, markers: &[String]) -> bool {
    directory
        .ancestors()
        .any(|ancestor| markers.iter().any(|marker| has_marker(ancestor, marker)))
}

fn has_marker(directory: &Path, marker: &str) -> bool {
    let Some((prefix, suffix)) = marker.split_once('*') else {
        return directory.join(marker).exists();
    };
    let Ok(entries) = std::fs::read_dir(directory) else {
        return false;
    };
    entries.filter_map(Result::ok).any(|entry| {
        entry.file_name().to_str().is_some_and(|name| {
            name.len() >= prefix.len() + suffix.len()
                && name.starts_with(prefix)
                && name.ends_with(suffix)
        })
    })
}

/// `command` as given when it names a path, else the project's
/// `node_modules/.bin/<command>`, else the first `PATH` entry holding it.
fn resolve_executable(command: &str, root: &Path, path: Option<&OsStr>) -> Option<PathBuf> {
    if Path::new(command).components().count() > 1 {
        let candidate = PathBuf::from(command);
        return is_executable(&candidate).then_some(candidate);
    }
    let local = root.join("node_modules/.bin").join(command);
    if is_executable(&local) {
        return Some(local);
    }
    std::env::split_paths(path?)
        .map(|directory| directory.join(command))
        .find(|candidate| is_executable(candidate))
}

#[cfg(unix)]
fn is_executable(path: &Path) -> bool {
    use std::os::unix::fs::PermissionsExt as _;
    std::fs::metadata(path)
        .is_ok_and(|metadata| metadata.is_file() && metadata.permissions().mode() & 0o111 != 0)
}

#[cfg(not(unix))]
fn is_executable(path: &Path) -> bool {
    path.is_file()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(file_types: &[&str]) -> RosterEntry {
        RosterEntry {
            name: "fixture".to_owned(),
            spec: Arc::new(ServerSpec {
                command: "fixture".to_owned(),
                args: Vec::new(),
                file_types: file_types.iter().map(|value| (*value).to_owned()).collect(),
                root_markers: Vec::new(),
                init_options: None,
                settings: None,
                is_linter: false,
                warmup_timeout_ms: None,
            }),
        }
    }

    #[test]
    fn file_types_match_extensions_and_exact_names() {
        let entry = entry(&[".rs", "Dockerfile"]);
        assert!(entry.handles(Path::new("/w/src/main.rs")));
        assert!(entry.handles(Path::new("/w/src/MAIN.RS")));
        assert!(!entry.handles(Path::new("/w/main.rson")));
        assert!(!entry.handles(Path::new("/w/.rs")));
        assert!(entry.handles(Path::new("/w/Dockerfile")));
        assert!(!entry.handles(Path::new("/w/notDockerfile")));
    }

    #[test]
    fn roster_follows_root_markers_and_skips_linters() {
        let scratch = tempfile::tempdir().unwrap();
        let root = scratch.path().join("crate");
        std::fs::create_dir_all(&root).unwrap();
        let names = |root: &Path| -> Vec<String> {
            ServerTable::builtin()
                .roster(root)
                .into_iter()
                .map(|entry| entry.name)
                .collect()
        };
        assert!(!names(&root).contains(&"rust-analyzer".to_owned()));
        std::fs::write(scratch.path().join("Cargo.toml"), "[workspace]").unwrap();
        assert!(names(&root).contains(&"rust-analyzer".to_owned()));
        std::fs::write(root.join("biome.json"), "{}").unwrap();
        assert!(!names(&root).contains(&"biome".to_owned()));
        std::fs::write(root.join("App.csproj"), "").unwrap();
        assert!(names(&root).contains(&"omnisharp".to_owned()));
    }

    #[cfg(unix)]
    #[test]
    fn project_node_modules_precede_path() {
        use std::os::unix::fs::PermissionsExt as _;
        let scratch = tempfile::tempdir().unwrap();
        let bin = scratch.path().join("node_modules/.bin");
        let on_path = scratch.path().join("path");
        std::fs::create_dir_all(&bin).unwrap();
        std::fs::create_dir_all(&on_path).unwrap();
        for directory in [&bin, &on_path] {
            let file = directory.join("tsls");
            std::fs::write(&file, "").unwrap();
            std::fs::set_permissions(&file, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        let path = std::env::join_paths([&on_path]).unwrap();
        assert_eq!(
            resolve_executable("tsls", scratch.path(), Some(&path)),
            Some(bin.join("tsls"))
        );
        std::fs::remove_file(bin.join("tsls")).unwrap();
        assert_eq!(
            resolve_executable("tsls", scratch.path(), Some(&path)),
            Some(on_path.join("tsls"))
        );
        assert_eq!(
            resolve_executable("absent", scratch.path(), Some(&path)),
            None
        );
    }
}
