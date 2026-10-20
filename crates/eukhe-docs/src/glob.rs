//! `glob`: files and directories matching globs, newest first, rendered as a
//! prefix-folded listing.
//!
//! Ported from omp `crates/tools/src/glob.rs` (request, ranking, rendering)
//! and `crates/envd/src/tool_search.rs` (`glob_blocking`: targets and walk).

use std::{
    cmp,
    collections::HashSet,
    fmt::Write as _,
    fs,
    num::NonZeroUsize,
    path::{Component, Path, PathBuf},
    time::{Duration, Instant, UNIX_EPOCH},
};

use globset::GlobBuilder;

use crate::{
    gate::{Access, AccessGate},
    notice::{Notice, NoticeKind},
    path_tree::format_grouped_paths,
    scope::{
        has_glob_chars, is_missing, normalize_path_input, resolve_input_path,
        split_top_level_semicolons, workspace_relative,
    },
};

/// Maximum number of paths one `glob` returns; also the default.
pub const MAX_GLOB_LIMIT: usize = 200;
/// Maximum time allotted to the traversal.
const DEFAULT_TIMEOUT: Duration = Duration::from_secs(5);

/// One `glob` call.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GlobRequest {
    /// Globs, files, or directories relative to the working directory,
    /// separated by `;` (`src/**/*.ts; test/**/*.ts`). A bare glob such as
    /// `*.rs` matches at any depth; a directory lists everything under it.
    pub path: String,
    /// Include dot-prefixed files and directories.
    pub hidden: bool,
    /// Respect `.gitignore`, `.ignore`, git excludes, and the global gitignore.
    pub gitignore: bool,
    /// Paths returned, at most [`MAX_GLOB_LIMIT`] (the default).
    pub limit: Option<NonZeroUsize>,
}

/// A failed `glob`. `Display` is the model-facing message.
#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum GlobError {
    /// The input contained no usable path target.
    #[error("`path` must contain non-empty globs or paths")]
    EmptyPath,
    /// A traversal would start at the filesystem root.
    #[error("Searching from root directory '/' is not allowed")]
    RootSearch,
    /// Every target, or the sole target, was missing.
    #[error("Path not found: {}", .paths.join(", "))]
    PathNotFound {
        /// Missing targets in request order.
        paths: Vec<String>,
    },
    /// A glob's base is a file, not a directory.
    #[error("Path is not a directory: {path}")]
    PathNotDirectory {
        /// The rejected target.
        path: String,
    },
    /// A `scheme://` target, which has no local filesystem walk.
    #[error("{scheme}:// targets are not supported yet")]
    UnsupportedScheme {
        /// Lowercase scheme without punctuation.
        scheme: String,
    },
    /// A glob did not compile.
    #[error("invalid glob pattern {pattern}: {message}")]
    InvalidPattern {
        /// The rejected pattern.
        pattern: String,
        /// The parser's explanation.
        message: String,
    },
    /// The host's gate refused a target.
    #[error("Did not list {path}: {reason}")]
    Refused {
        /// The target as the model wrote it.
        path: String,
        /// Why the host's gate refused it.
        reason: String,
    },
    /// The filesystem failed.
    #[error("{message}")]
    Workspace {
        /// The failure.
        message: String,
    },
}

/// One matching path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GlobMatch {
    /// Path relative to the working directory (absolute outside it), `/`
    /// separated; directories end in `/`.
    pub path: String,
    /// Modification time in milliseconds since the Unix epoch; 0 when unknown.
    pub modified_ms: u64,
    /// Whether the path names a directory.
    pub is_dir: bool,
}

/// A `glob` result: typed matches, notices, and the model-facing text.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GlobOutput {
    /// Newest first, then by path.
    pub matches: Vec<GlobMatch>,
    /// Targets skipped because they were missing.
    pub missing_paths: Vec<String>,
    /// Whether the deadline ended the walk.
    pub timed_out: bool,
    /// Whether matches were left out (deadline or limit).
    pub truncated: bool,
    /// Timeout, limit, and missing-path notices.
    pub notices: Vec<Notice>,
    /// Model-facing listing: `# dir/` headings and bare file names.
    pub text: String,
}

impl GlobOutput {
    /// The text followed by one `<diag>` line per notice.
    #[must_use]
    pub fn render(&self) -> String {
        let mut rendered = self.text.clone();
        for notice in &self.notices {
            if !rendered.is_empty() {
                rendered.push('\n');
            }
            let _ = write!(rendered, "{notice}");
        }
        rendered
    }
}

/// Lists paths matching `request.path` under `cwd`, each target after
/// `gate` let the list of its real path.
///
/// # Errors
/// [`GlobError`] for an empty or root target, a URL target, every target
/// missing, a file used as a glob base, a bad glob, a target the gate
/// refused, or a filesystem failure.
pub(crate) fn glob(
    cwd: &Path,
    request: &GlobRequest,
    gate: &dyn AccessGate,
) -> Result<GlobOutput, GlobError> {
    glob_until(cwd, request, gate, DEFAULT_TIMEOUT)
}

struct Target {
    pattern: Option<String>,
    is_dir: bool,
    canonical: PathBuf,
    visible_root: Option<PathBuf>,
}

fn glob_until(
    cwd: &Path,
    request: &GlobRequest,
    gate: &dyn AccessGate,
    timeout: Duration,
) -> Result<GlobOutput, GlobError> {
    let limit = request
        .limit
        .map_or(MAX_GLOB_LIMIT, NonZeroUsize::get)
        .min(MAX_GLOB_LIMIT);
    let raw = normalize_path_input(&request.path);
    if raw.is_empty() {
        return Err(GlobError::EmptyPath);
    }
    let root = fs::canonicalize(cwd).map_err(workspace_error)?;
    let inputs = split_inputs(&root, raw)?;
    if inputs
        .iter()
        .any(|input| input.bytes().all(|byte| byte == b'/'))
    {
        return Err(GlobError::RootSearch);
    }
    if let Some(scheme) = inputs.iter().find_map(|input| crate::url::scheme_of(input)) {
        return Err(GlobError::UnsupportedScheme { scheme });
    }

    let multi_target = inputs.len() > 1;
    let mut missing_paths = Vec::new();
    let mut targets = Vec::new();
    let mut found_paths = 0_usize;
    for input in inputs {
        let literal = resolve_input_path(&root, &input);
        let (base, pattern, target_path, metadata) = match fs::metadata(&literal) {
            Ok(metadata) => (input.clone(), None, literal, metadata),
            Err(error) if is_missing(&error) => {
                let (base, pattern) = parse_find_pattern(&input);
                if base.bytes().all(|byte| byte == b'/') {
                    return Err(GlobError::RootSearch);
                }
                let target_path = resolve_input_path(&root, &base);
                match fs::metadata(&target_path) {
                    Ok(metadata) => (base, pattern, target_path, metadata),
                    Err(error) if is_missing(&error) => {
                        missing_paths.push(input);
                        continue;
                    }
                    Err(error) => return Err(workspace_error(error)),
                }
            }
            Err(error) => return Err(workspace_error(error)),
        };
        let canonical = fs::canonicalize(&target_path).map_err(workspace_error)?;
        let resolved = eukhe_types::path_policy::resolve(&canonical);
        gate.check(Access::List, &resolved, &input)
            .map_err(|reason| GlobError::Refused {
                path: input.clone(),
                reason,
            })?;
        // Walk the canonical root, but keep an external absolute root's spelling
        // for display, normalizing only lexical `.` and `..`.
        let visible_root = (Path::new(&base).is_absolute() && !canonical.starts_with(&root))
            .then(|| lexical_normalize_absolute(&target_path));
        found_paths += 1;
        if (!metadata.is_file() && !metadata.is_dir()) || (pattern.is_some() && !metadata.is_dir())
        {
            if multi_target {
                continue;
            }
            return Err(GlobError::PathNotDirectory { path: input });
        }
        targets.push(Target {
            pattern,
            is_dir: metadata.is_dir(),
            canonical,
            visible_root,
        });
    }
    if targets.is_empty() && found_paths == 0 {
        return Err(GlobError::PathNotFound {
            paths: missing_paths,
        });
    }

    let deadline = Instant::now() + timeout;
    let mut matches = Vec::new();
    let mut truncated = false;
    let mut timed_out = false;
    for target in targets {
        if Instant::now() >= deadline {
            timed_out = true;
            break;
        }
        if !target.is_dir {
            let metadata = fs::metadata(&target.canonical).map_err(workspace_error)?;
            matches.push(GlobMatch {
                path: display_path(
                    &root,
                    &target.canonical,
                    target.visible_root.as_deref(),
                    &target.canonical,
                )?,
                modified_ms: modified_ms(&metadata),
                is_dir: false,
            });
            continue;
        }
        let pattern = target.pattern.as_deref().unwrap_or("**/*");
        let outcome = walk_target(&root, &target, pattern, request, limit, deadline)?;
        matches.extend(outcome.matches);
        truncated |= outcome.truncated;
        if outcome.timed_out {
            timed_out = true;
            break;
        }
    }

    matches.sort_by(|left, right| compare_rank(right, left));
    let mut seen = HashSet::with_capacity(matches.len());
    matches.retain(|entry| seen.insert(entry.path.clone()));
    if matches.len() > limit {
        truncated = true;
        matches.truncate(limit);
    }

    let mut notices = Vec::new();
    if timed_out {
        let millis = timeout.as_millis();
        let elapsed = if millis.is_multiple_of(1_000) {
            format!("{}s", millis / 1_000)
        } else {
            format!("{:.1}s", timeout.as_secs_f64())
        };
        notices.push(Notice::warn(
            NoticeKind::Timeout,
            format!(
                "Glob reached its {elapsed} timeout after finding {} partial matches",
                matches.len()
            ),
        ));
    }
    if truncated {
        notices.push(Notice {
            continuation: Some(format!("limit={}", limit.saturating_mul(2))),
            ..Notice::info(
                NoticeKind::LimitReached,
                format!("{limit} result limit reached"),
            )
        });
    }
    if !missing_paths.is_empty() {
        notices.push(Notice::warn(
            NoticeKind::MissingPaths,
            missing_paths.join(", "),
        ));
    }
    let text = if matches.is_empty() {
        if timed_out {
            String::new()
        } else {
            "No files found matching pattern".to_owned()
        }
    } else {
        let paths: Vec<&str> = matches.iter().map(|entry| entry.path.as_str()).collect();
        format_grouped_paths(&paths)
    };
    Ok(GlobOutput {
        matches,
        missing_paths,
        timed_out,
        truncated: truncated || timed_out,
        notices,
        text,
    })
}

/// The `;`-separated inputs; one input when the whole spelling exists or has
/// no top-level `;`.
fn split_inputs(root: &Path, raw: &str) -> Result<Vec<String>, GlobError> {
    if fs::metadata(resolve_input_path(root, raw)).is_ok() {
        return Ok(vec![raw.to_owned()]);
    }
    let parts = split_top_level_semicolons(raw);
    if parts.len() == 1 {
        return Ok(vec![raw.to_owned()]);
    }
    let inputs: Vec<String> = parts
        .into_iter()
        .map(normalize_path_input)
        .filter(|entry| !entry.is_empty())
        .map(str::to_owned)
        .collect();
    if inputs.is_empty() {
        Err(GlobError::EmptyPath)
    } else {
        Ok(inputs)
    }
}

/// Splits an input at its first glob segment into a base directory and a
/// pattern; a glob in the first segment matches at any depth under `.`.
/// Without a glob, the input is the base and the pattern is `None`.
fn parse_find_pattern(input: &str) -> (String, Option<String>) {
    let normalized = input.replace('\\', "/");
    let segments: Vec<&str> = normalized.split('/').collect();
    let Some(first_glob) = segments.iter().position(|segment| has_glob_chars(segment)) else {
        return (normalized, None);
    };
    if first_glob == 0 {
        let pattern = if normalized.starts_with("**/") {
            normalized
        } else {
            format!("**/{normalized}")
        };
        return (".".to_owned(), Some(pattern));
    }
    (
        segments[..first_glob].join("/"),
        Some(segments[first_glob..].join("/")),
    )
}

struct WalkOutcome {
    matches: Vec<GlobMatch>,
    truncated: bool,
    timed_out: bool,
}

fn walk_target(
    root: &Path,
    target: &Target,
    pattern: &str,
    request: &GlobRequest,
    limit: usize,
    deadline: Instant,
) -> Result<WalkOutcome, GlobError> {
    let pattern_matcher = GlobBuilder::new(pattern)
        .literal_separator(true)
        .build()
        .map_err(|error| GlobError::InvalidPattern {
            pattern: pattern.to_owned(),
            message: error.to_string(),
        })?
        .compile_matcher();
    let mentions_node_modules = pattern.contains("node_modules");
    let max_depth = if pattern.split('/').any(|segment| segment == "**") {
        None
    } else {
        Some(
            pattern
                .split('/')
                .filter(|segment| !segment.is_empty())
                .count()
                .max(1),
        )
    };
    let mut builder = ignore::WalkBuilder::new(&target.canonical);
    builder
        .hidden(!request.hidden)
        .ignore(request.gitignore)
        .git_ignore(request.gitignore)
        .git_global(request.gitignore)
        .git_exclude(request.gitignore)
        .parents(request.gitignore)
        .require_git(false)
        .follow_links(false)
        .max_depth(max_depth)
        .filter_entry(move |entry| {
            let name = entry.file_name();
            name != ".git" && (mentions_node_modules || name != "node_modules")
        });
    let keep = limit;
    let mut matches = Vec::with_capacity(keep.saturating_add(1));
    let mut timed_out = false;
    for entry in builder.build() {
        if Instant::now() >= deadline {
            timed_out = true;
            break;
        }
        let entry = match entry {
            Ok(entry) => entry,
            Err(error)
                if error.io_error().is_some_and(|error| {
                    matches!(
                        error.kind(),
                        std::io::ErrorKind::NotFound | std::io::ErrorKind::PermissionDenied
                    )
                }) =>
            {
                continue
            }
            Err(error) => return Err(workspace_error(error)),
        };
        if entry.depth() == 0 {
            continue;
        }
        let Ok(relative) = entry.path().strip_prefix(&target.canonical) else {
            continue;
        };
        if !pattern_matcher.is_match(relative.to_string_lossy().replace('\\', "/")) {
            continue;
        }
        let is_dir = entry.file_type().is_some_and(|kind| kind.is_dir());
        let mut path = display_path(
            root,
            &target.canonical,
            target.visible_root.as_deref(),
            entry.path(),
        )?;
        if is_dir {
            path.push('/');
        }
        let modified_ms = entry
            .metadata()
            .map_or(0, |metadata| modified_ms(&metadata));
        retain_ranked(
            &mut matches,
            GlobMatch {
                path,
                modified_ms,
                is_dir,
            },
            keep,
        );
    }
    timed_out |= Instant::now() >= deadline;
    matches.sort_by(|left, right| compare_rank(right, left));
    let truncated = matches.len() > keep;
    matches.truncate(keep);
    Ok(WalkOutcome {
        matches,
        truncated,
        timed_out,
    })
}

/// Keeps the `limit + 1` best-ranked matches seen so far.
fn retain_ranked(matches: &mut Vec<GlobMatch>, candidate: GlobMatch, limit: usize) {
    if matches.len() < limit.saturating_add(1) {
        matches.push(candidate);
        return;
    }
    let Some((worst, _)) = matches
        .iter()
        .enumerate()
        .min_by(|(_, left), (_, right)| compare_rank(left, right))
    else {
        return;
    };
    if compare_rank(&candidate, &matches[worst]).is_gt() {
        matches[worst] = candidate;
    }
}

/// Newer ranks higher; at equal times the lexically smaller path does.
fn compare_rank(left: &GlobMatch, right: &GlobMatch) -> cmp::Ordering {
    left.modified_ms
        .cmp(&right.modified_ms)
        .then_with(|| right.path.cmp(&left.path))
}

fn display_path(
    root: &Path,
    canonical_root: &Path,
    visible_root: Option<&Path>,
    path: &Path,
) -> Result<String, GlobError> {
    if let (false, Some(visible_root)) = (path.starts_with(root), visible_root) {
        let relative = path
            .strip_prefix(canonical_root)
            .map_err(|_| GlobError::Workspace {
                message: "glob result escaped the canonical traversal root".to_owned(),
            })?;
        return Ok(visible_root
            .join(relative)
            .to_string_lossy()
            .replace('\\', "/"));
    }
    workspace_relative(root, path).map_err(workspace_error)
}

fn lexical_normalize_absolute(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::Prefix(_) | Component::RootDir | Component::Normal(_) => {
                normalized.push(component.as_os_str());
            }
            Component::CurDir => {}
            Component::ParentDir => {
                if matches!(
                    normalized.components().next_back(),
                    Some(Component::Normal(_))
                ) {
                    normalized.pop();
                }
            }
        }
    }
    normalized
}

fn modified_ms(metadata: &fs::Metadata) -> u64 {
    metadata
        .modified()
        .ok()
        .and_then(|modified| modified.duration_since(UNIX_EPOCH).ok())
        .map_or(0, |duration| {
            u64::try_from(duration.as_millis()).unwrap_or(u64::MAX)
        })
}

fn workspace_error(error: impl std::fmt::Display) -> GlobError {
    GlobError::Workspace {
        message: error.to_string(),
    }
}

#[cfg(test)]
mod tests;
