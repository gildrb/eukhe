//! Filesystem collectors for resource discovery: recursive file collection
//! under `.gitignore`/`.ignore`/`.fdignore` rules, skill-entry scanning with
//! the `SKILL.md` stopping rule, prompt/theme auto-discovery, and the
//! `.agents/skills` ancestor scan.

use std::path::{Path, PathBuf};

use eukhe_bend::rules::glob::{self, IgnoreEntry, IgnoreRule};
use eukhe_bend::{expect_core, Entry};

use super::super::source::path_relative;
use crate::skills::diagnostics::ResourceDiagnostic;

/// Ignore-file names consulted during resource discovery.
const IGNORE_FILE_NAMES: [&str; 3] = [".gitignore", ".ignore", ".fdignore"];

/// Skill discovery styles: `pi` reads root markdown skills in addition to
/// `SKILL.md` packages; `agents` only reads `SKILL.md` packages.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SkillDiscoveryMode {
    Pi,
    Agents,
}

/// One directory entry: name, path, and whether it is a symlink (classified
/// through the target, matching the TS `statSync`-after-readdir flow).
struct DirEntry {
    name: String,
    path: PathBuf,
}

fn read_entries_sorted(dir: &Path) -> Vec<DirEntry> {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return Vec::new();
    };
    let mut entries: Vec<DirEntry> = entries
        .filter_map(std::result::Result::ok)
        .map(|entry| DirEntry {
            name: entry.file_name().to_string_lossy().into_owned(),
            path: entry.path(),
        })
        .collect();
    entries.sort_by(|a, b| a.name.cmp(&b.name));
    entries
}

/// Follow symlinks: classify an entry as (`is_dir`, `is_file`); unreadable
/// symlinks classify as nothing.
fn classify(path: &Path) -> (bool, bool) {
    match std::fs::metadata(path) {
        Ok(meta) => (meta.is_dir(), meta.is_file()),
        Err(_) => (false, false),
    }
}

fn is_node_modules(name: &str, skip_node_modules: bool) -> bool {
    skip_node_modules && name == "node_modules"
}

/// Ordered gitignore-style rule set, added incrementally as the walk enters
/// nested directories (patterns from nested files are prefixed with their
/// directory, so a single root-relative matcher stays correct). Broken
/// rules and ignore files that cannot be read go into `diagnostics`. A
/// rule that is not a valid glob, or an ignore file that cannot be read,
/// becomes the rule that ignores every path under its directory
/// ([`IgnoreRule::Everything`], a prefix that is empty for the root, else
/// ends in `/`): a broken rule can only ignore more paths, never fewer.
/// The compiled core decides which paths the rules ignore, one directory
/// listing per call.
pub(crate) struct IgnoreMatcher {
    rules: Vec<IgnoreRule>,
    diagnostics: Vec<ResourceDiagnostic>,
}

impl IgnoreMatcher {
    pub(crate) fn new() -> Self {
        Self {
            rules: Vec::new(),
            diagnostics: Vec::new(),
        }
    }

    /// Add the ignore-file rules found in `dir` (relative to `root`). A
    /// missing ignore file adds nothing. An ignore file that cannot be read
    /// is reported, and every path under `dir` is then ignored.
    pub(crate) fn add_rules(&mut self, dir: &Path, root: &Path) {
        let relative_dir = path_relative(root, dir);
        let prefix = if relative_dir.is_empty() {
            String::new()
        } else {
            format!("{relative_dir}/")
        };
        for filename in IGNORE_FILE_NAMES {
            let ignore_path = dir.join(filename);
            let content = match std::fs::read_to_string(&ignore_path) {
                Ok(content) => content,
                Err(error) if is_missing(&ignore_path, &error) => continue,
                Err(error) => {
                    self.diagnostics.push(ResourceDiagnostic::Warning {
                        message: format!(
                            "ignore file not read, so every path under its directory is ignored: {error}"
                        ),
                        path: Some(ignore_path.display().to_string()),
                    });
                    self.rules.push(IgnoreRule::Everything {
                        prefix: prefix.clone(),
                    });
                    continue;
                }
            };
            for line in content.split('\n').flat_map(|line| line.split('\r')) {
                if let Some(pattern) = prefix_ignore_pattern(line, &prefix) {
                    self.add_pattern(&pattern, line, &prefix, &ignore_path);
                }
            }
        }
    }

    /// Add one prefixed `pattern` (from `line` of `ignore_path`). A pattern
    /// that is not a valid glob is reported. If it is a negated pattern, it
    /// is not used, because it can only include paths again. Else every
    /// path under `prefix` is ignored.
    fn add_pattern(&mut self, pattern: &str, line: &str, prefix: &str, ignore_path: &Path) {
        let mut glob = pattern;
        let negated = glob.starts_with('!');
        if negated {
            glob = &glob[1..];
        }
        let dir_only = glob.ends_with('/');
        if dir_only {
            glob = glob.strip_suffix('/').unwrap_or(glob);
        }
        let anchored = glob.contains('/');
        let Err(error) = expect_core(Entry::Glob, glob::check(glob)) else {
            self.rules.push(IgnoreRule::Glob {
                pattern: glob.to_string(),
                anchored,
                negated,
                dir_only,
            });
            return;
        };
        let effect = if negated {
            "it is not used"
        } else {
            self.rules.push(IgnoreRule::Everything {
                prefix: prefix.to_string(),
            });
            "every path under its directory is ignored"
        };
        self.diagnostics.push(ResourceDiagnostic::Warning {
            message: format!("ignore rule \"{line}\" is not a valid glob, so {effect}: {error}"),
            path: Some(ignore_path.display().to_string()),
        });
    }

    /// Per root-relative path (`true`: a directory; the TS side passes
    /// trailing-slash paths), whether it is ignored. One core call for
    /// the whole listing; none when no rule is set.
    pub(crate) fn ignored(&self, entries: &[(String, bool)]) -> Vec<bool> {
        if self.rules.is_empty() {
            return vec![false; entries.len()];
        }
        let entries: Vec<IgnoreEntry<'_>> = entries
            .iter()
            .map(|(path, is_dir)| IgnoreEntry {
                path,
                is_dir: *is_dir,
            })
            .collect();
        expect_core(Entry::Glob, glob::ignored(&self.rules, &entries))
    }
}

/// Prepare one ignore-file line for the root-relative matcher: comments drop,
/// `!`/`\!` negation/escape prefixes and leading `/` anchors normalize, and
/// nested-directory patterns get their directory prefix. Returns the
/// negation-prefixed pattern (or `None` for blank/comment lines).
fn prefix_ignore_pattern(line: &str, prefix: &str) -> Option<String> {
    let trimmed = line.trim();
    if trimmed.is_empty() {
        return None;
    }
    if trimmed.starts_with('#') && !trimmed.starts_with("\\#") {
        return None;
    }

    let mut pattern = line;
    let mut negated = false;
    if let Some(rest) = pattern.strip_prefix('!') {
        negated = true;
        pattern = rest;
    } else if let Some(rest) = pattern.strip_prefix("\\!") {
        pattern = rest;
    }
    if let Some(rest) = pattern.strip_prefix('/') {
        pattern = rest;
    }

    let prefixed = if prefix.is_empty() {
        pattern.to_string()
    } else {
        format!("{prefix}{pattern}")
    };
    if negated {
        Some(format!("!{prefixed}"))
    } else {
        Some(prefixed)
    }
}

/// File-name suffixes recognized per resource type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FileKind {
    Markdown,
    Json,
}

/// Lowercase file-name extension test (a bare `.md` name has no extension and
/// does not match).
fn extension_is(name: &str, wanted: &[&str]) -> bool {
    Path::new(name)
        .extension()
        .and_then(|ext| ext.to_str())
        .is_some_and(|ext| wanted.contains(&ext))
}

impl FileKind {
    fn matches(self, name: &str) -> bool {
        match self {
            FileKind::Markdown => extension_is(name, &["md"]),
            FileKind::Json => extension_is(name, &["json"]),
        }
    }
}

/// Collect all files of a kind under `dir`, honoring ignore rules and
/// skipping dotfiles and `node_modules`. Broken ignore rules go into
/// `diagnostics`.
pub(crate) fn collect_files(
    dir: &Path,
    kind: FileKind,
    diagnostics: &mut Vec<ResourceDiagnostic>,
) -> Vec<PathBuf> {
    let mut matcher = IgnoreMatcher::new();
    let files = collect_files_inner(dir, kind, true, &mut matcher, dir);
    diagnostics.append(&mut matcher.diagnostics);
    files
}

/// One directory entry a walk considers: whether it is a directory or a
/// file (through symlinks), and whether the ignore rules ignore it.
struct Listed {
    entry: DirEntry,
    is_dir: bool,
    is_file: bool,
    ignored: bool,
}

/// The entries of `dir` (sorted by name) whose name `keep` admits, each
/// classified and decided by the ignore rules (paths relative to `root`)
/// in one core call.
fn listing(
    dir: &Path,
    root: &Path,
    matcher: &IgnoreMatcher,
    keep: impl Fn(&str) -> bool,
) -> Vec<Listed> {
    let kept: Vec<(DirEntry, bool, bool)> = read_entries_sorted(dir)
        .into_iter()
        .filter(|entry| keep(&entry.name))
        .map(|entry| {
            let (is_dir, is_file) = classify(&entry.path);
            (entry, is_dir, is_file)
        })
        .collect();
    let paths: Vec<(String, bool)> = kept
        .iter()
        .map(|(entry, is_dir, _)| (path_relative(root, &entry.path), *is_dir))
        .collect();
    kept.into_iter()
        .zip(matcher.ignored(&paths))
        .map(|((entry, is_dir, is_file), ignored)| Listed {
            entry,
            is_dir,
            is_file,
            ignored,
        })
        .collect()
}

fn collect_files_inner(
    dir: &Path,
    kind: FileKind,
    skip_node_modules: bool,
    matcher: &mut IgnoreMatcher,
    root: &Path,
) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if !dir.exists() {
        return files;
    }
    matcher.add_rules(dir, root);
    for listed in listing(dir, root, matcher, |name| {
        !name.starts_with('.') && !is_node_modules(name, skip_node_modules)
    }) {
        if listed.ignored {
            continue;
        }
        if listed.is_dir {
            files.extend(collect_files_inner(
                &listed.entry.path,
                kind,
                skip_node_modules,
                matcher,
                root,
            ));
        } else if listed.is_file && kind.matches(&listed.entry.name) {
            files.push(listed.entry.path);
        }
    }
    files
}

/// Scan one directory level for skill entries: a `SKILL.md` file present in
/// the directory stops the scan there. Broken ignore rules go into
/// `diagnostics`.
pub(crate) fn collect_skill_entries(
    dir: &Path,
    mode: SkillDiscoveryMode,
    diagnostics: &mut Vec<ResourceDiagnostic>,
) -> Vec<PathBuf> {
    let mut matcher = IgnoreMatcher::new();
    let entries = collect_skill_entries_inner(dir, mode, &mut matcher, dir);
    diagnostics.append(&mut matcher.diagnostics);
    entries
}

fn collect_skill_entries_inner(
    dir: &Path,
    mode: SkillDiscoveryMode,
    matcher: &mut IgnoreMatcher,
    root: &Path,
) -> Vec<PathBuf> {
    let mut entries = Vec::new();
    if !dir.exists() {
        return entries;
    }
    matcher.add_rules(dir, root);
    let listed = listing(dir, root, matcher, |name| {
        !name.starts_with('.') && !is_node_modules(name, true)
    });

    if let Some(skill) = listed.iter().find(|listed| {
        listed.entry.name == "SKILL.md" && !listed.is_dir && listed.is_file && !listed.ignored
    }) {
        entries.push(skill.entry.path.clone());
        return entries;
    }

    for listed in listed {
        // Root markdown skills apply only in `pi` mode at the scan root.
        if mode == SkillDiscoveryMode::Pi
            && dir == root
            && !listed.is_dir
            && listed.is_file
            && extension_is(&listed.entry.name, &["md"])
            && !listed.ignored
        {
            entries.push(listed.entry.path);
            continue;
        }
        if !listed.is_dir || listed.ignored {
            continue;
        }
        entries.extend(collect_skill_entries_inner(
            &listed.entry.path,
            mode,
            matcher,
            root,
        ));
    }
    entries
}

/// Auto-discovery of top-level `.md` prompt files (no recursion).
pub(crate) fn collect_auto_prompt_entries(
    dir: &Path,
    diagnostics: &mut Vec<ResourceDiagnostic>,
) -> Vec<PathBuf> {
    collect_top_level_files(dir, FileKind::Markdown, diagnostics)
}

/// Auto-discovery of top-level `.json` theme files (no recursion).
pub(crate) fn collect_auto_theme_entries(
    dir: &Path,
    diagnostics: &mut Vec<ResourceDiagnostic>,
) -> Vec<PathBuf> {
    collect_top_level_files(dir, FileKind::Json, diagnostics)
}

fn collect_top_level_files(
    dir: &Path,
    kind: FileKind,
    diagnostics: &mut Vec<ResourceDiagnostic>,
) -> Vec<PathBuf> {
    let mut entries = Vec::new();
    if !dir.exists() {
        return entries;
    }
    let mut matcher = IgnoreMatcher::new();
    matcher.add_rules(dir, dir);
    diagnostics.append(&mut matcher.diagnostics);
    for listed in listing(dir, dir, &matcher, |name| {
        !name.starts_with('.') && !is_node_modules(name, true)
    }) {
        if !listed.ignored && !listed.is_dir && listed.is_file && kind.matches(&listed.entry.name) {
            entries.push(listed.entry.path);
        }
    }
    entries
}

/// True when `error` tells that nothing is at `path`. A symlink that points
/// to nothing is not missing. It is a broken entry.
fn is_missing(path: &Path, error: &std::io::Error) -> bool {
    error.kind() == std::io::ErrorKind::NotFound && !path.is_symlink()
}

/// Read the `pi` manifest in the `package.json` of a package. `Ok(None)`
/// tells that the package has no `package.json`, or that its `package.json`
/// has no `pi` key. Then the convention directories apply.
///
/// # Errors
///
/// Returns a diagnostic for a `package.json` that cannot be read or parsed,
/// or that has a `pi` value of the wrong shape. Then the package loads
/// nothing.
pub(crate) fn read_pi_manifest(
    package_root: &Path,
) -> Result<Option<super::PiManifest>, Box<ResourceDiagnostic>> {
    let package_json = package_root.join("package.json");
    let broken = |reason: String| {
        Box::new(ResourceDiagnostic::Error {
            message: format!("package manifest not used, so the package loads nothing: {reason}"),
            path: Some(package_json.display().to_string()),
        })
    };
    let content = match std::fs::read_to_string(&package_json) {
        Ok(content) => content,
        Err(error) if is_missing(&package_json, &error) => return Ok(None),
        Err(error) => return Err(broken(error.to_string())),
    };
    let value: serde_json::Value =
        serde_json::from_str(&content).map_err(|error| broken(error.to_string()))?;
    let Some(package) = value.as_object() else {
        return Err(broken("package.json is not a JSON object".to_string()));
    };
    let Some(pi) = package.get("pi") else {
        return Ok(None);
    };
    let Some(pi) = pi.as_object() else {
        return Err(broken("\"pi\" is not an object".to_string()));
    };
    Ok(Some(super::PiManifest {
        skills: string_array(pi, "skills").map_err(&broken)?,
        prompts: string_array(pi, "prompts").map_err(&broken)?,
        themes: string_array(pi, "themes").map_err(&broken)?,
    }))
}

/// The list of strings at `pi.<key>`. A missing key gives `None`. A value
/// that is not a list of strings gives the reason as an error.
fn string_array(
    pi: &serde_json::Map<String, serde_json::Value>,
    key: &str,
) -> Result<Option<Vec<String>>, String> {
    let Some(value) = pi.get(key) else {
        return Ok(None);
    };
    let serde_json::Value::Array(entries) = value else {
        return Err(format!("\"pi.{key}\" is not a list"));
    };
    entries
        .iter()
        .map(|entry| {
            entry
                .as_str()
                .map(str::to_string)
                .ok_or_else(|| format!("\"pi.{key}\" has an entry that is not a string"))
        })
        .collect::<Result<Vec<String>, String>>()
        .map(Some)
}

/// Collect resource files from a directory by kind: skills use the
/// skill-entry scanner, others recursive file collection. Broken ignore
/// rules go into `diagnostics`.
pub(crate) fn collect_resource_files(
    dir: &Path,
    resource_type: super::ResourceType,
    diagnostics: &mut Vec<ResourceDiagnostic>,
) -> Vec<PathBuf> {
    match resource_type {
        super::ResourceType::Skills => {
            collect_skill_entries(dir, SkillDiscoveryMode::Pi, diagnostics)
        }
        super::ResourceType::Prompts => collect_files(dir, FileKind::Markdown, diagnostics),
        super::ResourceType::Themes => collect_files(dir, FileKind::Json, diagnostics),
    }
}

/// Find the nearest ancestor containing a `.git` entry.
fn find_git_repo_root(start_dir: &Path) -> Option<PathBuf> {
    let mut dir = start_dir.to_path_buf();
    loop {
        if dir.join(".git").exists() {
            return Some(dir);
        }
        let parent = dir.parent()?;
        if parent == dir {
            return None;
        }
        dir = parent.to_path_buf();
    }
}

/// Every ancestor's `.agents/skills` directory from the start dir up to the
/// git repo root (or the filesystem root outside a repo), nearest first.
pub(crate) fn collect_ancestor_agents_skill_dirs(start_dir: &Path) -> Vec<PathBuf> {
    let mut dirs = Vec::new();
    let git_root = find_git_repo_root(start_dir);
    let mut dir = start_dir.to_path_buf();
    loop {
        dirs.push(dir.join(".agents").join("skills"));
        if git_root.as_deref() == Some(dir.as_path()) {
            break;
        }
        let Some(parent) = dir.parent() else {
            break;
        };
        if parent == dir {
            break;
        }
        dir = parent.to_path_buf();
    }
    dirs
}
