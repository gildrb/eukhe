//! `grep`: regex search over files, grouped by file, with file tags.
//!
//! Every file in the result is snapshotted in the session [`EditStore`] and
//! its shown rows are recorded as seen, so `N:TEXT` rows are edit anchors.
//! Ported from omp `crates/tools/src/grep.rs` (request, paging, rendering)
//! and `crates/envd/src/tool_search.rs` (roots, targets); the per-call match
//! cap is omp v1's `totalMatchLimit` (`packages/coding-agent/src/tools/grep.ts`).

mod engine;
#[cfg(test)]
mod tests;

use std::{
    collections::{HashMap, HashSet},
    fmt::Write as _,
    fs,
    num::NonZeroUsize,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use crate::{
    notice::{Notice, NoticeKind, Omitted, Unit},
    path::canonical_key,
    path_tree::{build_path_tree, walk_path_tree, GroupedTreeEventKind},
    read::selector::{
        line_in_ranges, parse_selector, split_path_and_selector, LineRange, Selector,
    },
    scope::{
        has_glob_chars, is_missing, normalize_path_input, resolve_input_path, workspace_relative,
    },
    store::EditStore,
};

use engine::{FileRead, FileSearcher, RegexOptions, MAX_FILE_BYTES};

/// Files shown per page of a multi-file search; `skip` pages further.
pub const DEFAULT_FILE_LIMIT: usize = 20;
/// Matches kept per file when the scope can hold several files.
const MULTI_FILE_PER_FILE_MATCHES: usize = 20;
/// Matches kept when the scope is one file.
const SINGLE_FILE_MATCHES: usize = 200;
/// Matches fetched across all files before grouping and paging.
const INTERNAL_TOTAL_CAP: u64 = 2_000;
/// Wall-clock budget of one search.
const SEARCH_GREP_TIMEOUT: Duration = Duration::from_secs(30);
/// Maximum bytes kept of one shown line, including the `...` marker.
const DEFAULT_MAX_COLUMN: usize = 512;

/// One `grep` call.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GrepRequest {
    /// Regex (Rust syntax). A literal newline or a `\n` escape enables
    /// cross-line matching. An invalid regex is repaired or searched literally.
    pub pattern: String,
    /// Files, directories, or globs relative to the working directory,
    /// separated by `;`. Empty searches `.`. A file or directory may carry a
    /// line selector (`src/a.rs:50-100`, `src/a.rs:5-8,12`) that restricts
    /// matches and context to those lines.
    pub path: String,
    /// Extra file glob for directory roots; a bare name glob matches at any
    /// depth.
    pub glob: Option<String>,
    /// Match without regard to case.
    pub ignore_case: bool,
    /// Respect `.gitignore`, `.ignore`, git excludes, and the global gitignore.
    pub gitignore: bool,
    /// Context lines shown before each match.
    pub context_before: u32,
    /// Context lines shown after each match.
    pub context_after: u32,
    /// Matching files to skip; pages a multi-file result.
    pub skip: u64,
    /// Cap on shown matches, taken round-robin across files.
    pub limit: Option<NonZeroUsize>,
}

/// A failed `grep`. `Display` is the model-facing message.
#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum GrepError {
    /// The pattern was empty or whitespace-only.
    #[error("Pattern must not be empty")]
    EmptyPattern,
    /// The regex and every repair of it were rejected.
    #[error("Invalid regex: {message}")]
    InvalidRegex {
        /// Parser detail without the `regex parse error:` prefix.
        message: String,
    },
    /// The 30-second deadline elapsed.
    #[error("Grep timed out after 30s; narrow paths or pattern, or scope with `glob` first")]
    TimedOut,
    /// Every target was missing.
    #[error(
        "Path not found: {}; list each target in the semicolon-delimited `path`",
        .paths.join(", ")
    )]
    AllPathsMissing {
        /// Missing targets in request order.
        paths: Vec<String>,
    },
    /// A `path` entry carried an unusable line selector.
    #[error("{message}")]
    InvalidSelector {
        /// The model-facing reason.
        message: String,
    },
    /// The filesystem failed or a glob did not compile.
    #[error("{message}")]
    Workspace {
        /// The failure.
        message: String,
    },
}

/// One line shown around a match.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContextLine {
    /// One-based line number.
    pub line_number: u32,
    /// Line text without its line ending or trailing whitespace.
    pub line: String,
}

/// One matching line and its context.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GrepMatch {
    /// One-based line number.
    pub line_number: u32,
    /// Line text without its line ending or trailing whitespace.
    pub line: String,
    /// Whether `line` was cut to 512 bytes (ending in `...`).
    pub truncated: bool,
    /// Context before the match, in source order.
    pub context_before: Vec<ContextLine>,
    /// Context after the match, in source order.
    pub context_after: Vec<ContextLine>,
}

/// One file of the result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GrepFile {
    /// Path relative to the working directory (absolute outside it), `/`
    /// separated.
    pub path: String,
    /// Canonical path: the [`EditStore`] key.
    pub absolute: PathBuf,
    /// File tag; absent for a file above 4 MiB or not UTF-8.
    pub tag: Option<String>,
    /// Matches in source order.
    pub matches: Vec<GrepMatch>,
}

/// A `grep` result: typed hits, notices, and the model-facing text.
#[allow(
    clippy::struct_excessive_bools,
    reason = "independent facts of omp's grep payload, each read on its own by callers"
)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GrepOutput {
    /// The files of this page.
    pub files: Vec<GrepFile>,
    /// Matching files found before paging.
    pub total_files: u64,
    /// Whether the fetch cap stopped the search, so `total_files` is a lower
    /// bound.
    pub total_files_lower_bound: bool,
    /// Whether the scope can hold several files (a directory, a glob, or
    /// several roots).
    pub multi_scope: bool,
    /// Files skipped before this page.
    pub skip: u64,
    /// Whether more matching files follow this page.
    pub file_limit_reached: bool,
    /// Whether a file had more matches than its per-file cap.
    pub per_file_limit_reached: bool,
    /// Whether `limit` cut matches.
    pub match_limit_reached: bool,
    /// Pagination, limits, and skipped inputs.
    pub notices: Vec<Notice>,
    /// Model-facing rows: `[path#TAG]` then `*N:TEXT` (match) and ` N:TEXT`
    /// (context) for one file; `#`-headed folded directory groups for many.
    pub text: String,
}

impl GrepOutput {
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

enum Target {
    File(PathBuf),
    Directory { path: PathBuf, glob: Option<String> },
}

/// One resolved root: what to search and the lines a selector kept, empty
/// for an unrestricted root.
struct Scoped {
    target: Target,
    ranges: Vec<LineRange>,
}

struct Found {
    path: String,
    absolute: PathBuf,
    matched: GrepMatch,
}

/// What the search phase gathered before grouping and paging.
struct Searched {
    found: Vec<Found>,
    /// The fetch cap stopped the search.
    limit_reached: bool,
    skipped_oversized: u64,
    oversized_files: Vec<String>,
}

/// One page of grouped files.
struct Page {
    files: Vec<GrepFile>,
    total_files: u64,
    skip: u64,
    next_skip: u64,
    file_limit_reached: bool,
    per_file_limit_reached: bool,
    match_limit_reached: bool,
}

/// Search `request.path` under `cwd`, record every shown row as seen in
/// `store`, and render the result.
///
/// # Errors
/// [`GrepError`] for an empty pattern, an unusable regex or glob, all targets
/// missing, a filesystem failure, or the 30-second deadline.
pub fn grep(store: &EditStore, cwd: &Path, request: &GrepRequest) -> Result<GrepOutput, GrepError> {
    if request.pattern.trim().is_empty() {
        return Err(GrepError::EmptyPattern);
    }
    let deadline = Instant::now() + SEARCH_GREP_TIMEOUT;
    let root = fs::canonicalize(cwd).map_err(workspace_error)?;
    let roots = split_roots(&root, &request.path);
    let mut targets = Vec::new();
    let mut missing_paths = Vec::new();
    for input in &roots {
        let (path, ranges) = parse_root(input)?;
        match resolve_target(&root, path)? {
            Some(target) => targets.push(Scoped { target, ranges }),
            None => missing_paths.push(input.clone()),
        }
    }
    if targets.is_empty() {
        return Err(GrepError::AllPathsMissing {
            paths: missing_paths,
        });
    }
    let multi_scope = roots.len() > 1
        || targets.iter().any(|scoped| match scoped.target {
            Target::File(_) => false,
            Target::Directory { .. } => true,
        });
    let per_file_cap = if multi_scope {
        MULTI_FILE_PER_FILE_MATCHES
    } else {
        SINGLE_FILE_MATCHES
    };
    let mut searched = search_targets(&root, &targets, request, per_file_cap, deadline)?;
    let mut page = group_and_page(
        std::mem::take(&mut searched.found),
        request,
        multi_scope,
        per_file_cap,
    );

    for file in &mut page.files {
        let shown: Vec<u32> = file
            .matches
            .iter()
            .flat_map(|matched| {
                matched
                    .context_before
                    .iter()
                    .map(|line| line.line_number)
                    .chain([matched.line_number])
                    .chain(matched.context_after.iter().map(|line| line.line_number))
            })
            .collect();
        file.tag = store.record_file(&file.absolute, Some(&shown));
    }

    let notices = notices(&missing_paths, &searched, &page, multi_scope, request.limit);
    let (skip, total_files) = (page.skip, page.total_files);
    let text = render(&page.files, total_files, multi_scope);
    Ok(GrepOutput {
        files: page.files,
        total_files,
        total_files_lower_bound: searched.limit_reached,
        multi_scope,
        skip,
        file_limit_reached: page.file_limit_reached,
        per_file_limit_reached: page.per_file_limit_reached,
        match_limit_reached: page.match_limit_reached,
        notices,
        text,
    })
}

/// omp's notices for a result, in omp's order: skipped inputs, then paging,
/// then the match limit.
fn notices(
    missing_paths: &[String],
    searched: &Searched,
    page: &Page,
    multi_scope: bool,
    limit: Option<NonZeroUsize>,
) -> Vec<Notice> {
    let mut notices = Vec::new();
    if !missing_paths.is_empty() {
        notices.push(Notice::warn(
            NoticeKind::MissingPaths,
            missing_paths.join(", "),
        ));
    }
    if !searched.oversized_files.is_empty() {
        notices.push(Notice::warn(
            NoticeKind::PartialScan,
            format!(
                "Only the first 4 MB was searched: {}",
                searched.oversized_files.join(", ")
            ),
        ));
    } else if searched.skipped_oversized > 0 {
        notices.push(Notice::warn(
            NoticeKind::Skipped,
            format!(
                "{} unreadable large files were not searched",
                searched.skipped_oversized
            ),
        ));
    }
    let (skip, total_files) = (page.skip, page.total_files);
    if page.files.is_empty() && multi_scope && skip > 0 && total_files > 0 && skip >= total_files {
        let suffix = if searched.limit_reached { "+" } else { "" };
        notices.push(Notice::warn(
            NoticeKind::RangeOutOfBounds,
            format!("skip={skip} is past the end of {total_files}{suffix} files"),
        ));
    } else if page.file_limit_reached {
        let next_skip = page.next_skip;
        notices.push(Notice {
            continuation: Some(format!("skip={next_skip}")),
            omitted: Some(Omitted {
                count: total_files.saturating_sub(next_skip),
                unit: Unit::Files,
            }),
            ..Notice::info(
                NoticeKind::Pagination,
                format!(
                    "files {}-{next_skip} of {total_files}",
                    skip.saturating_add(1)
                ),
            )
        });
    }
    if let Some(limit) = limit.filter(|_| page.match_limit_reached) {
        notices.push(Notice {
            continuation: Some(format!("limit={}", limit.get().saturating_mul(2))),
            ..Notice::info(
                NoticeKind::LimitReached,
                format!("{limit} result limit reached"),
            )
        });
    }

    notices
}

/// Searches every target in order, fetching at most `per_file_cap + 1`
/// matches per file (more for a line-ranged root, so every match up to its
/// last selected line is reached) and [`INTERNAL_TOTAL_CAP`] in all; matches
/// and context outside a root's ranges are dropped, and a line reached
/// through two roots counts once.
fn search_targets(
    root: &Path,
    targets: &[Scoped],
    request: &GrepRequest,
    per_file_cap: usize,
    deadline: Instant,
) -> Result<Searched, GrepError> {
    let options = RegexOptions::for_pattern(&request.pattern, request.ignore_case);
    let matcher = engine::build_matcher(&request.pattern, options)?;
    let mut file_searcher = FileSearcher::new(
        request.context_before,
        request.context_after,
        options,
        DEFAULT_MAX_COLUMN,
    );
    let baseline_fetch = u64::try_from(per_file_cap + 1).unwrap_or(u64::MAX);
    let mut searched = Searched {
        found: Vec::new(),
        limit_reached: false,
        skipped_oversized: 0,
        oversized_files: Vec::new(),
    };
    let mut remaining = INTERNAL_TOTAL_CAP;
    let mut seen = HashSet::new();
    let mut buffer = Vec::new();
    for Scoped { target, ranges } in targets {
        let per_file_fetch = baseline_fetch.max(range_fetch(ranges, baseline_fetch));
        let files = match target {
            Target::File(path) => {
                if fs::metadata(path).map_err(workspace_error)?.len() > MAX_FILE_BYTES {
                    searched.oversized_files.push(display_path(root, path)?);
                }
                vec![path.clone()]
            }
            Target::Directory { path, glob } => {
                let globs = glob
                    .iter()
                    .chain(request.glob.iter().filter(|glob| !glob.trim().is_empty()))
                    .map(|source| Ok((source.clone(), engine::compile_walk_glob(source)?)))
                    .collect::<Result<Vec<_>, GrepError>>()?;
                engine::walk_files(path, &globs, request.gitignore, deadline)?
            }
        };
        for file in files {
            if remaining == 0 {
                searched.limit_reached = true;
                return Ok(searched);
            }
            if Instant::now() >= deadline {
                return Err(GrepError::TimedOut);
            }
            let read =
                engine::read_file(&file, &mut buffer).map_err(|error| GrepError::Workspace {
                    message: format!("{}: {error}", file.display()),
                })?;
            match read {
                FileRead::Read => {}
                FileRead::OversizedUnreadable => {
                    searched.skipped_oversized += 1;
                    continue;
                }
                FileRead::Skipped => continue,
            }
            if buffer.contains(&0) {
                continue;
            }
            let fetch = remaining.min(per_file_fetch);
            let hits = file_searcher
                .search(&matcher, &buffer, fetch)
                .map_err(workspace_error)?;
            searched.limit_reached |= hits.limit_reached && fetch == remaining;
            if hits.matches.is_empty() {
                continue;
            }
            let absolute = canonical_key(&file);
            let path = display_path(root, &absolute)?;
            for mut matched in hits.matches {
                if !ranges.is_empty() {
                    if !line_in_ranges(u64::from(matched.line_number), ranges) {
                        continue;
                    }
                    let inside =
                        |line: &ContextLine| line_in_ranges(u64::from(line.line_number), ranges);
                    matched.context_before.retain(inside);
                    matched.context_after.retain(inside);
                }
                if !seen.insert((absolute.clone(), matched.line_number)) {
                    continue;
                }
                searched.found.push(Found {
                    path: path.clone(),
                    absolute: absolute.clone(),
                    matched,
                });
                remaining -= 1;
                if remaining == 0 {
                    searched.limit_reached = true;
                    return Ok(searched);
                }
            }
        }
    }
    Ok(searched)
}

/// Matches to fetch from one file of a line-ranged root so that every match
/// up to the last selected line is reached; an open range keeps
/// `baseline` past its start (omp `fetch_budgets`).
fn range_fetch(ranges: &[LineRange], baseline: u64) -> u64 {
    ranges
        .iter()
        .map(|range| {
            range
                .end_line
                .unwrap_or_else(|| range.start_line.saturating_sub(1).saturating_add(baseline))
        })
        .max()
        .unwrap_or(0)
        .min(MAX_FILE_BYTES)
}

/// Peel a line selector off one root: the path to search and its ranges
/// (omp `parse_root`). `raw` is accepted and ignored; ranges need a single
/// file or directory, not a glob.
fn parse_root(original: &str) -> Result<(&str, Vec<LineRange>), GrepError> {
    let split = split_path_and_selector(original);
    let ranges = match split.selector {
        None => Vec::new(),
        Some(selector) => match parse_selector(Some(selector)) {
            Ok(Selector::Lines { ranges, .. }) => ranges,
            Ok(Selector::Whole | Selector::Raw) => Vec::new(),
            Err(error) => {
                return Err(GrepError::InvalidSelector {
                    message: format!(
                    "path entry \"{original}\" has an invalid selector \":{selector}\" — {error}"
                ),
                })
            }
        },
    };
    if !ranges.is_empty() && has_glob_chars(split.path) {
        return Err(GrepError::InvalidSelector {
            message: format!("Line-range selector requires a single file, not a glob: {original}"),
        });
    }
    Ok((split.path, ranges))
}

/// Groups matches by file in encounter order, caps each file, and cuts the
/// requested page: [`DEFAULT_FILE_LIMIT`] files, or `limit + 1` files with
/// `limit` matches taken round-robin.
fn group_and_page(
    found: Vec<Found>,
    request: &GrepRequest,
    multi_scope: bool,
    per_file_cap: usize,
) -> Page {
    let mut groups: Vec<GrepFile> = Vec::new();
    let mut group_by_path = HashMap::new();
    let mut per_file_limit_reached = false;
    for Found {
        path,
        absolute,
        matched,
    } in found
    {
        let index = *group_by_path.entry(path.clone()).or_insert_with(|| {
            groups.push(GrepFile {
                path,
                absolute,
                tag: None,
                matches: Vec::new(),
            });
            groups.len() - 1
        });
        let group = &mut groups[index];
        if group.matches.len() >= per_file_cap {
            per_file_limit_reached = true;
            continue;
        }
        group.matches.push(matched);
    }

    let total_files = u64::try_from(groups.len()).unwrap_or(u64::MAX);
    let skip = if multi_scope { request.skip } else { 0 };
    let file_window = request
        .limit
        .map_or(DEFAULT_FILE_LIMIT, |limit| limit.get().saturating_add(1));
    let start = usize::try_from(skip)
        .unwrap_or(usize::MAX)
        .min(groups.len());
    let end = start.saturating_add(file_window).min(groups.len());
    let file_limit_reached = multi_scope && end < groups.len();
    let mut files: Vec<GrepFile> = groups.drain(start..end).collect();
    let next_skip = skip.saturating_add(u64::try_from(files.len()).unwrap_or(u64::MAX));
    let match_limit_reached = request
        .limit
        .is_some_and(|limit| select_round_robin(&mut files, limit.get()));
    Page {
        files,
        total_files,
        skip,
        next_skip,
        file_limit_reached,
        per_file_limit_reached,
        match_limit_reached,
    }
}

/// The `;`-separated roots of `path`; one root when the whole spelling is an
/// existing path.
fn split_roots(root: &Path, path: &str) -> Vec<String> {
    let whole = normalize_path_input(path);
    if path.contains(';') && fs::metadata(resolve_input_path(root, whole)).is_ok() {
        return vec![whole.to_owned()];
    }
    let roots: Vec<String> = path
        .split(';')
        .map(normalize_path_input)
        .filter(|part| !part.is_empty())
        .map(str::to_owned)
        .collect();
    if roots.is_empty() {
        vec![".".to_owned()]
    } else {
        roots
    }
}

/// An existing file or directory, else the directory before the first glob
/// segment with the rest as its glob; `None` when neither exists.
fn resolve_target(root: &Path, input: &str) -> Result<Option<Target>, GrepError> {
    let literal = resolve_input_path(root, input);
    match fs::metadata(&literal) {
        Ok(metadata) => {
            let canonical = fs::canonicalize(&literal).map_err(workspace_error)?;
            return Ok(Some(if metadata.is_dir() {
                Target::Directory {
                    path: canonical,
                    glob: None,
                }
            } else {
                Target::File(canonical)
            }));
        }
        Err(error) if is_missing(&error) => {}
        Err(error) => return Err(workspace_error(error)),
    }
    let normalized = input.replace('\\', "/");
    let segments: Vec<&str> = normalized.split('/').collect();
    let Some(first_glob) = segments.iter().position(|segment| has_glob_chars(segment)) else {
        return Ok(None);
    };
    let base = if first_glob == 0 {
        ".".to_owned()
    } else {
        segments[..first_glob].join("/")
    };
    let base = resolve_input_path(root, &base);
    match fs::metadata(&base) {
        Ok(metadata) if metadata.is_dir() => Ok(Some(Target::Directory {
            path: fs::canonicalize(&base).map_err(workspace_error)?,
            glob: Some(segments[first_glob..].join("/")),
        })),
        Ok(_) => Ok(None),
        Err(error) if is_missing(&error) => Ok(None),
        Err(error) => Err(workspace_error(error)),
    }
}

/// Keeps at most `limit` matches, taken one per file per round in file
/// order; drops files left without matches. Returns whether matches were cut.
fn select_round_robin(files: &mut Vec<GrepFile>, limit: usize) -> bool {
    let select_limit = limit.saturating_add(1);
    let mut taken = vec![0_usize; files.len()];
    let mut selected = 0_usize;
    let mut last = None;
    let mut round = 0_usize;
    'rounds: loop {
        let mut added = false;
        for (index, file) in files.iter().enumerate() {
            if round >= file.matches.len() {
                continue;
            }
            taken[index] += 1;
            selected += 1;
            last = Some(index);
            added = true;
            if selected >= select_limit {
                break 'rounds;
            }
        }
        if !added {
            break;
        }
        round += 1;
    }
    let cut = selected > limit;
    if let (true, Some(index)) = (cut, last) {
        taken[index] -= 1;
    }
    for (file, keep) in files.iter_mut().zip(&taken) {
        file.matches.truncate(*keep);
    }
    files.retain(|file| !file.matches.is_empty());
    cut
}

fn render(files: &[GrepFile], total_files: u64, multi_scope: bool) -> String {
    let mut output = String::new();
    if files.is_empty() {
        if total_files == 0 {
            output.push_str("No matches found");
        }
        return output;
    }
    if multi_scope {
        let tree = build_path_tree(files.iter().map(|file| (file.path.as_str(), false)));
        let by_path: HashMap<&str, &GrepFile> = files
            .iter()
            .map(|file| (file.path.as_str(), file))
            .collect();
        let mut emitted = false;
        for event in walk_path_tree(&tree) {
            if emitted {
                output.push_str(if event.starts_group() { "\n\n" } else { "\n" });
            }
            emitted = true;
            output.push_str(&"#".repeat(event.heading_level()));
            output.push(' ');
            output.push_str(event.name);
            match event.kind {
                GroupedTreeEventKind::Directory => output.push('/'),
                GroupedTreeEventKind::File => {
                    let file = by_path[event.key];
                    if let Some(tag) = &file.tag {
                        output.push('#');
                        output.push_str(tag);
                    }
                    output.push('\n');
                    render_file_matches(&mut output, file);
                }
            }
        }
    } else {
        for (index, file) in files.iter().enumerate() {
            if index > 0 {
                output.push_str("\n\n");
            }
            if let Some(tag) = &file.tag {
                let _ = writeln!(output, "[{}#{tag}]", file.path);
            }
            render_file_matches(&mut output, file);
        }
    }
    output
}

fn render_file_matches(output: &mut String, file: &GrepFile) {
    let mut last = None;
    let mut push = |number: u32, line: &str, marker: char| {
        if last.is_some_and(|previous: u32| number > previous.saturating_add(1)) {
            output.push_str("...\n");
        }
        let _ = writeln!(output, "{marker}{number}:{line}");
        last = Some(number);
    };
    for matched in &file.matches {
        for context in &matched.context_before {
            push(context.line_number, &context.line, ' ');
        }
        push(matched.line_number, &matched.line, '*');
        for context in &matched.context_after {
            push(context.line_number, &context.line, ' ');
        }
    }
    if output.ends_with('\n') {
        output.pop();
    }
}

fn display_path(root: &Path, path: &Path) -> Result<String, GrepError> {
    workspace_relative(root, path).map_err(workspace_error)
}

fn workspace_error(error: impl std::fmt::Display) -> GrepError {
    GrepError::Workspace {
        message: error.to_string(),
    }
}
