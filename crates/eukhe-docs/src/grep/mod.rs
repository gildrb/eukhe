//! `grep`: regex search over files, grouped by file, with file tags.
//!
//! Every shown file is snapshotted in the session [`EditStore`] from the
//! exact bytes that were searched, so its tag names the text its rows come
//! from. The caller records the rows that reach the model as seen
//! ([`GrepFile::rows`]). Every walked file is accounted for
//! ([`GrepAccount`]), and each class of skipped or cut files gets a notice.
//! Ported from omp `crates/tools/src/grep.rs` (request, paging, rendering)
//! and `crates/envd/src/tool_search.rs` (roots, targets); the per-call match
//! cap is omp v1's `totalMatchLimit` (`packages/coding-agent/src/tools/grep.ts`).

#[cfg(test)]
mod bridge;
#[cfg(test)]
mod bridge_accounts;
mod engine;
#[cfg(test)]
mod tests;

use std::{
    collections::HashMap,
    fmt::Write as _,
    fs,
    num::NonZeroUsize,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use eukhe_types::path_policy::resolve;

use crate::{
    gate::{Access, AccessGate},
    notice::{Notice, NoticeKind, Omitted, Tally, Unit},
    path_tree::{build_path_tree, walk_path_tree, GroupedTreeEventKind},
    read::{
        selector::{line_in_ranges, parse_selector, split_path_and_selector, LineRange, Selector},
        Row,
    },
    scope::{
        has_glob_chars, is_missing, normalize_path_input, resolve_input_path, workspace_relative,
    },
    store::{EditStore, MAX_SNAPSHOT_FILE_BYTES},
    text::{format_bytes, normalize_to_lf, strip_bom},
};

use engine::{FileRead, FileSearcher, RegexOptions};

/// Files shown per page of a multi-file search; `skip` pages further.
pub const DEFAULT_FILE_LIMIT: usize = 20;
/// Matches kept per file when the scope can hold several files.
const MULTI_FILE_PER_FILE_MATCHES: usize = 20;
/// Matches kept when the scope is one file.
const SINGLE_FILE_MATCHES: usize = 200;
/// Matches kept across all files; files after the cap are not searched.
const INTERNAL_TOTAL_CAP: u64 = 2_000;
/// Wall-clock budget of one search.
pub(crate) const SEARCH_GREP_TIMEOUT: Duration = Duration::from_secs(30);
/// Bytes of one shown line kept before a cut; the cut marker follows them.
const DEFAULT_MAX_COLUMN: usize = 512;
/// The start of the marker at the end of a cut row:
/// `…⟨+N bytes⟩`, with N the count of bytes cut.
pub(crate) const CUT_MARKER: &str = "…⟨+";

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
    /// The [`SEARCH_GREP_TIMEOUT`] deadline elapsed.
    #[error(
        "Grep timed out after {}s; narrow paths or pattern, or scope with `glob` first",
        SEARCH_GREP_TIMEOUT.as_secs()
    )]
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
    /// The host's gate refused a target.
    #[error("Did not search {path}: {reason}")]
    Refused {
        /// The target as the model wrote it.
        path: String,
        /// Why the host's gate refused it.
        reason: String,
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
    /// Line text without its line ending (`\n` or `\r\n`).
    pub line: String,
}

/// One matching line and its context.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GrepMatch {
    /// One-based line number.
    pub line_number: u32,
    /// Line text without its line ending (`\n` or `\r\n`).
    pub line: String,
    /// Whether `line` was cut after 512 bytes (it then ends with the cut
    /// marker `…⟨+N bytes⟩`).
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
    /// File tag of the searched text; absent for a file over the size limit
    /// ([`MAX_SNAPSHOT_FILE_BYTES`]) or not UTF-8 (a notice says which).
    pub tag: Option<String>,
    /// Matches in source order.
    pub matches: Vec<GrepMatch>,
    /// Every shown row (match and context) of this file, in the order
    /// [`GrepOutput::render`] shows them.
    pub rows: Vec<Row>,
}

/// What happened to each file the search reached. The walk entries are
/// `no_match + shown + paged_out + not_searched + binary + unreadable +
/// excluded + symlink + walk_error`; a file named by several roots counts
/// once.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct GrepAccount {
    /// Searched files without a match.
    pub no_match: u64,
    /// Matching files shown on this page.
    pub shown: u64,
    /// Matching files on other pages.
    pub paged_out: u64,
    /// Files not opened because the total match cap was reached first.
    pub not_searched: u64,
    /// Searched files over the size limit: only their first bytes were
    /// searched. They are also in `no_match`, `shown`, or `paged_out`.
    pub partial: u64,
    /// Files with a NUL byte, not searched.
    pub binary: u64,
    /// Files that could not be read (no permission, vanished, not a
    /// regular file).
    pub unreadable: u64,
    /// `.git` and `node_modules` entries the walk did not enter.
    pub excluded: u64,
    /// Symbolic links; the walk does not follow them.
    pub symlink: u64,
    /// Entries the walk could not read.
    pub walk_error: u64,
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
    /// Whether the total match cap stopped the search, so `total_files` is
    /// a lower bound.
    pub total_files_lower_bound: bool,
    /// Whether the scope can hold several files (a directory, a glob, or
    /// several roots).
    pub multi_scope: bool,
    /// Files skipped before this page.
    pub skip: u64,
    /// Whether more matching files follow this page.
    pub file_limit_reached: bool,
    /// Whether a file had more matches than it kept (its per-file cap or
    /// the total cap).
    pub per_file_limit_reached: bool,
    /// Whether `limit` cut matches.
    pub match_limit_reached: bool,
    /// What happened to each file the search reached.
    pub account: GrepAccount,
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

/// The caps of one search.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct GrepLimits {
    /// Bytes searched of one file; a larger file is searched in part and
    /// gets no tag.
    pub(crate) max_file_bytes: u64,
    /// Matches kept across all files.
    pub(crate) total_matches: u64,
}

impl GrepLimits {
    /// The limits of the `grep` tool.
    pub(crate) const DEFAULT: Self = Self {
        max_file_bytes: MAX_SNAPSHOT_FILE_BYTES,
        total_matches: INTERNAL_TOTAL_CAP,
    };
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

/// One file to search, once, with the lines its roots keep (empty: all).
struct Queued {
    path: PathBuf,
    ranges: Vec<LineRange>,
}

/// The files the roots reach and the entries the walks did not give.
#[derive(Default)]
struct Collected {
    files: Vec<Queued>,
    excluded: Tally,
    symlinks: Tally,
    walk_errors: Tally,
}

/// A matching file before paging.
struct FileHit {
    path: String,
    absolute: PathBuf,
    matches: Vec<GrepMatch>,
    /// More matches exist than the file kept.
    cut: Option<Cut>,
}

/// The matches a cut file had: `found`, a lower bound when `more` is set.
#[derive(Clone, Copy)]
struct Cut {
    found: usize,
    more: bool,
}

/// What the search phase gathered before paging.
#[derive(Default)]
struct Searched {
    found: Vec<FileHit>,
    /// The searched bytes of each file that can be on the requested page,
    /// and whether that is the whole file.
    kept: HashMap<PathBuf, (Vec<u8>, FileRead)>,
    no_match: u64,
    /// Files after the total cap, never opened.
    unsearched: u64,
    binary: Tally,
    unreadable: Tally,
    partial: Tally,
}

/// One page of matching files.
struct Page {
    files: Vec<GrepFile>,
    cuts: Vec<Option<Cut>>,
    total_files: u64,
    skip: u64,
    next_skip: u64,
    file_limit_reached: bool,
    match_limit_reached: bool,
}

/// Search `request.path` under `cwd`, each target after `gate` let the read
/// (a file) or the search (a directory) of its real path, and render the
/// result. Shown files are snapshotted from the searched bytes; seen lines
/// are not recorded (the caller records [`GrepFile::rows`] that reach the
/// model).
///
/// # Errors
/// [`GrepError`] for an empty pattern, an unusable regex or glob, all targets
/// missing, a target the gate refused, a filesystem failure, or the
/// [`SEARCH_GREP_TIMEOUT`] deadline.
pub(crate) fn grep(
    store: &EditStore,
    cwd: &Path,
    request: &GrepRequest,
    gate: &dyn AccessGate,
) -> Result<GrepOutput, GrepError> {
    grep_with(store, cwd, request, gate, GrepLimits::DEFAULT, &|| {})
}

/// [`grep`] with explicit `limits`; `between` runs once after the search and
/// before any file is recorded in `store` (tests change files there).
///
/// # Errors
/// As [`grep`].
#[allow(
    clippy::too_many_lines,
    reason = "one search in order: resolve, search, page, record, render, account"
)]
pub(crate) fn grep_with(
    store: &EditStore,
    cwd: &Path,
    request: &GrepRequest,
    gate: &dyn AccessGate,
    limits: GrepLimits,
    between: &dyn Fn(),
) -> Result<GrepOutput, GrepError> {
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
            Some(target) => {
                let (access, real) = match &target {
                    Target::File(path) => (Access::Read, path),
                    Target::Directory { path, .. } => (Access::Search, path),
                };
                gate.check(access, &resolve(real), input)
                    .map_err(|reason| GrepError::Refused {
                        path: input.clone(),
                        reason,
                    })?;
                targets.push(Scoped { target, ranges });
            }
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
    let skip = if multi_scope { request.skip } else { 0 };
    let window = request
        .limit
        .map_or(DEFAULT_FILE_LIMIT, |limit| limit.get().saturating_add(1));
    let collected = collect_files(&root, &targets, request, deadline)?;
    let mut searched = search_files(
        &root,
        &collected.files,
        request,
        limits,
        per_file_cap,
        (skip, window),
        deadline,
    )?;
    let mut page = page_files(
        std::mem::take(&mut searched.found),
        request,
        skip,
        window,
        multi_scope,
    );

    between();
    let mut untagged = Tally::default();
    for file in &mut page.files {
        let Some((bytes, read)) = searched.kept.remove(&file.absolute) else {
            continue;
        };
        match read {
            FileRead::Partial => untagged.add(|| {
                format!(
                    "{} (over {}: `edit` cannot change it; read it in ranges, then change it with `write` (whole file) or `bash`)",
                    file.path,
                    format_bytes(limits.max_file_bytes)
                )
            }),
            FileRead::Whole => {
                store.saw_bytes(&file.absolute, &bytes);
                match std::str::from_utf8(&bytes) {
                    Ok(text) => {
                        let text = normalize_to_lf(strip_bom(text).1);
                        file.tag = Some(store.record(&file.absolute, &text, None));
                    }
                    Err(_) => untagged.add(|| {
                        format!(
                            "{} ({}: `edit` works on UTF-8 only; `write` replaces it as UTF-8)",
                            file.path,
                            crate::text::encoding_name(&bytes)
                        )
                    }),
                }
            }
        }
    }

    let (text, rows) = render(&page.files, page.total_files, multi_scope);
    for (file, rows) in page.files.iter_mut().zip(rows) {
        file.rows = rows;
    }
    let shown = u64::try_from(page.files.len()).unwrap_or(u64::MAX);
    let account = GrepAccount {
        no_match: searched.no_match,
        shown,
        paged_out: page.total_files.saturating_sub(shown),
        not_searched: searched.unsearched,
        partial: searched.partial.count,
        binary: searched.binary.count,
        unreadable: searched.unreadable.count,
        excluded: collected.excluded.count,
        symlink: collected.symlinks.count,
        walk_error: collected.walk_errors.count,
    };
    let notices = notices(&Noticed {
        missing_paths: &missing_paths,
        collected: &collected,
        searched: &searched,
        untagged: &untagged,
        page: &page,
        multi_scope,
        limit: request.limit,
        limits,
    });
    Ok(GrepOutput {
        per_file_limit_reached: page.cuts.iter().any(Option::is_some),
        files: page.files,
        total_files: page.total_files,
        total_files_lower_bound: searched.unsearched > 0,
        multi_scope,
        skip: page.skip,
        file_limit_reached: page.file_limit_reached,
        match_limit_reached: page.match_limit_reached,
        account,
        notices,
        text,
    })
}

/// The facts the notices of one result come from.
struct Noticed<'a> {
    missing_paths: &'a [String],
    collected: &'a Collected,
    searched: &'a Searched,
    untagged: &'a Tally,
    page: &'a Page,
    multi_scope: bool,
    limit: Option<NonZeroUsize>,
    limits: GrepLimits,
}

/// The notices of a result: skipped inputs, cut files, then paging, then
/// the match limit. Each class of skipped or cut files gets one notice
/// with its count and a few examples.
#[allow(
    clippy::too_many_lines,
    reason = "one notice per class, in the order the model reads them"
)]
fn notices(facts: &Noticed<'_>) -> Vec<Notice> {
    let Noticed {
        missing_paths,
        collected,
        searched,
        untagged,
        page,
        multi_scope,
        limit,
        limits,
    } = *facts;
    let mut notices = Vec::new();
    if !missing_paths.is_empty() {
        notices.push(Notice::warn(
            NoticeKind::MissingPaths,
            missing_paths.join(", "),
        ));
    }
    let size = format_bytes(limits.max_file_bytes);
    let skipped = [
        (&searched.binary, "binary files (a NUL byte) not searched".to_owned()),
        (&searched.unreadable, "unreadable files not searched".to_owned()),
        (
            &collected.excluded,
            "excluded directories not searched (`.git` always; `node_modules` unless the path or glob names it)".to_owned(),
        ),
        (
            &collected.symlinks,
            "symlinks not followed (name the target path to search it)".to_owned(),
        ),
        (&collected.walk_errors, "walk errors (these entries were not searched)".to_owned()),
    ];
    for (tally, what) in skipped {
        if let Some(text) = tally.describe(&what) {
            notices.push(Notice::warn(NoticeKind::Skipped, text));
        }
    }
    if let Some(text) = searched.partial.describe(&format!(
        "files over {size}: only their first {size} was searched"
    )) {
        notices.push(Notice::warn(NoticeKind::PartialScan, text));
    }
    if let Some(text) = untagged.describe("shown files have no tag, so `edit` cannot change them") {
        notices.push(Notice::warn(NoticeKind::NotEditable, text));
    }
    if searched.unsearched > 0 {
        notices.push(Notice::warn(
            NoticeKind::LimitReached,
            format!(
                "{} files not searched: the {}-match total was reached; narrow the path or the pattern",
                searched.unsearched, limits.total_matches
            ),
        ));
    }
    for (file, cut) in page.files.iter().zip(&page.cuts) {
        let (Some(cut), Some(last)) = (cut, file.matches.last()) else {
            continue;
        };
        let more = if cut.more { "+" } else { "" };
        let next = format!("{}:{}-", file.path, last.line_number.saturating_add(1));
        let advice = if multi_scope {
            format!("search {} alone, or {next}", file.path)
        } else {
            format!("search {next}")
        };
        notices.push(Notice {
            continuation: Some(format!("path={next}")),
            ..Notice::warn(
                NoticeKind::LimitReached,
                format!(
                    "{}: {} of {}{more} matches shown; {advice}",
                    file.path,
                    file.matches.len(),
                    cut.found
                ),
            )
        });
    }
    let (skip, total_files) = (page.skip, page.total_files);
    let suffix = if searched.unsearched > 0 { "+" } else { "" };
    if page.files.is_empty() && multi_scope && skip > 0 && total_files > 0 && skip >= total_files {
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
                    "files {}-{next_skip} of {total_files}{suffix}",
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

/// Every file the targets reach, in target order, each once: a file named
/// by several roots keeps the union of their lines (all lines when one root
/// has no selector).
fn collect_files(
    root: &Path,
    targets: &[Scoped],
    request: &GrepRequest,
    deadline: Instant,
) -> Result<Collected, GrepError> {
    let mut collected = Collected::default();
    let mut index_of: HashMap<PathBuf, usize> = HashMap::new();
    for Scoped { target, ranges } in targets {
        let files = match target {
            Target::File(path) => vec![path.clone()],
            Target::Directory { path, glob } => {
                let globs = glob
                    .iter()
                    .chain(request.glob.iter().filter(|glob| !glob.trim().is_empty()))
                    .map(|source| Ok((source.clone(), engine::compile_walk_glob(source)?)))
                    .collect::<Result<Vec<_>, GrepError>>()?;
                let walk = engine::walk_files(path, root, &globs, request.gitignore, deadline)?;
                collected.excluded.absorb(walk.excluded);
                collected.symlinks.absorb(walk.symlinks);
                collected.walk_errors.absorb(walk.errors);
                walk.files
            }
        };
        for file in files {
            if let Some(&index) = index_of.get(&file) {
                let queued: &mut Queued = &mut collected.files[index];
                if queued.ranges.is_empty() || ranges.is_empty() {
                    queued.ranges.clear();
                } else {
                    queued.ranges.extend_from_slice(ranges);
                }
                continue;
            }
            index_of.insert(file.clone(), collected.files.len());
            collected.files.push(Queued {
                path: file,
                ranges: ranges.clone(),
            });
        }
    }
    Ok(collected)
}

/// Searches each file once, in order. A file keeps at most `per_file_cap`
/// matches and the total keeps at most `limits.total_matches`; files after
/// the total cap are not searched. A file whose search found more matches
/// than it kept is cut. The searched bytes of the matching files whose
/// order falls in `page` (`skip`, `window`) are kept for the store.
#[allow(
    clippy::too_many_lines,
    reason = "one loop that classifies each file into exactly one account class"
)]
fn search_files(
    root: &Path,
    files: &[Queued],
    request: &GrepRequest,
    limits: GrepLimits,
    per_file_cap: usize,
    (skip, window): (u64, usize),
    deadline: Instant,
) -> Result<Searched, GrepError> {
    let options = RegexOptions::for_pattern(&request.pattern, request.ignore_case);
    let regex = engine::build_matcher(&request.pattern, options)?;
    let mut file_searcher = FileSearcher::new(
        request.context_before,
        request.context_after,
        options,
        DEFAULT_MAX_COLUMN,
    );
    let per_file_cap = u64::try_from(per_file_cap).unwrap_or(u64::MAX);
    let page_end = skip.saturating_add(u64::try_from(window).unwrap_or(u64::MAX));
    let mut searched = Searched::default();
    let mut remaining = limits.total_matches;
    let mut matching = 0_u64;
    let mut buffer = Vec::new();
    for (index, Queued { path, ranges }) in files.iter().enumerate() {
        if remaining == 0 {
            searched.unsearched = u64::try_from(files.len() - index).unwrap_or(u64::MAX);
            break;
        }
        if Instant::now() >= deadline {
            return Err(GrepError::TimedOut);
        }
        let read = match engine::read_file(path, &mut buffer, limits.max_file_bytes) {
            Ok(read) => read,
            Err(error) => {
                searched
                    .unreadable
                    .add(|| format!("{} ({error})", shown_path(root, path)));
                continue;
            }
        };
        // The searcher drops a UTF-8 BOM itself (BOM sniffing), so row 1
        // is the same text as read's row 1.
        if buffer.contains(&0) {
            searched.binary.add(|| shown_path(root, path));
            continue;
        }
        match read {
            FileRead::Partial => searched.partial.add(|| shown_path(root, path)),
            FileRead::Whole => {}
        }
        let cap = per_file_cap.min(remaining);
        let fetch = if ranges.is_empty() {
            cap.saturating_add(1)
        } else {
            let baseline = per_file_cap.saturating_add(1);
            baseline.max(range_fetch(ranges, baseline, limits.max_file_bytes))
        };
        let hits = file_searcher
            .search(&regex, &buffer, fetch)
            .map_err(workspace_error)?;
        let mut matches = hits.matches;
        if !ranges.is_empty() {
            let inside = |line: &ContextLine| line_in_ranges(u64::from(line.line_number), ranges);
            matches.retain(|matched| line_in_ranges(u64::from(matched.line_number), ranges));
            for matched in &mut matches {
                matched.context_before.retain(inside);
                matched.context_after.retain(inside);
            }
        }
        if matches.is_empty() {
            searched.no_match += 1;
            continue;
        }
        let found = matches.len();
        let keep = usize::try_from(cap).unwrap_or(usize::MAX).min(found);
        matches.truncate(keep);
        remaining -= u64::try_from(keep).unwrap_or(u64::MAX);
        let absolute = eukhe_types::path_policy::real_path(path);
        if (skip..page_end).contains(&matching) {
            searched
                .kept
                .insert(absolute.clone(), (std::mem::take(&mut buffer), read));
        }
        matching += 1;
        searched.found.push(FileHit {
            path: display_path(root, &absolute)?,
            absolute,
            matches,
            cut: (found > keep).then_some(Cut {
                found,
                more: hits.limit_reached,
            }),
        });
    }
    Ok(searched)
}

/// Matches to fetch from one file of a line-ranged root so that every match
/// up to the last selected line is reached; an open range keeps
/// `baseline` past its start (omp `fetch_budgets`). A file of `max_bytes`
/// bytes has no more lines than that.
fn range_fetch(ranges: &[LineRange], baseline: u64, max_bytes: u64) -> u64 {
    ranges
        .iter()
        .map(|range| {
            range
                .end_line
                .unwrap_or_else(|| range.start_line.saturating_sub(1).saturating_add(baseline))
        })
        .max()
        .unwrap_or(0)
        .min(max_bytes.saturating_add(1))
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

/// Cuts the requested page from the matching files in search order:
/// `window` files from `skip`, with `limit` matches taken round-robin.
fn page_files(
    found: Vec<FileHit>,
    request: &GrepRequest,
    skip: u64,
    window: usize,
    multi_scope: bool,
) -> Page {
    let total = found.len();
    let total_files = u64::try_from(total).unwrap_or(u64::MAX);
    let start = usize::try_from(skip).unwrap_or(usize::MAX).min(total);
    let end = start.saturating_add(window).min(total);
    let file_limit_reached = multi_scope && end < total;
    let (mut files, mut cuts): (Vec<GrepFile>, Vec<Option<Cut>>) = found
        .into_iter()
        .skip(start)
        .take(end - start)
        .map(|hit| {
            (
                GrepFile {
                    path: hit.path,
                    absolute: hit.absolute,
                    tag: None,
                    matches: hit.matches,
                    rows: Vec::new(),
                },
                hit.cut,
            )
        })
        .unzip();
    let next_skip = skip.saturating_add(u64::try_from(files.len()).unwrap_or(u64::MAX));
    let match_limit_reached = request.limit.is_some_and(|limit| {
        let cut = select_round_robin(&mut files, limit.get());
        // The first round takes one match of each file in order, so the
        // files it drops are the last ones.
        cuts.truncate(files.len());
        cut
    });
    Page {
        files,
        cuts,
        total_files,
        skip,
        next_skip,
        file_limit_reached,
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

/// The model-facing text of `files` and, per file, the rows it shows.
fn render(files: &[GrepFile], total_files: u64, multi_scope: bool) -> (String, Vec<Vec<Row>>) {
    let mut output = String::new();
    let mut rows = vec![Vec::new(); files.len()];
    if files.is_empty() {
        if total_files == 0 {
            output.push_str("No matches found");
        }
        return (output, rows);
    }
    let mut counter = LineCounter::default();
    if multi_scope {
        let tree = build_path_tree(files.iter().map(|file| (file.path.as_str(), false)));
        let by_path: HashMap<&str, usize> = files
            .iter()
            .enumerate()
            .map(|(index, file)| (file.path.as_str(), index))
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
                    let index = by_path[event.key];
                    let file = &files[index];
                    if let Some(tag) = &file.tag {
                        output.push('#');
                        output.push_str(tag);
                    }
                    output.push('\n');
                    rows[index] = render_file_matches(&mut output, &mut counter, file);
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
            rows[index] = render_file_matches(&mut output, &mut counter, file);
        }
    }
    (output, rows)
}

/// Counts the lines of a growing text once: the bytes already scanned and
/// the line breaks found in them.
#[derive(Default)]
struct LineCounter {
    scanned: usize,
    breaks: usize,
}

impl LineCounter {
    /// The 0-based index of the line that starts at the end of `output`.
    fn next_line(&mut self, output: &str) -> usize {
        self.breaks += output[self.scanned..].matches('\n').count();
        self.scanned = output.len();
        self.breaks
    }
}

/// Writes the rows of `file` and returns where each one is.
fn render_file_matches(
    output: &mut String,
    counter: &mut LineCounter,
    file: &GrepFile,
) -> Vec<Row> {
    let mut rows = Vec::new();
    let mut last = None;
    let mut push = |number: u32, line: &str, marker: char| {
        if last.is_some_and(|previous: u32| number > previous.saturating_add(1)) {
            output.push_str("...\n");
        }
        rows.push(Row {
            line: number,
            at: counter.next_line(output),
        });
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
    rows
}

/// `path` as a notice names it: relative to `root` when inside it.
fn shown_path(root: &Path, path: &Path) -> String {
    workspace_relative(root, path).unwrap_or_else(|_| path.display().to_string())
}

fn display_path(root: &Path, path: &Path) -> Result<String, GrepError> {
    workspace_relative(root, path).map_err(workspace_error)
}

fn workspace_error(error: impl std::fmt::Display) -> GrepError {
    GrepError::Workspace {
        message: error.to_string(),
    }
}
