//! The search engine under `grep`: matcher construction with omp's repairs,
//! the bounded file read, the gitignore-aware walk, and one file's search.
//!
//! Ported from omp `crates/envd/src/grep.rs`; per-file matching runs through
//! `grep-searcher` as in omp v1 `crates/pi-natives/src/grep.rs`, so a line is
//! reported once even when match contexts overlap.

use std::{
    borrow::Cow,
    fs::File,
    io::{self, Read},
    iter,
    path::{Path, PathBuf},
    sync::{Arc, Mutex, PoisonError},
    time::Instant,
};

use globset::{GlobBuilder, GlobMatcher};
use grep_regex::{RegexMatcher, RegexMatcherBuilder};
use grep_searcher::{
    BinaryDetection, Searcher, SearcherBuilder, Sink, SinkContext, SinkContextKind, SinkMatch,
};

use super::{ContextLine, GrepError, GrepMatch};
use crate::{
    notice::Tally,
    scope::{is_eukhe_temp, workspace_relative},
};

/// Regex options of one search.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct RegexOptions {
    /// Match without regard to case.
    pub(super) ignore_case: bool,
    /// Let matches span lines: set when the pattern holds a literal newline or
    /// a `\n` escape.
    pub(super) multiline: bool,
}

impl RegexOptions {
    pub(super) fn for_pattern(pattern: &str, ignore_case: bool) -> Self {
        Self {
            ignore_case,
            multiline: pattern.contains('\n') || pattern.contains("\\n"),
        }
    }
}

fn build_regex_matcher(
    pattern: &str,
    options: RegexOptions,
) -> Result<RegexMatcher, grep_regex::Error> {
    let build = |line_terminated: bool| {
        let mut builder = RegexMatcherBuilder::new();
        builder
            .case_insensitive(options.ignore_case)
            .multi_line(options.multiline);
        if line_terminated {
            builder.line_terminator(Some(b'\n'));
        }
        builder.build(pattern)
    };
    if !options.multiline {
        if let Ok(matcher) = build(true) {
            return Ok(matcher);
        }
    }
    build(false)
}

/// Compiles `pattern`. An invalid pattern is repaired in omp's order: stray
/// braces are escaped first, then stray parentheses, and the last resort
/// searches the pattern as a literal.
pub(super) fn build_matcher(
    pattern: &str,
    options: RegexOptions,
) -> Result<RegexMatcher, GrepError> {
    let sanitized = sanitize_braces(pattern);
    let regex_error = match build_regex_matcher(sanitized.as_ref(), options) {
        Ok(matcher) => return Ok(matcher),
        Err(error) => error,
    };
    let message = regex_error.to_string();
    if message.contains("unclosed group") || message.contains("unopened group") {
        let escaped = escape_unescaped_parentheses(sanitized.as_ref());
        if escaped.as_ref() != sanitized.as_ref() {
            if let Ok(matcher) = build_regex_matcher(escaped.as_ref(), options) {
                return Ok(matcher);
            }
        }
    }
    build_regex_matcher(&regex::escape(pattern), options).map_err(|_| GrepError::InvalidRegex {
        message: strip_regex_error_prefix(&message).to_owned(),
    })
}

fn strip_regex_error_prefix(message: &str) -> &str {
    for prefix in ["regex parse error:", "regex error:"] {
        if message
            .get(..prefix.len())
            .is_some_and(|candidate| candidate.eq_ignore_ascii_case(prefix))
        {
            return message[prefix.len()..].trim_start();
        }
    }
    message
}

/// Quotes literal parentheses after the regex engine reports invalid group
/// syntax, preserving escaped parentheses and every other operator.
fn escape_unescaped_parentheses(pattern: &str) -> Cow<'_, str> {
    if !pattern.contains(['(', ')']) {
        return Cow::Borrowed(pattern);
    }
    let mut escaped = String::with_capacity(pattern.len() + 4);
    let mut modified = false;
    let mut characters = pattern.chars();
    while let Some(character) = characters.next() {
        if character == '\\' {
            escaped.push('\\');
            if let Some(next) = characters.next() {
                escaped.push(next);
            }
            continue;
        }
        if matches!(character, '(' | ')') {
            escaped.push('\\');
            modified = true;
        }
        escaped.push(character);
    }
    if modified {
        Cow::Owned(escaped)
    } else {
        Cow::Borrowed(pattern)
    }
}

/// Escapes braces that are not a valid `{n}`, `{n,}`, or `{n,m}` repetition
/// or the body of a `\p{..}`, `\P{..}`, `\x{..}`, or `\u{..}` escape.
fn sanitize_braces(pattern: &str) -> Cow<'_, str> {
    let bytes = pattern.as_bytes();
    if !bytes.contains(&b'{') && !bytes.contains(&b'}') {
        return Cow::Borrowed(pattern);
    }
    let mut output = String::with_capacity(pattern.len() + 8);
    let mut modified = false;
    let mut index = 0;
    while let Some(character) = pattern[index..].chars().next() {
        if character == '\\' {
            output.push('\\');
            index += 1;
            let Some(escaped) = pattern[index..].chars().next() else {
                break;
            };
            output.push(escaped);
            index += escaped.len_utf8();
            if matches!(escaped, 'p' | 'P' | 'x' | 'u') && bytes.get(index) == Some(&b'{') {
                if let Some(end) = find_braced_escape_end(bytes, index) {
                    output.push_str(&pattern[index..=end]);
                    index = end + 1;
                } else {
                    output.push_str(&pattern[index..]);
                    index = bytes.len();
                }
            }
            continue;
        }
        if character == '{' {
            if let Some(end) = find_valid_repetition(bytes, index) {
                output.push_str(&pattern[index..=end]);
                index = end + 1;
                continue;
            }
            output.push_str("\\{");
            index += 1;
            modified = true;
            continue;
        }
        if character == '}' {
            output.push_str("\\}");
            index += 1;
            modified = true;
            continue;
        }
        output.push(character);
        index += character.len_utf8();
    }
    if modified {
        Cow::Owned(output)
    } else {
        Cow::Borrowed(pattern)
    }
}

const fn find_valid_repetition(bytes: &[u8], start: usize) -> Option<usize> {
    let mut index = start + 1;
    if index >= bytes.len() || !bytes[index].is_ascii_digit() {
        return None;
    }
    while index < bytes.len() && bytes[index].is_ascii_digit() {
        index += 1;
    }
    if index >= bytes.len() {
        return None;
    }
    if bytes[index] == b'}' {
        return Some(index);
    }
    if bytes[index] != b',' {
        return None;
    }
    index += 1;
    while index < bytes.len() && bytes[index].is_ascii_digit() {
        index += 1;
    }
    if index < bytes.len() && bytes[index] == b'}' {
        Some(index)
    } else {
        None
    }
}

const fn find_braced_escape_end(bytes: &[u8], start: usize) -> Option<usize> {
    let mut index = start + 1;
    while index < bytes.len() {
        if bytes[index] == b'}' {
            return Some(index);
        }
        index += 1;
    }
    None
}

/// Makes a bare file-name glob match at any depth (`*.rs` -> `**/*.rs`) and
/// closes unbalanced braces.
fn normalize_recursive_glob(glob: &str) -> String {
    let normalized = glob.replace('\\', "/");
    let mut pattern = if normalized.contains('/')
        || normalized.starts_with("**")
        || is_exact_brace_union(&normalized)
    {
        normalized
    } else {
        format!("**/{normalized}")
    };
    let opens = pattern.bytes().filter(|byte| *byte == b'{').count();
    let closes = pattern.bytes().filter(|byte| *byte == b'}').count();
    if opens > closes {
        pattern.extend(iter::repeat_n('}', opens - closes));
    }
    pattern
}

fn is_exact_brace_union(pattern: &str) -> bool {
    let Some(inner) = pattern
        .strip_prefix('{')
        .and_then(|rest| rest.strip_suffix('}'))
    else {
        return false;
    };
    !inner.is_empty()
        && !inner
            .chars()
            .any(|character| matches!(character, '*' | '?' | '[' | ']' | '{' | '}'))
}

/// Compiles a walk filter glob; `*`, `?`, and classes do not cross `/`.
pub(super) fn compile_walk_glob(glob: &str) -> Result<GlobMatcher, GrepError> {
    let pattern = normalize_recursive_glob(glob.trim());
    GlobBuilder::new(&pattern)
        .literal_separator(true)
        .build()
        .map(|glob| glob.compile_matcher())
        .map_err(|error| GrepError::Workspace {
            message: format!("invalid glob pattern: {error}"),
        })
}

/// What a directory walk found: the files to search, and the entries it
/// did not give, one [`Tally`] per reason.
#[derive(Default)]
pub(super) struct Walk {
    /// Regular files in path order.
    pub(super) files: Vec<PathBuf>,
    /// `.git` and `node_modules` entries the walk did not enter.
    pub(super) excluded: Tally,
    /// Symbolic links; the walk does not follow them.
    pub(super) symlinks: Tally,
    /// Entries the walk could not read (no permission, vanished, a bad
    /// ignore file, and other errors).
    pub(super) errors: Tally,
}

/// Regular files under `root` in path order, filtered by every glob in
/// `globs` (matched against the `/`-separated path relative to `root`).
/// `.git` is never entered; `node_modules` only when a glob names it;
/// eukhe temporary files are hidden. Examples in the tallies are shown
/// relative to `shown_root`.
pub(super) fn walk_files(
    root: &Path,
    shown_root: &Path,
    globs: &[(String, GlobMatcher)],
    gitignore: bool,
    deadline: Instant,
) -> Result<Walk, GrepError> {
    let mentions_node_modules = globs
        .iter()
        .any(|(source, _)| source.contains("node_modules"));
    let excluded = Arc::new(Mutex::new(Tally::default()));
    let excluded_sink = Arc::clone(&excluded);
    let filter_root = shown_root.to_owned();
    let mut builder = ignore::WalkBuilder::new(root);
    builder
        .hidden(false)
        .ignore(gitignore)
        .git_ignore(gitignore)
        .git_global(gitignore)
        .git_exclude(gitignore)
        .parents(gitignore)
        .require_git(false)
        .follow_links(false)
        .sort_by_file_name(Ord::cmp)
        .filter_entry(move |entry| {
            let name = entry.file_name();
            if is_eukhe_temp(name) {
                return false;
            }
            let keep = name != ".git" && (mentions_node_modules || name != "node_modules");
            if !keep {
                excluded_sink
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .add(|| shown(&filter_root, entry.path()));
            }
            keep
        });
    let mut walk = Walk::default();
    for entry in builder.build() {
        if Instant::now() >= deadline {
            return Err(GrepError::TimedOut);
        }
        let entry = match entry {
            Ok(entry) => entry,
            Err(error) => {
                walk.errors.add(|| error.to_string());
                continue;
            }
        };
        let Some(kind) = entry.file_type() else {
            continue;
        };
        if entry.depth() == 0 || !(kind.is_file() || kind.is_symlink()) {
            continue;
        }
        let Ok(relative) = entry.path().strip_prefix(root) else {
            continue;
        };
        let relative = relative.to_string_lossy().replace('\\', "/");
        if !globs.iter().all(|(_, glob)| glob.is_match(&relative)) {
            continue;
        }
        if kind.is_symlink() {
            walk.symlinks.add(|| shown(shown_root, entry.path()));
        } else {
            walk.files.push(entry.into_path());
        }
    }
    walk.excluded = std::mem::take(&mut *excluded.lock().unwrap_or_else(PoisonError::into_inner));
    Ok(walk)
}

/// `path` as a notice names it: relative to `root` when inside it.
fn shown(root: &Path, path: &Path) -> String {
    workspace_relative(root, path).unwrap_or_else(|_| path.display().to_string())
}

/// How much of a file [`read_file`] put in the buffer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FileRead {
    /// The whole file.
    Whole,
    /// The file is larger than the size limit: only its first bytes.
    Partial,
}

/// Reads `path` into `buffer`: the whole file, or its first `max_bytes`
/// bytes when it is larger.
///
/// # Errors
/// The file cannot be opened or read, or it is not a regular file.
pub(super) fn read_file(path: &Path, buffer: &mut Vec<u8>, max_bytes: u64) -> io::Result<FileRead> {
    let file = File::open(path)?;
    let metadata = file.metadata()?;
    if !metadata.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "not a regular file",
        ));
    }
    buffer.clear();
    buffer.reserve(usize::try_from(metadata.len().min(max_bytes)).unwrap_or(0));
    file.take(max_bytes.saturating_add(1)).read_to_end(buffer)?;
    let limit = usize::try_from(max_bytes).unwrap_or(usize::MAX);
    if buffer.len() > limit {
        buffer.truncate(limit);
        Ok(FileRead::Partial)
    } else {
        Ok(FileRead::Whole)
    }
}

/// Per-file search configuration shared by every file of one request.
pub(super) struct FileSearcher {
    searcher: Searcher,
    max_columns: usize,
}

/// Matches of one file and whether its fetch cap stopped the search.
pub(super) struct FileHits {
    pub(super) matches: Vec<GrepMatch>,
    pub(super) limit_reached: bool,
}

impl FileSearcher {
    pub(super) fn new(
        context_before: u32,
        context_after: u32,
        options: RegexOptions,
        max_columns: usize,
    ) -> Self {
        let searcher = SearcherBuilder::new()
            .binary_detection(BinaryDetection::none())
            .line_number(true)
            .multi_line(options.multiline)
            .before_context(usize::try_from(context_before).unwrap_or(usize::MAX))
            .after_context(usize::try_from(context_after).unwrap_or(usize::MAX))
            .build();
        Self {
            searcher,
            max_columns,
        }
    }

    /// Searches `content`, stopping after `max_count` (at least one) matching
    /// lines; the after-context of the last one still arrives.
    pub(super) fn search(
        &mut self,
        matcher: &RegexMatcher,
        content: &[u8],
        max_count: u64,
    ) -> io::Result<FileHits> {
        let mut collector = Collector {
            max_columns: self.max_columns,
            max_count,
            collected: 0,
            limit_reached: false,
            pending_before: Vec::new(),
            matches: Vec::new(),
        };
        self.searcher
            .search_slice(matcher, content, &mut collector)?;
        Ok(FileHits {
            limit_reached: collector.limit_reached,
            matches: collector.matches,
        })
    }
}

struct Collector {
    max_columns: usize,
    max_count: u64,
    collected: u64,
    limit_reached: bool,
    pending_before: Vec<ContextLine>,
    matches: Vec<GrepMatch>,
}

impl Sink for Collector {
    type Error = io::Error;

    fn matched(&mut self, _searcher: &Searcher, matched: &SinkMatch<'_>) -> io::Result<bool> {
        if self.limit_reached {
            return Ok(false);
        }
        let first = line_number(matched.line_number())?;
        for (offset, bytes) in (0_u64..).zip(matched.lines()) {
            let (line, truncated) = row_text(bytes, self.max_columns);
            self.matches.push(GrepMatch {
                line_number: clamp_u32(first.saturating_add(offset)),
                line,
                truncated,
                context_before: if offset == 0 {
                    std::mem::take(&mut self.pending_before)
                } else {
                    Vec::new()
                },
                context_after: Vec::new(),
            });
            self.collected = self.collected.saturating_add(1);
        }
        if self.collected >= self.max_count {
            self.limit_reached = true;
        }
        Ok(true)
    }

    fn context(&mut self, _searcher: &Searcher, context: &SinkContext<'_>) -> io::Result<bool> {
        let (line, _) = row_text(context.bytes(), self.max_columns);
        let line = ContextLine {
            line_number: clamp_u32(line_number(context.line_number())?),
            line,
        };
        match context.kind() {
            SinkContextKind::Before => self.pending_before.push(line),
            SinkContextKind::After => {
                if let Some(last) = self.matches.last_mut() {
                    last.context_after.push(line);
                }
            }
            SinkContextKind::Other => {}
        }
        Ok(true)
    }
}

fn line_number(number: Option<u64>) -> io::Result<u64> {
    number.ok_or_else(|| io::Error::other("the searcher reported a line without its number"))
}

/// The text of one line without its terminator (`\n` or `\r\n`; other
/// trailing characters stay), and whether it was cut. A line longer than
/// `max_columns` bytes keeps its first `max_columns` bytes (at a character
/// boundary) and ends with [`super::CUT_MARKER`] and the count of bytes cut,
/// so a cut row cannot look like the whole line.
fn row_text(bytes: &[u8], max_columns: usize) -> (String, bool) {
    let body = match bytes.strip_suffix(b"\n") {
        Some(line) => line.strip_suffix(b"\r").unwrap_or(line),
        None => bytes,
    };
    let line = String::from_utf8_lossy(body);
    if line.len() <= max_columns {
        return (line.into_owned(), false);
    }
    let mut boundary = max_columns;
    while !line.is_char_boundary(boundary) {
        boundary -= 1;
    }
    let cut = line.len() - boundary;
    let marker = super::CUT_MARKER;
    (format!("{}{marker}{cut} bytes⟩", &line[..boundary]), true)
}

pub(super) fn clamp_u32(value: u64) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}
