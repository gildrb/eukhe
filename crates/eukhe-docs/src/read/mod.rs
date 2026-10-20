//! The read projection: a file becomes `[path#TAG]` plus `N:TEXT` rows, and
//! selectors bound what is shown (port of omp `read/format.rs` for text
//! files, without syntax-aware block context). A read records the file's
//! snapshot but not its seen lines: the caller records the [`Row`]s that
//! reach the model. A read without a selector shows the whole file, as in
//! omp; output is bounded once, by the caller.

mod listing;
pub(crate) mod selector;

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use eukhe_types::path_policy::{resolve, RealPath};

use crate::gate::{Access, AccessGate};
use crate::notice::{Notice, NoticeKind, Omitted, Unit};
use crate::store::{EditStore, MAX_SNAPSHOT_FILE_BYTES};
use crate::text::{encoding_name, format_bytes, normalize_to_lf, strip_bom};
use crate::url::{Located, Url, UrlError};

pub use listing::DirEntry;
pub use selector::SelectorError;
use selector::{LineRange, Selector};

/// Source lines added before a range whose start was given.
const RANGE_LEADING_CONTEXT_LINES: usize = 1;
/// Source lines added after a range whose end was given.
const RANGE_TRAILING_CONTEXT_LINES: usize = 3;
/// Marker between non-contiguous spans.
const ELLIPSIS: &str = "…";
/// Bytes sniffed for a NUL.
const BINARY_SNIFF_BYTES: usize = 8192;
/// Lines in the range a notice gives for a file too large to edit.
const LARGE_FILE_RANGE_LINES: usize = 2000;

/// Why a read failed; the message is model-facing.
#[derive(Debug, thiserror::Error)]
pub enum ReadError {
    #[error("Path '{0}' not found")]
    NotFound(String),
    #[error(transparent)]
    Selector(#[from] SelectorError),
    #[error(
        "[Cannot read binary file '{display}' ({size}): it has a NUL byte. Use ':raw' to read bytes verbatim.]"
    )]
    Binary { display: String, size: String },
    #[error(
        "[{display} is {encoding}: `edit` works on UTF-8 only. ':raw' shows it (characters that are not UTF-8 become U+FFFD); `write` replaces it as UTF-8.]"
    )]
    NotUtf8 {
        display: String,
        encoding: &'static str,
    },
    #[error("{display}: {source}")]
    Io {
        display: String,
        #[source]
        source: std::io::Error,
    },
    #[error(transparent)]
    Url(#[from] crate::url::UrlError),
    #[error("Did not read {display}: {reason}")]
    Refused { display: String, reason: String },
}

/// One inclusive, one-based span of source lines.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LineSpan {
    pub start_line: usize,
    pub end_line: usize,
}

/// One shown row of a read or grep result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Row {
    /// The one-based source line the row shows.
    pub line: u32,
    /// The 0-based index of the row's line in the rendered text
    /// ([`ReadView::rendered`], `GrepOutput::render()`).
    pub at: usize,
}

/// A read result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReadView {
    /// The edit anchor: cwd-relative, `~/`-shortened, or absolute.
    pub path: String,
    pub absolute: PathBuf,
    pub content: ReadContent,
    /// The model-facing text: the projection, then one line per notice.
    pub rendered: String,
    pub diags: Vec<Notice>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReadContent {
    File(FileView),
    Directory(Vec<DirEntry>),
}

/// A read file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FileView {
    /// The file tag; `None` when the file is over the size limit or not
    /// UTF-8 (a lossy `:raw` read).
    pub tag: Option<String>,
    /// The whole text, LF-normalized, without BOM.
    pub text: String,
    /// Addressable lines in `text`.
    pub total_lines: usize,
    /// Source spans the projection shows (context lines included).
    pub shown: Vec<LineSpan>,
    /// The numbered rows shown, with their place in `rendered`; empty for a
    /// `:raw` read.
    pub rows: Vec<Row>,
}

/// Read `authored` (which may carry a `:selector`) relative to `cwd`.
///
/// # Errors
///
/// The path is missing or unreadable, the selector is invalid, or the file
/// is binary without `:raw`.
pub(crate) fn read(
    store: &EditStore,
    cwd: &Path,
    home: Option<&Path>,
    authored: &str,
    gate: &dyn AccessGate,
) -> Result<ReadView, ReadError> {
    let literal = crate::path::resolve(cwd, home, authored);
    let (absolute, selector) = if literal.exists() {
        (literal, None)
    } else {
        let split = selector::split_path_and_selector(authored);
        (crate::path::resolve(cwd, home, split.path), split.selector)
    };
    let real = resolve(&absolute);
    project_path(store, cwd, home, authored, absolute, &real, selector, gate)
}

/// Read the internal URL `url` (whose path may carry a `:selector`):
/// `locate` turns the names the path reaches under its scheme's root into
/// the file or directory to read and that root (`None`: there is none).
/// The real path (symlinks followed) must stay under the root's real path,
/// and the read opens that checked real path. Display paths stay relative
/// to `cwd`.
///
/// # Errors
///
/// The path goes above its root, as written or through a symlink, `locate`
/// finds nothing, the path or the root has no real path, or as [`read`].
pub(crate) fn read_under(
    store: &EditStore,
    cwd: &Path,
    home: Option<&Path>,
    url: Url<'_>,
    locate: impl Fn(&[&str]) -> Option<Located>,
    gate: &dyn AccessGate,
) -> Result<ReadView, ReadError> {
    let authored = format!("{}://{}", url.scheme.name(), url.path);
    let (located, path, selector) = match url.names().map(|names| locate(&names)) {
        Ok(Some(literal)) if literal.path.exists() => (literal, url.path, None),
        Ok(Some(_) | None) | Err(_) => {
            let split = selector::split_path_and_selector(url.path);
            let names = Url {
                path: split.path,
                ..url
            }
            .names()?;
            let located = locate(&names).ok_or_else(|| ReadError::NotFound(authored.clone()))?;
            (located, split.path, split.selector)
        }
    };
    let real_root = std::fs::canonicalize(&located.root).map_err(|source| ReadError::Io {
        display: display_path(&located.root, cwd, home),
        source,
    })?;
    let real = std::fs::canonicalize(&located.path)
        .map(|real| resolve(&real))
        .map_err(|source| match source.kind() {
            std::io::ErrorKind::NotFound => ReadError::NotFound(authored.clone()),
            _ => ReadError::Io {
                display: display_path(&located.path, cwd, home),
                source,
            },
        })?;
    if !real.path().starts_with(&real_root) {
        return Err(UrlError::Leaves {
            scheme: url.scheme.name(),
            path: path.to_owned(),
        }
        .into());
    }
    project_path(
        store,
        cwd,
        home,
        &authored,
        located.path,
        &real,
        selector,
        gate,
    )
}

/// Project the file or directory at `absolute`, opened at `real` (its
/// resolved path), after `gate` let the read (a list, for a directory) of
/// `real`; `authored` names it in a not-found message.
#[allow(
    clippy::too_many_arguments,
    reason = "each argument is one part of the read; a struct would only rename them"
)]
#[allow(
    clippy::too_many_lines,
    reason = "one read: directory or file, classify the bytes, project, tag"
)]
fn project_path(
    store: &EditStore,
    cwd: &Path,
    home: Option<&Path>,
    authored: &str,
    absolute: PathBuf,
    real: &RealPath,
    selector: Option<&str>,
    gate: &dyn AccessGate,
) -> Result<ReadView, ReadError> {
    let open = real.path();
    let selector = selector::parse_selector(selector)?;
    let display = display_path(&absolute, cwd, home);
    let metadata = std::fs::metadata(open).map_err(|source| match source.kind() {
        std::io::ErrorKind::NotFound => ReadError::NotFound(authored.to_owned()),
        _ => ReadError::Io {
            display: display.clone(),
            source,
        },
    })?;
    let access = if metadata.is_dir() {
        Access::List
    } else {
        Access::Read
    };
    gate.check(access, real, &display)
        .map_err(|reason| ReadError::Refused {
            display: display.clone(),
            reason,
        })?;
    if metadata.is_dir() {
        let (offset, limit) = match &selector {
            Selector::Whole | Selector::Raw => (None, None),
            Selector::Lines { ranges, .. } => match ranges.as_slice() {
                [range] => (
                    Some(to_usize(range.start_line)),
                    range
                        .end_line
                        .map(|end| to_usize(end - range.start_line).saturating_add(1)),
                ),
                [] | [_, _, ..] => return Err(SelectorError::directory_multi_range().into()),
            },
        };
        let entries = listing::list(open).map_err(|source| ReadError::Io {
            display: display.clone(),
            source,
        })?;
        let listing = listing::render(&entries, listing::now_ms(), offset, limit);
        return Ok(ReadView {
            path: display,
            absolute,
            content: ReadContent::Directory(entries),
            rendered: with_notices(listing.text, &listing.diags),
            diags: listing.diags,
        });
    }
    let bytes = std::fs::read(open).map_err(|source| ReadError::Io {
        display: display.clone(),
        source,
    })?;
    let sniffed_nul = bytes[..bytes.len().min(BINARY_SNIFF_BYTES)].contains(&0);
    let utf8 = std::str::from_utf8(&bytes).is_ok();
    let utf16 = matches!(bytes.as_slice(), [0xFF, 0xFE, ..] | [0xFE, 0xFF, ..]);
    if !selector.is_raw() {
        if !utf8 && (utf16 || !sniffed_nul) {
            return Err(ReadError::NotUtf8 {
                display,
                encoding: encoding_name(&bytes),
            });
        }
        if sniffed_nul {
            return Err(ReadError::Binary {
                display,
                size: format_bytes(metadata.len()),
            });
        }
    }
    let key = open.to_path_buf();
    store.saw_bytes(&key, &bytes);
    let size = u64::try_from(bytes.len()).unwrap_or(u64::MAX);
    let raw_text = match String::from_utf8(bytes) {
        Ok(text) => text,
        Err(error) => String::from_utf8_lossy(error.as_bytes()).into_owned(),
    };
    let text = normalize_to_lf(strip_bom(&raw_text).1).into_owned();
    let mut projection = project(&text, &selector, &display);
    let tag = (utf8 && size <= MAX_SNAPSHOT_FILE_BYTES).then(|| store.record(&key, &text, None));
    if size > MAX_SNAPSHOT_FILE_BYTES {
        projection.diags.push(Notice {
            continuation: Some(format!(":1-{LARGE_FILE_RANGE_LINES}")),
            ..Notice::warn(
                NoticeKind::NotEditable,
                format!(
                    "{display} is {}, over the {} limit: it has no tag, so `edit` cannot change it. Read it in ranges; change it with `write` (whole file) or `bash`.",
                    format_bytes(size),
                    format_bytes(MAX_SNAPSHOT_FILE_BYTES)
                ),
            )
        });
    }
    let (rendered, rows) = match (&tag, selector.is_raw()) {
        (Some(tag), false) => {
            let rows = projection
                .rows
                .iter()
                .map(|row| Row {
                    line: row.line,
                    at: row.at + 1,
                })
                .collect();
            (format!("[{display}#{tag}]\n{}", projection.text), rows)
        }
        (None, false) => (projection.text, projection.rows),
        (Some(_) | None, true) => (projection.text, Vec::new()),
    };
    let rendered = with_notices(rendered, &projection.diags);
    Ok(ReadView {
        path: display,
        absolute,
        content: ReadContent::File(FileView {
            tag,
            total_lines: projection.total_lines,
            shown: projection.shown,
            text,
            rows,
        }),
        rendered,
        diags: projection.diags,
    })
}

/// Append one `<diag>` line per notice.
fn with_notices(mut rendered: String, diags: &[Notice]) -> String {
    for diag in diags {
        if !rendered.is_empty() {
            rendered.push('\n');
        }
        let _infallible = write!(rendered, "{diag}");
    }
    rendered
}

/// The edit anchor of `path`: relative inside `cwd`, `~/...` inside
/// `home`, else absolute (omp `format_read_anchor`).
#[must_use]
pub fn display_path(path: &Path, cwd: &Path, home: Option<&Path>) -> String {
    if let Ok(relative) = path.strip_prefix(cwd) {
        return if relative.as_os_str().is_empty() {
            ".".to_owned()
        } else {
            relative.to_string_lossy().into_owned()
        };
    }
    if let Some(relative) = home.and_then(|home| path.strip_prefix(home).ok()) {
        return if relative.as_os_str().is_empty() {
            "~".to_owned()
        } else {
            format!("~/{}", relative.to_string_lossy())
        };
    }
    path.to_string_lossy().into_owned()
}

struct Projection {
    text: String,
    diags: Vec<Notice>,
    total_lines: usize,
    shown: Vec<LineSpan>,
    /// Numbered rows, with `at` counted in `text`.
    rows: Vec<Row>,
}

/// Lines a hashline anchor can address: a final newline adds no line.
fn addressable_lines(text: &str) -> Vec<&str> {
    let mut lines: Vec<&str> = text.split('\n').collect();
    if text.ends_with('\n') {
        lines.pop();
    }
    lines
}

fn to_usize(line: u64) -> usize {
    usize::try_from(line).unwrap_or(usize::MAX)
}

fn project(text: &str, selector: &Selector, label: &str) -> Projection {
    let raw = selector.is_raw();
    let lines = if raw {
        text.split('\n').collect()
    } else {
        addressable_lines(text)
    };
    let total = lines.len();
    match selector {
        Selector::Lines { ranges, raw } if ranges.len() > 1 => {
            project_ranges(&lines, ranges, *raw, label)
        }
        Selector::Lines { ranges, raw } => {
            project_window(&lines, ranges.first().copied(), *raw, label)
        }
        Selector::Raw => Projection {
            text: text.to_owned(),
            diags: Vec::new(),
            total_lines: total,
            shown: span_of(1, total).into_iter().collect(),
            rows: Vec::new(),
        },
        Selector::Whole => project_window(&lines, None, false, label),
    }
}

fn span_of(start_line: usize, end_line: usize) -> Option<LineSpan> {
    (end_line >= start_line).then_some(LineSpan {
        start_line,
        end_line,
    })
}

/// Write the `N:TEXT` rows of `span` to `out` and record each in `rows`.
fn numbered(lines: &[&str], span: LineSpan, out: &mut String, rows: &mut Vec<Row>) {
    let mut at = out.bytes().filter(|byte| *byte == b'\n').count();
    for (offset, line) in lines[span.start_line - 1..span.end_line].iter().enumerate() {
        if !out.is_empty() {
            out.push('\n');
            at += 1;
        }
        let number = span.start_line + offset;
        rows.push(Row {
            line: u32::try_from(number).unwrap_or(u32::MAX),
            at,
        });
        let _infallible = write!(out, "{number}:{line}");
    }
}

/// One window: the whole file, or one selected range with its context
/// lines.
fn project_window(lines: &[&str], range: Option<LineRange>, raw: bool, label: &str) -> Projection {
    let total = lines.len();
    let requested_start = range.map_or(1, |range| to_usize(range.start_line)) - 1;
    if requested_start >= total {
        let diag = Notice {
            continuation: Some(":1".to_owned()),
            ..Notice::warn(
                NoticeKind::RangeOutOfBounds,
                format!(
                    "Line {} is beyond end of {label} ({total} lines total).",
                    requested_start.saturating_add(1)
                ),
            )
        };
        return Projection {
            text: String::new(),
            diags: vec![diag],
            total_lines: total,
            shown: Vec::new(),
            rows: Vec::new(),
        };
    }
    let limit = range.and_then(|range| {
        range
            .end_line
            .map(|end| to_usize(end - range.start_line).saturating_add(1))
    });
    let requested_end = limit.map_or(total, |limit| {
        requested_start.saturating_add(limit).min(total)
    });
    let explicit_start = !raw && requested_start > 0;
    let explicit_end = !raw && range.is_some_and(|range| range.end_line.is_some());
    let start = if explicit_start {
        requested_start.saturating_sub(RANGE_LEADING_CONTEXT_LINES)
    } else {
        requested_start
    };
    let end = if explicit_end {
        requested_end
            .saturating_add(RANGE_TRAILING_CONTEXT_LINES)
            .min(total)
    } else {
        requested_end
    };
    let shown: Vec<LineSpan> = span_of(start + 1, end).into_iter().collect();
    let mut rows = Vec::new();
    let text = if raw {
        lines[start..end].join("\n")
    } else {
        let mut out = String::new();
        for span in &shown {
            numbered(lines, *span, &mut out, &mut rows);
        }
        out
    };
    let mut diags = Vec::new();
    if !raw && limit.is_some() && end < total {
        let remaining = total - end;
        diags.push(Notice {
            continuation: Some(format!(":{}", end + 1)),
            omitted: Some(Omitted {
                count: remaining as u64,
                unit: Unit::Lines,
            }),
            ..Notice::info(
                NoticeKind::Pagination,
                format!("{remaining} lines remain in {label}."),
            )
        });
    }
    Projection {
        text,
        diags,
        total_lines: total,
        shown,
        rows,
    }
}

fn project_ranges(lines: &[&str], ranges: &[LineRange], raw: bool, label: &str) -> Projection {
    let total = lines.len();
    let mut shown = Vec::with_capacity(ranges.len());
    let mut diags = Vec::new();
    for range in ranges {
        let start_line = to_usize(range.start_line);
        if start_line > total {
            let bound = range.end_line.map_or_else(
                || range.start_line.to_string(),
                |end| format!("{}-{end}", range.start_line),
            );
            diags.push(Notice::warn(
                NoticeKind::RangeOutOfBounds,
                format!("Requested range {bound} is beyond end of {label} ({total} lines total)."),
            ));
            continue;
        }
        let end_line = range.end_line.map_or(total, |end| to_usize(end).min(total));
        shown.push(LineSpan {
            start_line,
            end_line,
        });
    }
    let mut text = String::new();
    let mut rows = Vec::new();
    for (index, span) in shown.iter().enumerate() {
        if raw {
            if index > 0 {
                let _infallible = write!(text, "\n\n{ELLIPSIS}\n\n");
            }
            text.push_str(&lines[span.start_line - 1..span.end_line].join("\n"));
        } else {
            if index > 0 && span.start_line > shown[index - 1].end_line + 1 {
                text.push('\n');
                text.push_str(ELLIPSIS);
            }
            numbered(lines, *span, &mut text, &mut rows);
        }
    }
    Projection {
        text,
        diags,
        total_lines: total,
        shown,
        rows,
    }
}

#[cfg(test)]
mod tests;
