//! The `read` tool. Port of `tools/read.ts`.

use std::future::Future;
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_chord::json::{to_json, JsonNumber};
use eukhe_pi_ai::typebox::{Options, TSchema, Type};
use eukhe_types::pi_ai::{TextContent, UserContentBlock};
use serde::ser::SerializeMap;
use serde::{Deserialize, Serialize, Serializer};

use super::env::require_env;
use super::image::{detect_supported_image_mime_type_of, ByteSource};
use super::path_utils::resolve_read_tool_path;
use crate::env::{
    range_decoder, starts_with_bom, BinaryReader, FileError, FileInfo, LineRange, LineScan,
    OpenBinaryReaderOptions,
};
use crate::harness::define::define_tool;
use crate::harness::output::character_end;
use crate::harness::types::{
    ToolDiagnostic, ToolDiagnosticSeverity, ToolExecutionResult, ToolRegistration,
};
use crate::session::{SessionError, SessionResult};
use crate::truncate::{
    format_size, truncate_head_of, utf8_byte_length, TruncationOptions, TruncationResult,
    TruncationTotals, DEFAULT_MAX_BYTES, DEFAULT_MAX_LINES,
};

fn read_schema() -> TSchema {
    Type::object([
        (
            "path",
            Type::string_with(Options::new().set(
                "description",
                "Path to the file to read (relative or absolute)",
            )),
        ),
        (
            "offset",
            Type::optional(Type::number_with(Options::new().set(
                "description",
                "Line number to start reading from (1-indexed)",
            ))),
        ),
        (
            "limit",
            Type::optional(Type::number_with(
                Options::new().set("description", "Maximum number of lines to read"),
            )),
        ),
    ])
}

/// Arguments of `read` (TS `ReadToolInput`).
#[derive(Debug, Clone, PartialEq, Deserialize)]
pub struct ReadToolInput {
    pub path: String,
    #[serde(default)]
    pub offset: Option<f64>,
    #[serde(default)]
    pub limit: Option<f64>,
}

/// How the shown text was cut (TS `Omit<TruncationResult, "content">`); the
/// text itself is the result content.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReadTruncation(TruncationResult);

impl Serialize for ReadTruncation {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let result = &self.0;
        let mut map = serializer.serialize_map(Some(10))?;
        map.serialize_entry("truncated", &result.truncated)?;
        map.serialize_entry(
            "truncatedBy",
            &result
                .truncated_by
                .map(crate::truncate::TruncatedBy::as_str),
        )?;
        map.serialize_entry("totalLines", &result.total_lines)?;
        map.serialize_entry("totalBytes", &result.total_bytes)?;
        map.serialize_entry("outputLines", &result.output_lines)?;
        map.serialize_entry("outputBytes", &result.output_bytes)?;
        map.serialize_entry("lastLinePartial", &result.last_line_partial)?;
        map.serialize_entry("firstLineExceedsLimit", &result.first_line_exceeds_limit)?;
        map.serialize_entry("maxLines", &result.max_lines)?;
        map.serialize_entry("maxBytes", &result.max_bytes)?;
        map.end()
    }
}

/// Details of a truncated read (TS `ReadToolDetails`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ReadToolDetails {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub truncation: Option<ReadTruncation>,
}

const READ_CHUNK: u64 = 64 * 1024;

/// `Array.prototype.slice`'s conversion of an index: NaN is 0, other values
/// truncate toward zero.
fn slice_index(value: f64) -> f64 {
    if value.is_nan() {
        0.0
    } else {
        value.trunc()
    }
}

/// `Number.isSafeInteger`.
fn is_safe_integer(value: f64) -> bool {
    const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;
    value.is_finite() && value.fract() == 0.0 && value.abs() <= MAX_SAFE_INTEGER
}

/// JS `String(number)`.
fn js_number(value: f64) -> String {
    match JsonNumber::new(value) {
        Some(number) => number.to_string(),
        None if value.is_nan() => "NaN".to_owned(),
        None if value > 0.0 => "Infinity".to_owned(),
        None => "-Infinity".to_owned(),
    }
}

/// A count known to be a non-negative integer, as `u64`.
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "callers pass non-negative integral line counts below 2^53"
)]
fn count(value: f64) -> u64 {
    value as u64
}

#[expect(
    clippy::cast_precision_loss,
    reason = "file sizes and line counts stay below 2^53"
)]
fn number(value: u64) -> f64 {
    value as f64
}

/// The decoded start of bytes `[start, end)` of the file, decoded as part of
/// the whole file: all of it, or enough for `truncate_head_of` (more than
/// `DEFAULT_MAX_BYTES + 1` bytes, or `DEFAULT_MAX_LINES` newlines).
async fn read_head(
    reader: &dyn BinaryReader,
    start: u64,
    end: u64,
    skip_bom: bool,
    cx: &Context,
) -> Result<String, FileError> {
    let mut decoder = range_decoder();
    let mut text = String::new();
    let mut newlines = 0;
    let mut position = if skip_bom && start == 0 { 3 } else { start };
    while position < end {
        let bytes = reader
            .read(number(position), number(READ_CHUNK.min(end - position)), cx)
            .await?;
        if bytes.is_empty() {
            break;
        }
        position += bytes.len() as u64;
        let chunk_text = decoder.decode_chunk(&bytes);
        newlines += chunk_text.matches('\n').count() as u64;
        text.push_str(&chunk_text);
        if newlines >= DEFAULT_MAX_LINES || utf8_byte_length(&text) > DEFAULT_MAX_BYTES + 1 {
            return Ok(text);
        }
    }
    text.push_str(&decoder.finish());
    Ok(text)
}

/// Reads text files. Remarks about truncation and continuation are
/// diagnostics; the content is only file text.
#[must_use]
pub fn create_read_tool() -> Arc<ToolRegistration> {
    define_tool(ToolRegistration::new(
        "read",
        format!(
            "Read the contents of a text file. Output is truncated to {DEFAULT_MAX_LINES} lines or {}KB (whichever is hit first). Use offset/limit for large files. When you need the full file, continue with offset until complete.",
            DEFAULT_MAX_BYTES / 1024
        ),
        read_schema(),
        |args, api, cx| async move {
            let ReadToolInput {
                path,
                offset,
                limit,
            } = serde_json::from_value(args).map_err(SessionError::other)?;
            let env = require_env(api.as_ref())?;
            let absolute_path = resolve_read_tool_path(env.as_ref(), &path, &cx).await?;
            let reader = env
                .open_binary_reader(&absolute_path, OpenBinaryReaderOptions::default(), &cx)
                .await?;
            let result = read_consistent(reader.as_ref(), &path, offset, limit, &cx).await;
            reader.close(&cx).await;
            result
        },
    ))
}

/// A concurrent writer can change the file between the scan and the reads.
/// Appending (a growing log) leaves the scanned bytes as they were; a file
/// that shrank or was rewritten in place is read again once.
async fn read_consistent(
    reader: &dyn BinaryReader,
    path: &str,
    offset: Option<f64>,
    limit: Option<f64>,
    cx: &Context,
) -> SessionResult<ToolExecutionResult> {
    let mut retried = false;
    loop {
        let before = reader.info(cx).await?;
        let result = read_text(reader, &before, path, offset, limit, cx).await?;
        let after = reader.info(cx).await?;
        #[expect(clippy::float_cmp, reason = "TS compares mtimeMs with ===")]
        let unchanged = after.size == before.size && after.mtime_ms == before.mtime_ms;
        if after.size > before.size || unchanged {
            return Ok(result);
        }
        if retried {
            return Err(SessionError::error(format!(
                "{path} changed while it was read"
            )));
        }
        retried = true;
    }
}

/// Positional reads of the opened file for image detection.
struct ReaderSource<'a> {
    reader: &'a dyn BinaryReader,
    size: u64,
    cx: &'a Context,
}

impl ByteSource for ReaderSource<'_> {
    fn size(&self) -> u64 {
        self.size
    }

    fn read(
        &self,
        offset: u64,
        length: u64,
    ) -> impl Future<Output = Result<Vec<u8>, FileError>> + Send {
        self.reader.read(number(offset), number(length), self.cx)
    }
}

fn diagnostic(
    severity: ToolDiagnosticSeverity,
    code: Option<&str>,
    message: String,
) -> ToolDiagnostic {
    ToolDiagnostic {
        severity,
        code: code.map(str::to_owned),
        message,
    }
}

/// The read result for the opened file. It equals decoding the whole file
/// with `TextDecoder`, splitting it on `\n`, and bounding the selected lines
/// with `truncateHead`, while reading only one scan's worth of the file plus
/// the head.
#[expect(
    clippy::too_many_lines,
    reason = "one TS function; its steps share the selection state"
)]
async fn read_text(
    reader: &dyn BinaryReader,
    info: &FileInfo,
    path: &str,
    offset: Option<f64>,
    limit: Option<f64>,
    cx: &Context,
) -> SessionResult<ToolExecutionResult> {
    let source = ReaderSource {
        reader,
        size: info.size,
        cx,
    };
    if let Some(mime_type) = detect_supported_image_mime_type_of(&source).await? {
        // Image content is not supported yet.
        return Ok(ToolExecutionResult {
            content: Some(Vec::new()),
            is_error: Some(true),
            diagnostics: Some(vec![diagnostic(
                ToolDiagnosticSeverity::Error,
                Some("unsupported_image"),
                format!("{path} is an image ({mime_type}); reading images is not supported"),
            )]),
            ..ToolExecutionResult::default()
        });
    }

    // `offset ? ... : 0`: zero and NaN are falsy.
    let start_line = match offset {
        Some(offset) if offset != 0.0 && !offset.is_nan() => (offset - 1.0).max(0.0),
        Some(_) | None => 0.0,
    };
    let start_line_display = start_line + 1.0;
    // Lines are selected like `allLines.slice(startLine, endLine)`, which truncates fractional indices.
    let slice_start = slice_index(start_line);
    // One pass finds the line count and the selection; a selection past the last line ends with it, as `slice` does,
    // and an empty one (a zero or negative limit) is scanned as one line and then ignored.
    // A start beyond any file is scanned from 0 only to count lines; the offset check below then fails as before.
    let scan_start = if is_safe_integer(slice_start) {
        slice_start
    } else {
        0.0
    };
    let requested_end = limit.map(|limit| (scan_start + 1.0).max(slice_index(start_line + limit)));
    let scan_end = requested_end.filter(|end| is_safe_integer(*end));
    let scan_of = |end_line: Option<f64>| async move {
        reader
            .scan_lines(
                LineRange {
                    start_line: scan_start,
                    end_line,
                },
                cx,
            )
            .await
    };
    let mut scan: LineScan = scan_of(scan_end).await?;
    let total_file_lines = number(scan.newlines) + 1.0;
    if start_line >= total_file_lines {
        let offset = offset.map_or_else(|| "undefined".to_owned(), js_number);
        return Err(SessionError::error(format!(
            "Offset {offset} is beyond end of file ({} lines total)",
            js_number(total_file_lines)
        )));
    }

    let mut user_limited_lines = None;
    let mut selected_line_count = total_file_lines - slice_start;
    if let Some(limit) = limit {
        let end_line = (start_line + limit).min(total_file_lines);
        user_limited_lines = Some(end_line - start_line);
        // `slice` counts a negative end from the end of the lines, which only the line count tells; scan again for it.
        let relative_end = slice_index(end_line);
        let slice_end = if relative_end < 0.0 {
            (total_file_lines + relative_end).max(0.0)
        } else {
            relative_end
        };
        selected_line_count = (slice_end - slice_start).max(0.0);
        if selected_line_count > 0.0 && relative_end < 0.0 {
            scan = scan_of(Some(slice_end)).await?;
        }
    }
    let empty = selected_line_count == 0.0;
    // Counted like `truncateHead`: a trailing newline adds no line, and empty text has none.
    let ends_with_newline =
        !empty && scan.last_line_start == scan.end && scan.last_line_start > scan.start;
    let totals = TruncationTotals {
        lines: if empty || scan.selected_bytes == 0 {
            0
        } else {
            count(selected_line_count) - u64::from(ends_with_newline)
        },
        bytes: if empty { 0 } else { scan.selected_bytes },
    };
    let first_bytes = reader.read(0.0, 3.0, cx).await?;
    let head = if empty {
        String::new()
    } else {
        read_head(
            reader,
            scan.start,
            scan.end,
            starts_with_bom(&first_bytes),
            cx,
        )
        .await?
    };

    let mut truncation = truncate_head_of(&head, totals, TruncationOptions::default());
    let head_text = std::mem::take(&mut truncation.content);
    let mut diagnostics = Vec::new();
    let mut output_text = head_text;
    let mut details = None;
    if truncation.first_line_exceeds_limit {
        // Show the start of the line, cut at the byte limit on a character boundary. Like `allLines[startLine]`, a
        // fractional start line names no line.
        let integral = start_line.fract() == 0.0;
        let line = if integral {
            head.split('\n').next().unwrap_or_default()
        } else {
            ""
        };
        let line_size = if integral { scan.first_line_bytes } else { 0 };
        let max_bytes = usize::try_from(DEFAULT_MAX_BYTES).unwrap_or(usize::MAX);
        let end = character_end(line.as_bytes(), max_bytes);
        // `new TextDecoder().decode()` drops a leading byte order mark.
        let shown = &line[..end];
        shown
            .strip_prefix('\u{FEFF}')
            .unwrap_or(shown)
            .clone_into(&mut output_text);
        let display = js_number(start_line_display);
        diagnostics.push(diagnostic(
            ToolDiagnosticSeverity::Warn,
            Some("truncated"),
            format!(
                "Line {display} is {}, exceeds the {} limit; showing its first {}. Use bash: sed -n '{display}p' {path} | tail -c +{}",
                format_size(line_size),
                format_size(DEFAULT_MAX_BYTES),
                format_size(end as u64),
                end + 1
            ),
        ));
        truncation.output_bytes = end as u64;
        truncation.output_lines = 1;
        details = Some(ReadToolDetails {
            truncation: Some(ReadTruncation(truncation)),
        });
    } else if truncation.truncated {
        let end_line_display = start_line_display + number(truncation.output_lines) - 1.0;
        let next_offset = end_line_display + 1.0;
        let limit_text = match truncation.truncated_by {
            Some(crate::truncate::TruncatedBy::Lines) => String::new(),
            Some(crate::truncate::TruncatedBy::Bytes) | None => {
                format!(" ({} limit)", format_size(DEFAULT_MAX_BYTES))
            }
        };
        diagnostics.push(diagnostic(
            ToolDiagnosticSeverity::Info,
            Some("truncated"),
            format!(
                "Showing lines {}-{} of {}{limit_text}. Use offset={} to continue.",
                js_number(start_line_display),
                js_number(end_line_display),
                js_number(total_file_lines),
                js_number(next_offset)
            ),
        ));
        details = Some(ReadToolDetails {
            truncation: Some(ReadTruncation(truncation)),
        });
    } else if let Some(user_limited_lines) = user_limited_lines {
        if start_line + user_limited_lines < total_file_lines {
            let remaining = total_file_lines - (start_line + user_limited_lines);
            let next_offset = start_line + user_limited_lines + 1.0;
            diagnostics.push(diagnostic(
                ToolDiagnosticSeverity::Info,
                None,
                format!(
                    "{} more lines in file. Use offset={} to continue.",
                    js_number(remaining),
                    js_number(next_offset)
                ),
            ));
        }
    }

    Ok(ToolExecutionResult {
        content: Some(if output_text.is_empty() {
            Vec::new()
        } else {
            vec![UserContentBlock::Text(TextContent::new(output_text))]
        }),
        details: details.map(|details| to_json(&details)).transpose()?,
        diagnostics: Some(diagnostics),
        ..ToolExecutionResult::default()
    })
}
