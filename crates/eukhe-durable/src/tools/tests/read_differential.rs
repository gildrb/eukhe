//! Port of `test/tools-read-differential.test.ts`: the bounded `read` tool
//! against the whole-file reference.
//!
//! The TS trials also pass `NaN` offsets and limits; tool arguments are JSON
//! here, which cannot carry `NaN`, so those trials are skipped (the other
//! values, including `1e20` and fractional ones, run as in TS).

use std::sync::Arc;

use eukhe_chord::json::to_json;
use eukhe_types::pi_ai::{ImageContent, TextContent, UserContentBlock};
use serde_json::{json, Map, Value};

use super::support::{native, run, temp_dir};
use crate::env::{range_decoder, ExecutionEnv};
use crate::harness::output::character_end;
use crate::harness::types::{ToolDiagnostic, ToolDiagnosticSeverity, ToolExecutionResult};
use crate::tools::image::detect_supported_image_mime_type;
use crate::tools::image_processor::to_base64;
use crate::tools::{create_read_tool, ReadToolOptions};
use crate::truncate::{
    format_size, truncate_head, TruncationOptions, TruncationResult, DEFAULT_MAX_BYTES,
};

/// `DEFAULT_MAX_BYTES` as an index.
const MAX_BYTES: usize = 50 * 1024;

/// JS `String(number)`.
fn js(value: f64) -> String {
    eukhe_chord::json::JsonNumber::new(value)
        .map_or_else(|| value.to_string(), |number| number.to_string())
}

/// `Array.prototype.slice(start, end)` index resolution.
fn slice_bounds(len: usize, start: f64, end: Option<f64>) -> (usize, usize) {
    #[expect(clippy::cast_precision_loss, reason = "test line counts are small")]
    let length = len as f64;
    let resolve = |value: f64| {
        let integer = if value.is_nan() { 0.0 } else { value.trunc() };
        if integer < 0.0 {
            (length + integer).max(0.0)
        } else {
            integer.min(length)
        }
    };
    let from = resolve(start);
    let to = end.map_or(length, resolve);
    #[expect(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "clamped to 0..=len"
    )]
    let bounds = (from as usize, to.max(from) as usize);
    bounds
}

fn truncation_json(truncation: &TruncationResult) -> Value {
    json!({
        "truncated": truncation.truncated,
        "truncatedBy": truncation.truncated_by.map(crate::truncate::TruncatedBy::as_str),
        "totalLines": truncation.total_lines,
        "totalBytes": truncation.total_bytes,
        "outputLines": truncation.output_lines,
        "outputBytes": truncation.output_bytes,
        "lastLinePartial": truncation.last_line_partial,
        "firstLineExceedsLimit": truncation.first_line_exceeds_limit,
        "maxLines": truncation.max_lines,
        "maxBytes": truncation.max_bytes,
    })
}

/// The `read` tool before bounded reads, kept as the reference: it decodes
/// the whole file, splits it into lines, and truncates the selection.
#[expect(clippy::too_many_lines, reason = "one TS function")]
fn reference_read(
    bytes: &[u8],
    path: &str,
    offset: Option<f64>,
    limit: Option<f64>,
) -> Result<ToolExecutionResult, String> {
    if let Some(mime_type) = detect_supported_image_mime_type(bytes) {
        return Ok(ToolExecutionResult {
            output: Some(vec![UserContentBlock::Image(ImageContent {
                data: to_base64(bytes),
                mime_type: mime_type.to_owned(),
            })]),
            diagnostics: Some(vec![ToolDiagnostic {
                severity: ToolDiagnosticSeverity::Info,
                code: Some("image".to_owned()),
                message: format!("Read image file [{mime_type}]."),
            }]),
            ..ToolExecutionResult::default()
        });
    }
    let decoded = range_decoder().decode_all(bytes);
    let text_content = decoded.strip_prefix('\u{FEFF}').unwrap_or(&decoded);
    let all_lines: Vec<&str> = text_content.split('\n').collect();
    #[expect(clippy::cast_precision_loss, reason = "test line counts are small")]
    let total_file_lines = all_lines.len() as f64;
    let start_line = match offset {
        Some(offset) if offset != 0.0 && !offset.is_nan() => (offset - 1.0).max(0.0),
        Some(_) | None => 0.0,
    };
    let start_line_display = start_line + 1.0;
    if start_line >= total_file_lines {
        let offset = offset.map_or_else(|| "undefined".to_owned(), js);
        return Err(format!(
            "Offset {offset} is beyond end of file ({} lines total)",
            all_lines.len()
        ));
    }
    let mut user_limited_lines = None;
    let selected_content = if let Some(limit) = limit {
        let end_line = (start_line + limit).min(total_file_lines);
        let (from, to) = slice_bounds(all_lines.len(), start_line, Some(end_line));
        user_limited_lines = Some(end_line - start_line);
        all_lines[from..to].join("\n")
    } else {
        let (from, to) = slice_bounds(all_lines.len(), start_line, None);
        all_lines[from..to].join("\n")
    };
    let mut truncation = truncate_head(&selected_content, TruncationOptions::default());
    let head_text = std::mem::take(&mut truncation.content);
    let mut diagnostics = Vec::new();
    let mut output_text = head_text;
    let mut details = None;
    if truncation.first_line_exceeds_limit {
        // `allLines[startLine]`: a fractional index names no line, and `encode(undefined)` encodes "".
        let line = if start_line.fract() == 0.0 {
            #[expect(
                clippy::cast_possible_truncation,
                clippy::cast_sign_loss,
                reason = "a valid line index"
            )]
            let index = start_line as usize;
            all_lines[index].to_owned()
        } else {
            String::new()
        };
        let end = character_end(line.as_bytes(), MAX_BYTES);
        let shown = &line[..end];
        output_text = shown.strip_prefix('\u{FEFF}').unwrap_or(shown).to_owned();
        let display = js(start_line_display);
        diagnostics.push(ToolDiagnostic {
            severity: ToolDiagnosticSeverity::Warn,
            code: Some("truncated".to_owned()),
            message: format!(
                "Line {display} is {}, exceeds the {} limit; showing its first {}. Use bash: sed -n '{display}p' {path} | tail -c +{}",
                format_size(line.len() as u64),
                format_size(DEFAULT_MAX_BYTES),
                format_size(end as u64),
                end + 1
            ),
        });
        truncation.output_bytes = end as u64;
        truncation.output_lines = 1;
        details = Some(json!({ "truncation": truncation_json(&truncation) }));
    } else if truncation.truncated {
        #[expect(clippy::cast_precision_loss, reason = "test line counts are small")]
        let end_line_display = start_line_display + truncation.output_lines as f64 - 1.0;
        let next_offset = end_line_display + 1.0;
        let limit_text = if truncation.truncated_by == Some(crate::truncate::TruncatedBy::Lines) {
            String::new()
        } else {
            format!(" ({} limit)", format_size(DEFAULT_MAX_BYTES))
        };
        diagnostics.push(ToolDiagnostic {
            severity: ToolDiagnosticSeverity::Info,
            code: Some("truncated".to_owned()),
            message: format!(
                "Showing lines {}-{} of {}{limit_text}. Use offset={} to continue.",
                js(start_line_display),
                js(end_line_display),
                all_lines.len(),
                js(next_offset)
            ),
        });
        details = Some(json!({ "truncation": truncation_json(&truncation) }));
    } else if let Some(user_limited_lines) = user_limited_lines {
        if start_line + user_limited_lines < total_file_lines {
            let remaining = total_file_lines - (start_line + user_limited_lines);
            let next_offset = start_line + user_limited_lines + 1.0;
            diagnostics.push(ToolDiagnostic {
                severity: ToolDiagnosticSeverity::Info,
                code: None,
                message: format!(
                    "{} more lines in file. Use offset={} to continue.",
                    js(remaining),
                    js(next_offset)
                ),
            });
        }
    }
    Ok(ToolExecutionResult {
        output: Some(if output_text.is_empty() {
            Vec::new()
        } else {
            vec![UserContentBlock::Text(TextContent::new(output_text))]
        }),
        details: details.map(|details| to_json(&details).unwrap()),
        diagnostics: Some(diagnostics),
        ..ToolExecutionResult::default()
    })
}

/// mulberry32, as the TS `random(seed)`.
fn random(seed: u32) -> impl FnMut() -> f64 {
    let mut state = seed;
    move || {
        state = state.wrapping_add(0x6d2b_79f5);
        let mut t = state;
        t = (t ^ (t >> 15)).wrapping_mul(t | 1);
        t ^= t.wrapping_add((t ^ (t >> 7)).wrapping_mul(t | 0x3d));
        f64::from(t ^ (t >> 14)) / 4_294_967_296.0
    }
}

const PIECES: [&[u8]; 11] = [
    &[0x0a],
    &[0x0a],
    &[0x61],
    &[0x62, 0x63, 0x64, 0x65],
    &[0xef, 0xbb, 0xbf],
    &[0xc3, 0xa9],
    &[0xe2, 0x82, 0xac],
    &[0xf0, 0x9f, 0x98, 0x80],
    &[0xe2, 0x82],
    &[0xff],
    &[0x0d, 0x0a],
];

#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "Math.floor of [0, n)"
)]
fn pick(next: &mut impl FnMut() -> f64, count: usize) -> usize {
    #[expect(clippy::cast_precision_loss, reason = "small counts")]
    let scaled = (next() * count as f64).floor();
    scaled as usize
}

/// Mostly small files, some over the line limit, some over the byte limit,
/// some with one huge line.
fn random_file(next: &mut impl FnMut() -> f64) -> Vec<u8> {
    let kind = next();
    if kind < 0.1 {
        let mut bytes = vec![0xef, 0xbb, 0xbf];
        bytes.extend("x\n".repeat(2100).into_bytes());
        return bytes;
    }
    if kind < 0.2 {
        let mut line = vec![0x61; MAX_BYTES + 200 + pick(next, 400)];
        let index = MAX_BYTES - 1 + pick(next, 3);
        line[index] = 0xc3;
        line.extend([0x0a, 0x62]);
        return line;
    }
    if kind < 0.3 {
        return format!("{}\n", "0123456789".repeat(30))
            .repeat(200)
            .into_bytes();
    }
    let mut bytes = Vec::new();
    let pieces = pick(next, 80);
    for _ in 0..pieces {
        bytes.extend_from_slice(PIECES[pick(next, PIECES.len())]);
    }
    bytes
}

const OFFSETS: [Option<f64>; 12] = [
    None,
    Some(0.0),
    Some(1.0),
    Some(2.0),
    Some(3.0),
    Some(2.5),
    Some(-4.0),
    Some(50.0),
    Some(2001.0),
    Some(3000.0),
    Some(1e20),
    Some(f64::NAN),
];
const LIMITS: [Option<f64>; 12] = [
    None,
    Some(0.0),
    Some(1.0),
    Some(2.0),
    Some(-3.0),
    Some(-1e20),
    Some(1.5),
    Some(7.0),
    Some(2000.0),
    Some(2500.0),
    Some(1e20),
    Some(f64::NAN),
];

fn args(path: &str, offset: Option<f64>, limit: Option<f64>) -> Value {
    let mut args = Map::new();
    args.insert("path".to_owned(), json!(path));
    if let Some(offset) = offset {
        args.insert("offset".to_owned(), json!(offset));
    }
    if let Some(limit) = limit {
        args.insert("limit".to_owned(), json!(limit));
    }
    Value::Object(args)
}

#[tokio::test]
async fn returns_exactly_what_reading_the_whole_file_returned() {
    let dir = temp_dir();
    let env: Arc<dyn ExecutionEnv> = Arc::new(native(&dir));
    let tool = create_read_tool(ReadToolOptions::default());
    for seed in 1..=400 {
        let mut next = random(seed);
        let file = random_file(&mut next);
        std::fs::write(dir.path().join("f.txt"), &file).unwrap();
        for _trial in 0..4 {
            let offset = OFFSETS[pick(&mut next, OFFSETS.len())];
            let limit = LIMITS[pick(&mut next, LIMITS.len())];
            if offset.is_some_and(f64::is_nan) || limit.is_some_and(f64::is_nan) {
                continue;
            }
            let (actual, _) = run(&tool, args("f.txt", offset, limit), Arc::clone(&env)).await;
            let actual = actual.map_err(|error| error.to_string());
            let expected = reference_read(&file, "f.txt", offset, limit);
            assert_eq!(
                actual, expected,
                "seed {seed} offset {offset:?} limit {limit:?}"
            );
        }
    }
}

#[tokio::test]
async fn detects_animated_pngs_whose_ac_tl_chunk_lies_far_beyond_the_header() {
    let dir = temp_dir();
    let chunk = |kind: &str, length: u32| -> Vec<u8> {
        let mut bytes = length.to_be_bytes().to_vec();
        bytes.extend(kind.as_bytes());
        bytes.extend(std::iter::repeat_n(0, length as usize + 4));
        bytes
    };
    let mut png = vec![0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a];
    png.extend(chunk("IHDR", 13));
    png.extend(chunk("iCCP", 200_000));
    png.extend(chunk("acTL", 8));
    png.extend(chunk("IDAT", 10));
    std::fs::write(dir.path().join("a.png"), &png).unwrap();
    let (actual, _) = run(
        &create_read_tool(ReadToolOptions::default()),
        json!({ "path": "a.png" }),
        Arc::new(native(&dir)),
    )
    .await;
    assert_eq!(
        actual.map_err(|error| error.to_string()),
        reference_read(&png, "a.png", None, None)
    );
}
