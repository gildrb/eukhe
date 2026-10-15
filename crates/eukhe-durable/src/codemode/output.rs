//! Port of pi-durable `codemode/output.ts`: the code mode tool result's
//! layout for a script's result: the header, the output items with their
//! markers, the error, the token budget, and the saved images.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::future::Future;

use base64::alphabet;
use base64::engine::general_purpose::{GeneralPurpose, GeneralPurposeConfig};
use base64::engine::DecodePaddingMode;
use base64::Engine as _;
use eukhe_chord::json::JsonValue;
use eukhe_types::pi_ai::{ImageContent, TextContent, UserContentBlock};

use super::types::{
    CodemodeCallStatus, CodemodeEnding, CodemodeError, CodemodeErrorKind, CodemodeNestedCall,
    CodemodeOutputItem, CodemodeResult, TextOrigin,
};

/// Lines of the result besides the script's text: the header, markers,
/// notes.
const LINE_MARGIN: i64 = 100;
/// Default token budget for script output.
pub const DEFAULT_MAX_OUTPUT_TOKENS: u64 = 10_000;
/// Characters per token when estimating.
const CHARS_PER_TOKEN: u64 = 4;

/// JS `atob`: the standard alphabet, padding optional, non-zero trailing
/// bits accepted (ASCII whitespace is stripped before decoding).
const ATOB: GeneralPurpose = GeneralPurpose::new(
    &alphabet::STANDARD,
    GeneralPurposeConfig::new()
        .with_decode_allow_trailing_bits(true)
        .with_decode_padding_mode(DecodePaddingMode::Indifferent),
);

/// Writes one file of the result under a fixed name (the run's output
/// directory); resolves to its path, or an error message.
pub(crate) trait OutputFiles: Send + Sync {
    /// Write `data` as `name`.
    fn write(&self, name: &str, data: &[u8])
        -> impl Future<Output = Result<String, String>> + Send;
}

/// The tool result's size limits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct OutputLimits {
    pub(crate) max_bytes: u64,
    pub(crate) max_lines: u64,
}

/// What [`format_result`] needs besides the result.
pub(crate) struct FormatOptions<'a> {
    /// Images `models.generateImages()` returned during the run.
    pub(crate) generated_images: u64,
    pub(crate) wall_ms: f64,
    pub(crate) max_output_tokens: u64,
    /// The run's tool calls, for the failure summary.
    pub(crate) calls: &'a [CodemodeNestedCall],
    pub(crate) limits: OutputLimits,
}

/// The tool result's content, and the path of the complete text when it was
/// cut.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct FormattedResult {
    pub(crate) content: Vec<UserContentBlock>,
    pub(crate) full_output_path: Option<String>,
}

/// An item of the laid-out result.
#[derive(Debug, Clone, PartialEq)]
enum Item {
    Text(String),
    Image { data: String, mime_type: String },
}

fn utf16_len(text: &str) -> usize {
    text.encode_utf16().count()
}

/// The first `units` UTF-16 code units of `text`. A character the bound
/// splits is left out: JS would keep its lone surrogate, which a Rust
/// string cannot hold.
fn utf16_prefix(text: &str, units: usize) -> &str {
    let mut count = 0;
    let mut end = 0;
    for (index, c) in text.char_indices() {
        count += c.len_utf16();
        if count > units {
            break;
        }
        end = index + c.len_utf8();
    }
    &text[..end]
}

/// The last `units` UTF-16 code units of `text` (JS `slice(-units)`), a
/// split character left out.
fn utf16_suffix(text: &str, units: usize) -> &str {
    let mut count = 0;
    let mut start = text.len();
    for (index, c) in text.char_indices().rev() {
        count += c.len_utf16();
        if count > units {
            break;
        }
        start = index;
    }
    &text[start..]
}

/// The range of JS `array.slice(start, end)` on `len` elements.
fn js_slice(len: usize, start: i64, end: Option<i64>) -> std::ops::Range<usize> {
    let len = i64::try_from(len).unwrap_or(i64::MAX);
    let clamp = |index: i64| {
        if index < 0 {
            (len + index).max(0)
        } else {
            index.min(len)
        }
    };
    let start = clamp(start);
    let end = end.map_or(len, clamp).max(start);
    usize::try_from(start).unwrap_or(0)..usize::try_from(end).unwrap_or(0)
}

/// JS `Math.ceil(units / CHARS_PER_TOKEN)`.
fn tokens(units: i64) -> i64 {
    let per_token = i64::try_from(CHARS_PER_TOKEN).unwrap_or(i64::MAX);
    // Ceiling division: `ceil(a / b) == -floor(-a / b)` for `b > 0`.
    -(-units).div_euclid(per_token)
}

/// JS `x.toFixed(1)`: an exact tie rounds to the larger neighbour, where
/// Rust's formatting rounds it to even.
fn to_fixed_1(x: f64) -> String {
    let scaled = x * 10.0;
    #[expect(
        clippy::float_cmp,
        reason = "detecting an exact binary tie, as JS `toFixed` does"
    )]
    let tie = scaled.fract().abs() == 0.5 && x.mul_add(10.0, -scaled) == 0.0;
    if tie {
        return format!("{:.1}", scaled.ceil() / 10.0);
    }
    format!("{x:.1}")
}

/// Like the script's `text()`: strings as is, other values as compact JSON.
fn value_text(value: &JsonValue) -> String {
    match value {
        JsonValue::String(text) => text.to_string(),
        JsonValue::Null
        | JsonValue::Bool(_)
        | JsonValue::Number(_)
        | JsonValue::Array(_)
        | JsonValue::Object(_) => value.to_string(),
    }
}

/// Lay out the script's output so the model can tell items apart: with more
/// than one text item, each starts with a `==> text N/M <==` line;
/// `console` lines follow all other output in one `<console_output>` block.
fn format_items(output: &[CodemodeOutputItem]) -> Vec<Item> {
    let total = output
        .iter()
        .filter(|item| {
            matches!(
                item,
                CodemodeOutputItem::Text {
                    origin: TextOrigin::Script,
                    ..
                }
            )
        })
        .count();
    let mut items = Vec::new();
    let mut console_lines: Vec<&str> = Vec::new();
    let mut index = 0;
    for item in output {
        match item {
            CodemodeOutputItem::Image { data, mime_type } => items.push(Item::Image {
                data: data.clone(),
                mime_type: mime_type.clone(),
            }),
            CodemodeOutputItem::Text {
                text,
                origin: TextOrigin::Console,
            } => console_lines.push(text),
            CodemodeOutputItem::Text {
                text,
                origin: TextOrigin::Script,
            } => {
                index += 1;
                items.push(Item::Text(if total > 1 {
                    format!("==> text {index}/{total} <==\n{text}")
                } else {
                    text.clone()
                }));
            }
        }
    }
    if !console_lines.is_empty() {
        items.push(Item::Text(format!(
            "<console_output>\n{}\n</console_output>",
            console_lines.join("\n")
        )));
    }
    items
}

/// Join adjacent text items into one, each part starting on its own line
/// (judged by the last non-empty part).
fn join_adjacent_text(items: Vec<Item>) -> Vec<Item> {
    let mut joined = Vec::new();
    let mut text: Option<String> = None;
    let mut last_part_ends_line = true;
    for item in items {
        match item {
            Item::Image { .. } => {
                if let Some(text) = text.take() {
                    joined.push(Item::Text(text));
                }
                last_part_ends_line = true;
                joined.push(item);
            }
            Item::Text(part) => {
                let buffer = text.get_or_insert_with(String::new);
                if !last_part_ends_line {
                    buffer.push('\n');
                    last_part_ends_line = true;
                }
                if !part.is_empty() {
                    last_part_ends_line = part.ends_with('\n');
                }
                buffer.push_str(&part);
            }
        }
    }
    if let Some(text) = text {
        joined.push(Item::Text(text));
    }
    joined
}

/// Apply the token budget: when the combined text exceeds it, the text
/// items become one item that keeps the start and end of the text, and
/// images follow it. The complete text is written to `output.txt`.
async fn truncate<W: OutputFiles>(
    items: Vec<Item>,
    max_tokens: u64,
    limits: OutputLimits,
    files: &W,
) -> (Vec<Item>, Option<String>) {
    let texts: Vec<&str> = items
        .iter()
        .filter_map(|item| match item {
            Item::Text(text) => Some(text.as_str()),
            Item::Image { .. } => None,
        })
        .collect();
    if texts.is_empty() {
        return (items, None);
    }
    let combined = texts.join("\n");
    let length = utf16_len(&combined);
    // Within the limits too: a UTF-16 unit is at most 3 UTF-8 bytes, and the
    // rest of the result is a few short lines.
    let budget = max_tokens
        .saturating_mul(CHARS_PER_TOKEN)
        .min(limits.max_bytes / 4);
    let max_lines = i64::try_from(limits.max_lines).unwrap_or(i64::MAX);
    let line_budget = (max_lines - LINE_MARGIN).div_euclid(2);
    let lines: Vec<&str> = combined.split('\n').collect();
    let line_count = i64::try_from(lines.len()).unwrap_or(i64::MAX);
    if (length as u64) <= budget && line_count <= 2 * line_budget {
        return (items, None);
    }
    let head_chars = budget / 2;
    let tail_chars = budget - head_chars;
    let head_lines: Vec<&str> =
        utf16_prefix(&combined, usize::try_from(head_chars).unwrap_or(usize::MAX))
            .split('\n')
            .collect();
    let head = head_lines[js_slice(head_lines.len(), 0, Some(line_budget))].join("\n");
    let tail = if tail_chars > 0 {
        let tail_lines: Vec<&str> =
            utf16_suffix(&combined, usize::try_from(tail_chars).unwrap_or(usize::MAX))
                .split('\n')
                .collect();
        tail_lines[js_slice(tail_lines.len(), -line_budget, None)].join("\n")
    } else {
        String::new()
    };
    #[expect(
        clippy::cast_possible_wrap,
        reason = "UTF-16 lengths of in-memory text are far below `i64::MAX`"
    )]
    let removed = length as i64 - utf16_len(&head) as i64 - utf16_len(&tail) as i64;
    #[expect(
        clippy::cast_possible_wrap,
        reason = "UTF-16 lengths of in-memory text are far below `i64::MAX`"
    )]
    let original_tokens = tokens(length as i64);
    let mut text = format!(
        "Warning: truncated output (original token count: {original_tokens})\nTotal output lines: {line_count}\n\n{head}…{} tokens truncated…{tail}",
        tokens(removed)
    );
    let spilled = files.write("output.txt", combined.as_bytes()).await;
    let full_output_path = match spilled {
        Ok(path) => {
            let _ = write!(text, "\n\n[Full output: {path} (read with offset/limit)]");
            Some(path)
        }
        Err(error) => {
            let _ = write!(text, "\n\n[Could not save the full output: {error}]");
            None
        }
    };
    let mut truncated = vec![Item::Text(text)];
    truncated.extend(
        items
            .into_iter()
            .filter(|item| matches!(item, Item::Image { .. })),
    );
    (truncated, full_output_path)
}

/// File extension of an image type `image()` accepts.
fn image_extension(mime_type: &str) -> &'static str {
    match mime_type {
        "image/png" => ".png",
        "image/jpeg" => ".jpg",
        "image/gif" => ".gif",
        "image/webp" => ".webp",
        _ => ".bin",
    }
}

/// Save one image as `image-<index><ext>`; the label names its path, or why
/// it was not saved. A failed write must not discard the result of a script
/// whose calls already ran: it becomes part of the label.
async fn label_image<W: OutputFiles>(
    data: &str,
    mime_type: &str,
    index: usize,
    files: &W,
) -> String {
    let cleaned: String = data
        .chars()
        .filter(|c| !matches!(c, '\t' | '\n' | '\u{c}' | '\r' | ' '))
        .collect();
    // JS `atob` throws on invalid base64 and fails the whole layout; here the
    // label says so instead.
    let bytes = match ATOB.decode(cleaned) {
        Ok(bytes) => bytes,
        Err(error) => {
            return format!("[Image ({mime_type}) could not be saved: invalid base64: {error}]")
        }
    };
    let kind = format!("{mime_type}, {} bytes", bytes.len());
    let name = format!("image-{index}{}", image_extension(mime_type));
    match files.write(&name, &bytes).await {
        Ok(path) => format!("[Image saved to {path} ({kind})]"),
        Err(error) => format!("[Image ({kind}) could not be saved: {error}]"),
    }
}

/// Save each image to a file and put a text item with its path before it;
/// an image shown twice is saved once.
async fn save_images<W: OutputFiles>(items: Vec<Item>, files: &W) -> Vec<Item> {
    let mut labels: HashMap<String, String> = HashMap::new();
    let mut result = Vec::with_capacity(items.len());
    for item in items {
        match item {
            Item::Text(_) => result.push(item),
            Item::Image {
                ref data,
                ref mime_type,
            } => {
                let label = if let Some(label) = labels.get(data) {
                    label.clone()
                } else {
                    let label = label_image(data, mime_type, labels.len() + 1, files).await;
                    labels.insert(data.clone(), label.clone());
                    label
                };
                result.push(Item::Text(label));
                result.push(item);
            }
        }
    }
    result
}

fn status_text(status: CodemodeCallStatus) -> &'static str {
    match status {
        CodemodeCallStatus::Running => "running",
        CodemodeCallStatus::Ok => "ok",
        CodemodeCallStatus::Error => "error",
        CodemodeCallStatus::Cancelled => "cancelled",
    }
}

fn format_error(error: &CodemodeError, calls: &[CodemodeNestedCall]) -> String {
    let head = match error.kind {
        CodemodeErrorKind::Script => error.stack.clone().unwrap_or_else(|| {
            format!(
                "{}: {}",
                error.name.as_deref().unwrap_or("Error"),
                error.message
            )
        }),
        CodemodeErrorKind::Timeout => format!("Script timed out: {}", error.message),
        CodemodeErrorKind::Aborted => format!("Script aborted: {}", error.message),
        CodemodeErrorKind::Sandbox => format!("Script sandbox failed: {}", error.message),
    };
    let summary = if calls.is_empty() {
        "No tool calls were made.".to_owned()
    } else {
        let list: Vec<String> = calls
            .iter()
            .map(|call| format!("{} ({})", call.name, status_text(call.status)))
            .collect();
        format!(
            "Tool calls made before the failure (they are not undone): {}",
            list.join(", ")
        )
    };
    format!("{head}\n\n{summary}")
}

/// The tool result's content for a script's result, and the path of the
/// complete text when it was cut.
pub(crate) async fn format_result<W: OutputFiles>(
    result: &CodemodeResult,
    options: FormatOptions<'_>,
    files: &W,
) -> FormattedResult {
    let mut output = result.output.clone();
    let failure = match &result.ending {
        CodemodeEnding::Completed { value, .. } => {
            if let Some(value) = value {
                output.push(CodemodeOutputItem::Text {
                    text: value_text(value),
                    origin: TextOrigin::Script,
                });
            }
            None
        }
        CodemodeEnding::Failed(error) => Some(error),
    };
    let mut items = format_items(&output);
    if let Some(error) = failure {
        items.push(Item::Text(format!(
            "Script error:\n{}",
            format_error(error, options.calls)
        )));
    }
    let generated = options.generated_images;
    if generated > 0 && !items.iter().any(|item| matches!(item, Item::Image { .. })) {
        let plural = if generated == 1 { "" } else { "s" };
        items.push(Item::Text(format!(
            "Note: models.generateImages() returned {generated} image{plural} that the script did not show. Show each image block of result.output with image(block)."
        )));
    }
    let (truncated, full_output_path) = truncate(
        join_adjacent_text(items),
        options.max_output_tokens,
        options.limits,
        files,
    )
    .await;
    // After truncation, which joins the text items and moves images after
    // them, so each path stays next to its image.
    let content = join_adjacent_text(save_images(truncated, files).await);
    let status = if failure.is_some() {
        "Script failed"
    } else {
        "Script completed"
    };
    let header = format!(
        "{status}\nWall time {} seconds\nOutput:\n",
        to_fixed_1(options.wall_ms / 1000.0)
    );
    let mut blocks = vec![UserContentBlock::Text(TextContent::new(header))];
    blocks.extend(content.into_iter().map(|item| match item {
        Item::Text(text) => UserContentBlock::Text(TextContent::new(text)),
        Item::Image { data, mime_type } => {
            UserContentBlock::Image(ImageContent { data, mime_type })
        }
    }));
    FormattedResult {
        content: blocks,
        full_output_path,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{Mutex, PoisonError};

    use eukhe_chord::json::to_json;
    use serde_json::json;

    use super::*;
    use crate::codemode::types::CodemodeStoreWrites;

    /// Whether the fake's writes succeed.
    #[derive(Clone, Copy)]
    enum Writes {
        Succeed,
        Fail,
    }

    struct FakeFiles {
        writes: Mutex<Vec<(String, Vec<u8>)>>,
        outcome: Writes,
    }

    impl FakeFiles {
        fn new(outcome: Writes) -> Self {
            Self {
                writes: Mutex::new(Vec::new()),
                outcome,
            }
        }

        fn written(&self) -> Vec<(String, Vec<u8>)> {
            self.writes
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .clone()
        }
    }

    impl OutputFiles for FakeFiles {
        fn write(
            &self,
            name: &str,
            data: &[u8],
        ) -> impl Future<Output = Result<String, String>> + Send {
            self.writes
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push((name.to_owned(), data.to_vec()));
            let result = match self.outcome {
                Writes::Succeed => Ok(format!("/tmp/out/{name}")),
                Writes::Fail => Err("disk full".to_owned()),
            };
            std::future::ready(result)
        }
    }

    const LIMITS: OutputLimits = OutputLimits {
        max_bytes: 50 * 1024,
        max_lines: 2000,
    };

    fn options(calls: &[CodemodeNestedCall]) -> FormatOptions<'_> {
        FormatOptions {
            generated_images: 0,
            wall_ms: 1234.0,
            max_output_tokens: DEFAULT_MAX_OUTPUT_TOKENS,
            calls,
            limits: LIMITS,
        }
    }

    fn completed(
        value: Option<serde_json::Value>,
        output: Vec<CodemodeOutputItem>,
    ) -> CodemodeResult {
        CodemodeResult {
            ending: CodemodeEnding::Completed {
                value: value.map(|value| to_json(&value).expect("JSON value")),
                store_writes: CodemodeStoreWrites::default(),
            },
            output,
            during: None,
        }
    }

    fn failed(error: CodemodeError, output: Vec<CodemodeOutputItem>) -> CodemodeResult {
        CodemodeResult {
            ending: CodemodeEnding::Failed(error),
            output,
            during: None,
        }
    }

    fn script(text: &str) -> CodemodeOutputItem {
        CodemodeOutputItem::Text {
            text: text.to_owned(),
            origin: TextOrigin::Script,
        }
    }

    fn console(text: &str) -> CodemodeOutputItem {
        CodemodeOutputItem::Text {
            text: text.to_owned(),
            origin: TextOrigin::Console,
        }
    }

    fn image(data: &str, mime_type: &str) -> CodemodeOutputItem {
        CodemodeOutputItem::Image {
            data: data.to_owned(),
            mime_type: mime_type.to_owned(),
        }
    }

    fn text(text: &str) -> UserContentBlock {
        UserContentBlock::Text(TextContent::new(text))
    }

    fn image_block(data: &str, mime_type: &str) -> UserContentBlock {
        UserContentBlock::Image(ImageContent {
            data: data.to_owned(),
            mime_type: mime_type.to_owned(),
        })
    }

    const COMPLETED: &str = "Script completed\nWall time 1.2 seconds\nOutput:\n";
    const FAILED: &str = "Script failed\nWall time 1.2 seconds\nOutput:\n";

    #[tokio::test]
    async fn marks_several_text_items_and_collects_console_lines() {
        let files = FakeFiles::new(Writes::Succeed);
        let result = completed(
            Some(json!({"x": 1})),
            vec![script("a"), console("log1"), script("b"), console("log2")],
        );
        assert_eq!(
            format_result(&result, options(&[]), &files).await,
            FormattedResult {
                content: vec![
                    text(COMPLETED),
                    text("==> text 1/3 <==\na\n==> text 2/3 <==\nb\n==> text 3/3 <==\n{\"x\":1}\n<console_output>\nlog1\nlog2\n</console_output>"),
                ],
                full_output_path: None,
            }
        );
        assert_eq!(files.written(), Vec::new());
    }

    #[tokio::test]
    async fn single_text_has_no_marker_and_keeps_its_newline() {
        let files = FakeFiles::new(Writes::Succeed);
        let result = completed(Some(json!("line\n")), vec![console("c")]);
        assert_eq!(
            format_result(&result, options(&[]), &files).await,
            FormattedResult {
                content: vec![
                    text(COMPLETED),
                    text("line\n<console_output>\nc\n</console_output>")
                ],
                full_output_path: None,
            }
        );
    }

    #[tokio::test]
    async fn exit_without_output_is_the_header() {
        let files = FakeFiles::new(Writes::Succeed);
        assert_eq!(
            format_result(&completed(None, Vec::new()), options(&[]), &files).await,
            FormattedResult {
                content: vec![text(COMPLETED)],
                full_output_path: None
            }
        );
    }

    #[tokio::test]
    async fn truncates_to_the_token_budget_and_spills_the_text() {
        let files = FakeFiles::new(Writes::Succeed);
        let result = completed(None, vec![script("0123456789abcdefghij")]);
        let options = FormatOptions {
            max_output_tokens: 2,
            ..options(&[])
        };
        assert_eq!(
            format_result(&result, options, &files).await,
            FormattedResult {
                content: vec![
                    text(COMPLETED),
                    text("Warning: truncated output (original token count: 5)\nTotal output lines: 1\n\n0123…3 tokens truncated…ghij\n\n[Full output: /tmp/out/output.txt (read with offset/limit)]"),
                ],
                full_output_path: Some("/tmp/out/output.txt".to_owned()),
            }
        );
        assert_eq!(
            files.written(),
            vec![("output.txt".to_owned(), b"0123456789abcdefghij".to_vec())]
        );
    }

    #[tokio::test]
    async fn truncates_to_the_line_limit_and_reports_a_failed_spill() {
        let files = FakeFiles::new(Writes::Fail);
        let result = completed(
            Some(json!("1\n2\n3\n4\n5")),
            vec![image("AAEC", "image/gif")],
        );
        let options = FormatOptions {
            limits: OutputLimits {
                max_bytes: 50 * 1024,
                max_lines: 104,
            },
            ..options(&[])
        };
        assert_eq!(
            format_result(&result, options, &files).await,
            FormattedResult {
                content: vec![
                    text(COMPLETED),
                    text("Warning: truncated output (original token count: 3)\nTotal output lines: 5\n\n1\n2…1 tokens truncated…4\n5\n\n[Could not save the full output: disk full]\n[Image (image/gif, 3 bytes) could not be saved: disk full]"),
                    image_block("AAEC", "image/gif"),
                ],
                full_output_path: None,
            }
        );
        assert_eq!(
            files.written(),
            vec![
                ("output.txt".to_owned(), b"1\n2\n3\n4\n5".to_vec()),
                ("image-1.gif".to_owned(), vec![0, 1, 2]),
            ]
        );
    }

    #[tokio::test]
    async fn saves_each_image_once_and_labels_it() {
        let files = FakeFiles::new(Writes::Succeed);
        let result = completed(
            None,
            vec![
                image("aGVsbG8=", "image/png"),
                script("t"),
                image("aGVsbG8=", "image/png"),
                image("AAEC", "image/bmp"),
            ],
        );
        assert_eq!(
            format_result(&result, options(&[]), &files).await,
            FormattedResult {
                content: vec![
                    text(COMPLETED),
                    text("[Image saved to /tmp/out/image-1.png (image/png, 5 bytes)]"),
                    image_block("aGVsbG8=", "image/png"),
                    text("t\n[Image saved to /tmp/out/image-1.png (image/png, 5 bytes)]"),
                    image_block("aGVsbG8=", "image/png"),
                    text("[Image saved to /tmp/out/image-2.bin (image/bmp, 3 bytes)]"),
                    image_block("AAEC", "image/bmp"),
                ],
                full_output_path: None,
            }
        );
        assert_eq!(
            files.written(),
            vec![
                ("image-1.png".to_owned(), b"hello".to_vec()),
                ("image-2.bin".to_owned(), vec![0, 1, 2]),
            ]
        );
    }

    #[tokio::test]
    async fn script_error_without_calls() {
        let files = FakeFiles::new(Writes::Succeed);
        let error = CodemodeError {
            kind: CodemodeErrorKind::Script,
            name: None,
            message: "boom".to_owned(),
            stack: None,
        };
        assert_eq!(
            format_result(
                &failed(error, vec![script("partial")]),
                options(&[]),
                &files
            )
            .await,
            FormattedResult {
                content: vec![
                    text(FAILED),
                    text("partial\nScript error:\nError: boom\n\nNo tool calls were made."),
                ],
                full_output_path: None,
            }
        );
    }

    #[tokio::test]
    async fn errors_list_the_calls_made() {
        let files = FakeFiles::new(Writes::Succeed);
        let call = |id, name: &str, status| CodemodeNestedCall {
            id,
            name: name.to_owned(),
            args: "{}".to_owned(),
            status,
            duration_ms: None,
            error: None,
        };
        let calls = [
            call(1, "read", CodemodeCallStatus::Ok),
            call(2, "write", CodemodeCallStatus::Cancelled),
        ];
        let timeout = CodemodeError {
            kind: CodemodeErrorKind::Timeout,
            name: None,
            message: "60000 ms".to_owned(),
            stack: None,
        };
        assert_eq!(
            format_result(&failed(timeout, Vec::new()), options(&calls), &files).await,
            FormattedResult {
                content: vec![
                    text(FAILED),
                    text("Script error:\nScript timed out: 60000 ms\n\nTool calls made before the failure (they are not undone): read (ok), write (cancelled)"),
                ],
                full_output_path: None,
            }
        );
        let thrown = CodemodeError {
            kind: CodemodeErrorKind::Script,
            name: Some("TypeError".to_owned()),
            message: "x".to_owned(),
            stack: Some("TypeError: x\n    at <eval>".to_owned()),
        };
        assert_eq!(
            format_result(&failed(thrown, Vec::new()), options(&calls[..1]), &files).await,
            FormattedResult {
                content: vec![
                    text(FAILED),
                    text("Script error:\nTypeError: x\n    at <eval>\n\nTool calls made before the failure (they are not undone): read (ok)"),
                ],
                full_output_path: None,
            }
        );
        let sandbox = CodemodeError {
            kind: CodemodeErrorKind::Sandbox,
            name: Some("Ignored".to_owned()),
            message: "VM gone".to_owned(),
            stack: None,
        };
        assert_eq!(
            format_result(&failed(sandbox, Vec::new()), options(&[]), &files).await,
            FormattedResult {
                content: vec![
                    text(FAILED),
                    text(
                        "Script error:\nScript sandbox failed: VM gone\n\nNo tool calls were made."
                    ),
                ],
                full_output_path: None,
            }
        );
    }

    #[tokio::test]
    async fn notes_generated_images_the_script_did_not_show() {
        let files = FakeFiles::new(Writes::Succeed);
        let two = FormatOptions {
            generated_images: 2,
            ..options(&[])
        };
        assert_eq!(
            format_result(&completed(None, Vec::new()), two, &files).await,
            FormattedResult {
                content: vec![
                    text(COMPLETED),
                    text("Note: models.generateImages() returned 2 images that the script did not show. Show each image block of result.output with image(block)."),
                ],
                full_output_path: None,
            }
        );
        let shown = completed(None, vec![image("AAEC", "image/gif")]);
        let one = FormatOptions {
            generated_images: 1,
            ..options(&[])
        };
        assert_eq!(
            format_result(&shown, one, &files).await,
            FormattedResult {
                content: vec![
                    text(COMPLETED),
                    text("[Image saved to /tmp/out/image-1.gif (image/gif, 3 bytes)]"),
                    image_block("AAEC", "image/gif"),
                ],
                full_output_path: None,
            }
        );
    }

    #[test]
    fn to_fixed_rounds_ties_up() {
        let formatted: Vec<String> = [0.25, 1.05, 0.0, 12.34, 0.04]
            .into_iter()
            .map(to_fixed_1)
            .collect();
        assert_eq!(formatted, vec!["0.3", "1.1", "0.0", "12.3", "0.0"]);
    }

    #[test]
    fn js_slice_handles_negative_bounds() {
        assert_eq!(js_slice(5, 0, Some(2)), 0..2);
        assert_eq!(js_slice(5, -2, None), 3..5);
        assert_eq!(js_slice(5, 0, Some(-1)), 0..4);
        assert_eq!(js_slice(5, 0, None), 0..5);
        assert_eq!(js_slice(2, -7, Some(9)), 0..2);
    }
}
