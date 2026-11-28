//! Tool-call card rendering, the TUI side of the TS `tool-execution.ts` /
//! `ipython-cell.ts` renderer stack. The card model mirrors the TS
//! component state (args, execution start, partial results, live timing);
//! every tool builds its card as `crate::element` rows -- one summary row
//! at the default detail, the body hanging below it when expanded -- and
//! the element renderer draws them.

pub mod bash;
mod diff;
pub mod generic;
#[cfg(test)]
mod golden_tests;
pub mod highlight;
pub mod ipython;
pub mod ipython_details;
mod layout;
mod summary;
pub mod worker;

use std::time::Instant;

use serde_json::Value;

use crate::chat::Detail;
use crate::element::Status;
use crate::theme::{Theme, ThemeColor};
use crate::{Line, Span};

/// One tool call and its execution state (TS `ToolExecutionComponent`
/// state minus the renderer caches).
#[derive(Debug, Clone, PartialEq, Default)]
pub struct ToolCallCard {
    pub id: String,
    pub name: ToolName,
    pub args: Value,
    /// `tool_execution_start` seen (live only; replayed cards infer it from
    /// the result).
    pub started: bool,
    /// When the execution started, when seen live (drives `Took`/`Elapsed`).
    pub started_at: Option<Instant>,
    /// When the final result landed (replay sets start and end together).
    pub ended_at: Option<Instant>,
    /// The result so far; `None` until the first result frame.
    pub result: Option<ToolResultView>,
    /// `result` is a partial streaming frame.
    pub result_partial: bool,
    /// The run's failed final frame (an abort or a provider error) settled
    /// this still-pending card with the run's error text; the tool's late
    /// result frames are dropped (TS `resetPendingToolState` removed the
    /// component from the pending map the same way).
    pub aborted: bool,
}

/// A tool call's name: the tools whose cards render their own way, else
/// the name as sent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ToolName {
    Python,
    /// The REPL's name in sessions stored before `python`.
    Ipython,
    Bash,
    Edit,
    WorkerAssign,
    WorkerForward,
    Other(String),
}

impl Default for ToolName {
    fn default() -> Self {
        Self::Other(String::new())
    }
}

impl ToolName {
    /// The wire name.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::Python => "python",
            Self::Ipython => "ipython",
            Self::Bash => "bash",
            Self::Edit => "edit",
            Self::WorkerAssign => "worker_assign",
            Self::WorkerForward => "worker_forward",
            Self::Other(name) => name,
        }
    }

    /// A `python` cell, under either of its names.
    #[must_use]
    pub fn is_python(&self) -> bool {
        matches!(self, Self::Python | Self::Ipython)
    }
}

impl From<&str> for ToolName {
    fn from(name: &str) -> Self {
        match name {
            "python" => Self::Python,
            "ipython" => Self::Ipython,
            "bash" => Self::Bash,
            "edit" => Self::Edit,
            "worker_assign" => Self::WorkerAssign,
            "worker_forward" => Self::WorkerForward,
            other => Self::Other(other.to_string()),
        }
    }
}

impl From<String> for ToolName {
    fn from(name: String) -> Self {
        match Self::from(name.as_str()) {
            Self::Other(_) => Self::Other(name),
            known => known,
        }
    }
}

impl std::fmt::Display for ToolName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The wire JSON of one content block, as the cards read it (every field,
/// the image metadata included).
pub(crate) fn content_block_value(block: &eukhe_types::ai::UserContentBlock) -> Value {
    serde_json::json!(block)
}

/// One (partial or final) tool result (TS `AgentToolResult` view).
#[derive(Debug, Clone, PartialEq, Default)]
pub struct ToolResultView {
    pub content: Vec<Value>,
    /// The part of the result's details its card reads ([`card_details`]).
    pub details: Value,
    pub is_error: bool,
}

impl ToolResultView {
    /// The view of one tool output, as the card of `tool_name` keeps it.
    #[must_use]
    pub fn new(tool_name: &str, output: &eukhe_types::daemon::ToolOutput, is_error: bool) -> Self {
        Self {
            content: output.content.iter().map(content_block_value).collect(),
            details: card_details(tool_name, output.details.as_ref()),
            is_error,
        }
    }

    /// The joined text of the result's text blocks, ANSI stripped, with
    /// hidden image blocks appended as `[Image: ...]` fallback text (TS
    /// `render-utils.getTextOutput` with `showImages` false: each image
    /// contributes its mime type and, when the payload parses, its
    /// dimensions).
    pub fn text_output(&self, show_images: bool) -> String {
        let mut parts: Vec<String> = Vec::new();
        for block in &self.content {
            match block.get("type").and_then(Value::as_str) {
                Some("text") => parts.push(
                    crate::error_summary::normalize_error_details(
                        block
                            .get("text")
                            .and_then(Value::as_str)
                            .unwrap_or_default(),
                    )
                    .replace('\r', ""),
                ),
                Some("image") if !show_images => parts.push(hidden_image_text(block)),
                _ => {}
            }
        }
        parts.join("\n")
    }
}

/// The `[Image: ...]` text standing in for one hidden image block (TS
/// `imageFallback(mimeType, dims)` with `includeImageDimensions: false` --
/// the interactive transcript's two mount sites pass the knob off, so the
/// hidden text never parses image dimensions; the export renderer is the
/// dims-including consumer). The payload is never decoded: the text is
/// the mime alone, for live payloads and elided markers alike.
pub(super) fn hidden_image_text(block: &Value) -> String {
    let mime = block
        .get("mimeType")
        .and_then(Value::as_str)
        .unwrap_or("image/unknown");
    crate::terminal_image::image_fallback(mime, None, None)
}

/// The image block's rendered size segment: `140.1KB` -- the elided payload's
/// byte count when the transcript load replaced the data, the payload's own
/// length otherwise. Never touches the payload beyond its length.
pub(crate) fn image_block_size_text(block: &Value) -> String {
    format_size(image_block_bytes(block))
}

/// The payload's size in bytes, from the elision marker when present (the
/// transcript load's [`crate::snapshot`] marker shape: `elidedBytes`),
/// from the payload's own character length otherwise.
pub(crate) fn image_block_bytes(block: &Value) -> usize {
    block
        .get("elidedBytes")
        .and_then(Value::as_u64)
        .map_or_else(
            || {
                block
                    .get("data")
                    .and_then(Value::as_str)
                    .map_or(0, str::len)
            },
            |bytes| bytes as usize,
        )
}

/// The part of a result's `details` the card of `tool_name` reads (the
/// [`render_tool_card`] shells); the rest is dropped when the result
/// lands, so a card holds its output once: a `read` result's details
/// repeat the whole output twice (`rendered`, `text`), and the generic
/// card reads none of them.
#[must_use]
pub(crate) fn card_details(tool_name: &str, details: Option<&Value>) -> Value {
    let keys: &[&str] = match tool_name {
        "python" | "ipython" | "worker_assign" | "worker_forward" => {
            return details.cloned().unwrap_or(Value::Null);
        }
        "bash" => bash::DETAIL_KEYS,
        "edit" => generic::EDIT_DETAIL_KEYS,
        _ => return Value::Null,
    };
    match details {
        Some(Value::Object(details)) => Value::Object(
            keys.iter()
                .filter_map(|key| details.get_key_value(*key))
                .map(|(key, value)| (key.clone(), value.clone()))
                .collect(),
        ),
        _ => Value::Null,
    }
}

/// Render one tool-call card through its tool shell. `show_images` is the
/// `terminal.showImages` setting (TS `showImages` on the tool component):
/// image blocks render their metadata rows when set, their
/// `[Image: ...]` text placeholders otherwise.
#[must_use]
pub fn render_tool_card(
    card: &ToolCallCard,
    frame: usize,
    detail: Detail,
    theme: &Theme,
    width: usize,
    show_images: bool,
) -> Vec<Line> {
    match card.name {
        ToolName::Python | ToolName::Ipython => {
            ipython::render(card, frame, detail, theme, width, show_images)
        }
        ToolName::Bash => bash::render(card, frame, detail, theme, width, show_images),
        ToolName::WorkerAssign | ToolName::WorkerForward => {
            worker::render(card, frame, theme, width)
        }
        ToolName::Edit | ToolName::Other(_) => {
            generic::render(card, frame, detail, theme, width, show_images)
        }
    }
}

/// The settled card marks its call failed (`x`): an error result, and
/// for `bash` and `python` a nonzero exit or a refusal too. The turn's
/// usage footer counts its failed calls by the same mark.
#[must_use]
pub(crate) fn marks_failed(card: &ToolCallCard) -> bool {
    match card.name {
        ToolName::Python | ToolName::Ipython => ipython::failed(card),
        ToolName::Bash => bash::failed(card),
        ToolName::Edit | ToolName::WorkerAssign | ToolName::WorkerForward | ToolName::Other(_) => {
            card.result.as_ref().is_some_and(|result| result.is_error)
        }
    }
}

/// The generic panel status (TS `ToolExecutionComponent.panelStatus`):
/// the last non-partial result settles the card; error wins even while
/// streaming; `running` animates until then.
pub(crate) fn panel_status(card: &ToolCallCard) -> Status {
    if let Some(result) = &card.result {
        if !card.result_partial {
            return if result.is_error {
                Status::Error
            } else {
                Status::Done
            };
        }
        if result.is_error {
            return Status::Error;
        }
    }
    if card.started {
        Status::Running
    } else {
        Status::Queued
    }
}

/// `formatSize` (TS `truncate.ts`): `512B`, `50.0KB`, `1.2MB`.
#[must_use]
pub fn format_size(bytes: usize) -> String {
    if bytes < 1024 {
        format!("{bytes}B")
    } else if bytes < 1024 * 1024 {
        format!("{:.1}KB", bytes as f64 / 1024.0)
    } else {
        format!("{:.1}MB", bytes as f64 / (1024.0 * 1024.0))
    }
}

/// Image result blocks render their metadata row below the card, at the
/// tool quote column (TS `tool-execution.ts` adds one `Image` component
/// per result image block, with `fallbackOnly`, in the toolOutput
/// fallback color). Blocks without data or a mime type, and
/// every image while `show_images` is false, render nothing here -- the
/// hidden ones contribute their `[Image: ...]` text through
/// [`ToolResultView::text_output`] instead.
///
/// The row is built from the block's metadata only (the render-path skip,
/// the image-heavy session-open fix): the TS component decoded the whole
/// base64 string for its dimensions, and a tool result carrying megabytes
/// of image payload paid that decode on every visited card. The
/// dimensions now come from [`get_image_dimensions_prefix`]'s bounded
/// prefix read, and a payload whose header does not parse from the
/// prefix renders its size instead -- `[image/jpeg * 140.1KB omitted]` --
/// so the base64 is never cloned or decoded in full.
///
/// [`get_image_dimensions_prefix`]:
/// crate::terminal_image::get_image_dimensions_prefix
pub(crate) fn image_rows(
    result: Option<&ToolResultView>,
    show_images: bool,
    theme: &Theme,
) -> Vec<Line> {
    let fallback = theme.fg_style(ThemeColor::ToolOutput);
    let mut rows: Vec<Line> = Vec::new();
    for block in eligible_image_blocks(result, show_images) {
        rows.push(vec![Span::styled(
            format!(
                "{}{}",
                " ".repeat(crate::rows::Gutter::ToolQuote.mark_col()),
                image_block_row_text(block)
            ),
            fallback,
        )]);
    }
    rows
}

/// The metadata-row text for one shown image block: the TS `Image`
/// component's fallback-only shape `[mime * WxH]`, or the size-only
/// placeholder `[mime * 140.1KB omitted]` when the dimensions are not
/// available. The dimensions come from the elision marker's
/// `widthPx`/`heightPx` when the transcript load elided the payload, and
/// from the payload's bounded prefix otherwise (never a full decode).
/// Computed without cloning the payload.
pub(crate) fn image_block_row_text(block: &Value) -> String {
    let mime = block
        .get("mimeType")
        .and_then(Value::as_str)
        .unwrap_or("image/unknown");
    let dimensions = image_block_dimensions(block);
    match dimensions {
        Some(dimensions) => format!(
            "[{mime} - {}x{}]",
            dimensions.width_px, dimensions.height_px
        ),
        None => format!("[{mime} - {} omitted]", image_block_size_text(block)),
    }
}

/// The image block's pixel dimensions, without a payload decode: the
/// elision marker's `widthPx`/`heightPx` when the transcript load elided
/// the data (the marker the daemon's attach snapshot writes), else the
/// bounded-prefix read of the payload.
pub(crate) fn image_block_dimensions(
    block: &Value,
) -> Option<crate::terminal_image::ImageDimensions> {
    if let (Some(width), Some(height)) = (
        block.get("widthPx").and_then(Value::as_u64),
        block.get("heightPx").and_then(Value::as_u64),
    ) {
        return Some(crate::terminal_image::ImageDimensions {
            width_px: width as u32,
            height_px: height as u32,
        });
    }
    match (
        block.get("data").and_then(Value::as_str),
        block.get("mimeType").and_then(Value::as_str),
    ) {
        (Some(data), Some(mime)) => crate::terminal_image::get_image_dimensions_prefix(
            data,
            mime,
            crate::terminal_image::IMAGE_DIMENSIONS_PREFIX_BYTES,
        ),
        _ => None,
    }
}

fn eligible_image_blocks(
    result: Option<&ToolResultView>,
    show_images: bool,
) -> impl Iterator<Item = &Value> {
    result
        .into_iter()
        .flat_map(|result| result.content.iter())
        .filter(move |block| {
            // A block whose `data` or `mimeType` is not a string renders
            // no image row.
            show_images
                && block.get("type").and_then(Value::as_str) == Some("image")
                && block.get("data").and_then(Value::as_str).is_some()
                && block.get("mimeType").and_then(Value::as_str).is_some()
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn theme() -> crate::theme::Theme {
        use crate::theme::{ColorMode, Theme};
        Theme::builtin("forge", ColorMode::TrueColor)
    }

    fn text_of(line: &Line) -> String {
        line.iter().map(|s| s.content.as_str()).collect()
    }

    fn tiny_png(width: u32, height: u32) -> String {
        use base64::Engine;
        let mut bytes = vec![0x89, b'P', b'N', b'G'];
        bytes.extend(vec![0u8; 12]); // length + IHDR tag
        bytes.extend(width.to_be_bytes());
        bytes.extend(height.to_be_bytes());
        base64::engine::general_purpose::STANDARD.encode(bytes)
    }

    /// A card keeps only the details its shell reads: a `read` result's
    /// copies of the output (`rendered`, `text`) are dropped, `bash` keeps
    /// its status and truncation keys, `edit` its diffs, `python` all.
    #[test]
    fn a_card_keeps_only_the_details_its_shell_reads() {
        let read = serde_json::json!({ "rendered": "1:a", "text": "a", "path": "f" });
        assert_eq!(card_details("read", Some(&read)), Value::Null);
        let bash = serde_json::json!({
            "version": "bash@1",
            "steps": [{ "command": "ls" }],
            "end": { "kind": "finished", "status": 0 },
            "fullOutputPath": "/tmp/out",
        });
        assert_eq!(
            card_details("bash", Some(&bash)),
            serde_json::json!({
                "end": { "kind": "finished", "status": 0 },
                "fullOutputPath": "/tmp/out",
            })
        );
        let edit = serde_json::json!({ "files": [{ "path": "f", "diff": "+a" }], "rendered": "x" });
        assert_eq!(
            card_details("edit", Some(&edit)),
            serde_json::json!({ "files": [{ "path": "f", "diff": "+a" }] })
        );
        assert_eq!(card_details("python", Some(&read)), read);
        assert_eq!(card_details("bash", None), Value::Null);
    }

    fn image_result(data: &str, mime: &str) -> Option<ToolResultView> {
        Some(ToolResultView {
            content: vec![
                serde_json::json!({ "type": "text", "text": "done" }),
                serde_json::json!({ "type": "image", "data": data, "mimeType": mime }),
            ],
            details: serde_json::Value::Null,
            is_error: false,
        })
    }

    #[test]
    fn shown_image_rows_render_metadata_without_materializing_the_payload() {
        // A payload whose header parses but whose tail (past the bounded
        // prefix) is invalid base64: the row still renders its dimensions,
        // proving the payload was never decoded in full -- a full decode
        // would have failed and rendered the size placeholder instead.
        let payload = format!("{}{}{}", tiny_png(64, 32), "A".repeat(4096), "!".repeat(64));
        let result = image_result(&payload, "image/png");
        let rows = image_rows(result.as_ref(), true, &theme());
        let flat: Vec<String> = rows.iter().map(text_of).collect();
        assert_eq!(flat, vec!["      [image/png - 64x32]".to_string()]);
        // The render never emits any of the payload's tail bytes.
        assert!(flat.iter().all(|row| !row.contains("AAAA")));
    }

    #[test]
    fn shown_image_rows_render_the_size_placeholder_when_the_header_does_not_parse() {
        // A payload whose dimensions do not parse from the bounded prefix
        // renders its size instead (the honest omission marker).
        let payload = "x".repeat(186_328);
        let result = image_result(&payload, "image/jpeg");
        let rows = image_rows(result.as_ref(), true, &theme());
        let flat: Vec<String> = rows.iter().map(text_of).collect();
        assert_eq!(
            flat,
            vec!["      [image/jpeg - 182.0KB omitted]".to_string()]
        );
    }

    #[test]
    fn elided_payloads_render_the_size_placeholder_from_the_marker() {
        // The transcript load's elision marker (data emptied, the byte
        // count in elidedBytes): the row renders from the marker alone.
        let result = Some(ToolResultView {
            content: vec![serde_json::json!({
                "type": "image",
                "data": "",
                "mimeType": "image/jpeg",
                "elidedBytes": 186_328
            })],
            details: serde_json::Value::Null,
            is_error: false,
        });
        let rows = image_rows(result.as_ref(), true, &theme());
        let flat: Vec<String> = rows.iter().map(text_of).collect();
        assert_eq!(
            flat,
            vec!["      [image/jpeg - 182.0KB omitted]".to_string()]
        );
    }

    #[test]
    fn hidden_image_text_never_parses_the_payload_or_the_marker() {
        let view = ToolResultView {
            content: vec![serde_json::json!({
                "type": "image",
                "data": tiny_png(64, 32),
                "mimeType": "image/png"
            })],
            ..Default::default()
        };
        assert_eq!(view.text_output(false), "[Image: [image/png]]");

        let elided = ToolResultView {
            content: vec![serde_json::json!({
                "type": "image",
                "data": "",
                "mimeType": "image/jpeg",
                "elidedBytes": 186_328
            })],
            ..Default::default()
        };
        assert_eq!(elided.text_output(false), "[Image: [image/jpeg]]");
    }

    #[test]
    fn non_string_data_blocks_render_no_rows() {
        // A `data: null` image block is not an image row.
        let result = Some(ToolResultView {
            content: vec![serde_json::json!({
                "type": "image",
                "data": null,
                "mimeType": "image/png"
            })],
            details: serde_json::Value::Null,
            is_error: false,
        });
        assert!(image_rows(result.as_ref(), true, &theme()).is_empty());
        // The elided marker (data: "") stays a real row.
        let elided = Some(ToolResultView {
            content: vec![serde_json::json!({
                "type": "image",
                "data": "",
                "mimeType": "image/png",
                "elidedBytes": 500 * 1024
            })],
            details: serde_json::Value::Null,
            is_error: false,
        });
        assert_eq!(image_rows(elided.as_ref(), true, &theme()).len(), 1);
    }

    #[test]
    fn panel_status_settles_on_error_even_while_partial() {
        let mut card = ToolCallCard {
            name: "bash".into(),
            started: true,
            ..Default::default()
        };
        card.result = Some(ToolResultView {
            is_error: true,
            ..Default::default()
        });
        card.result_partial = true;
        assert_eq!(panel_status(&card), Status::Error);
        card.result_partial = false;
        assert_eq!(panel_status(&card), Status::Error);
        card.result = Some(ToolResultView::default());
        assert_eq!(panel_status(&card), Status::Done);
        card.result = None;
        assert_eq!(panel_status(&card), Status::Running);
        card.started = false;
        assert_eq!(panel_status(&card), Status::Queued);
    }
}
