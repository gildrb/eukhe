//! Splitting a payload into `[path#TAG]` sections (omp
//! `modes/hashline/input.rs`).

use std::{collections::HashMap, path::Path, sync::LazyLock};

use regex::Regex;

use super::{
    clipboard::has_clipboard_edit,
    messages::{
        json_quote, ABORT_MARKER, BEGIN_PATCH_MARKER, CLIPBOARD_INTERLEAVED_SECTIONS,
        END_PATCH_MARKER, HL_FILE_HASH_EXAMPLES, HL_FILE_HASH_LENGTH,
    },
    parser::parse_patch,
    tokenizer::{classify_line, header_path_has_orphan_bracket, Token},
    types::{Edit, FileOp},
};
use crate::error::EditError;

/// Envelope and abort sentinels recognized when nested inside a header row.
const ENVELOPE_MARKERS: [&str; 3] = [BEGIN_PATCH_MARKER, END_PATCH_MARKER, ABORT_MARKER];

static APPLY_PATCH_PATH_NOISE_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?i)^\*{0,3}\s*(?:(?:update|add|delete|move)[^A-Za-z0-9]*(?:file|to)?[^A-Za-z0-9]*:)?\s*\*{0,3}\s*",
    )
    .expect("valid regex")
});
static RECOVERY_TAG_RE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"#([0-9A-Fa-f]{4})\s*$").expect("valid regex"));
static UNIFIED_HUNK_RE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^@@\s+[-+]?\d+,\d+\s+[-+]?\d+,\d+\s+@@").expect("valid regex"));

/// Parsed edits, optional file operation, and parser warnings for one section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Parsed {
    pub(crate) edits: Vec<Edit>,
    pub(crate) file_op: Option<FileOp>,
    pub(crate) warnings: Vec<String>,
}

/// One target file section: authored path, optional tag, and body.
#[derive(Debug, Clone)]
pub(crate) struct PatchSection {
    pub(crate) path: String,
    pub(crate) file_hash: Option<String>,
    pub(crate) diff: String,
    /// Same-path sections were merged across another file's section.
    interleaved: bool,
}

impl PatchSection {
    /// Parse this section's body. Interleaved same-path sections may not use
    /// the clipboard; a `MV` destination loses apply-patch path noise.
    pub(crate) fn parse(&self) -> Result<Parsed, EditError> {
        let mut parsed = parse_patch(&self.diff).map_err(EditError::parse)?;
        if self.interleaved && has_clipboard_edit(&parsed.edits) {
            return Err(EditError::parse(CLIPBOARD_INTERLEAVED_SECTIONS));
        }
        if let Some(FileOp::Move { dest }) = &mut parsed.file_op {
            *dest = normalize_hashline_path(dest, None);
        }
        Ok(parsed)
    }

    /// The same section bound to another path.
    pub(crate) fn with_path(&self, path: &str) -> Self {
        Self {
            path: path.to_owned(),
            ..self.clone()
        }
    }
}

/// Split and coalesce the authored file sections of a payload. Absolute
/// header paths under `cwd` become cwd-relative.
pub(crate) fn split_sections(input: &str, cwd: &Path) -> Result<Vec<PatchSection>, EditError> {
    merge_same_path_sections(split_raw_sections(input, cwd)?)
}

fn unquote(path: &str) -> &str {
    if path.len() >= 2
        && ((path.starts_with('"') && path.ends_with('"'))
            || (path.starts_with('\'') && path.ends_with('\'')))
    {
        &path[1..path.len() - 1]
    } else {
        path
    }
}

fn normalize_hashline_path(raw: &str, cwd: Option<&Path>) -> String {
    let cleaned = APPLY_PATCH_PATH_NOISE_RE
        .replace(unquote(raw.trim()), "")
        .into_owned();
    let path = Path::new(&cleaned);
    let Some(cwd) = cwd else {
        return cleaned;
    };
    if !path.is_absolute() {
        return cleaned;
    }
    let path = crate::path::lexical_normalize(path);
    let cwd = crate::path::lexical_normalize(cwd);
    if let Ok(relative) = path.strip_prefix(&cwd) {
        let text = relative
            .to_string_lossy()
            .replace(std::path::MAIN_SEPARATOR, "/");
        return if text.is_empty() { ".".into() } else { text };
    }
    cleaned
}

fn parse_header_line(line: &str, cwd: &Path) -> Result<Option<PatchSection>, EditError> {
    let trimmed = unbracket_envelope_markers(line.trim_end());
    if !trimmed.starts_with('[') {
        return Ok(None);
    }
    if let Token::Header {
        path, file_hash, ..
    } = classify_line(trimmed, 0)
    {
        let path = normalize_hashline_path(&path, Some(cwd));
        if path.is_empty() {
            return Err(EditError::parse(
                "Input header \"[]\" is empty; provide a file path.",
            ));
        }
        return Ok(Some(PatchSection {
            path,
            file_hash,
            diff: String::new(),
            interleaved: false,
        }));
    }
    if let Some(recovered) = recover_header(trimmed, cwd) {
        return Ok(Some(recovered));
    }
    Err(EditError::parse(format!(
        "Input header must be [PATH] or [PATH#TAG] with a {HL_FILE_HASH_LENGTH}-hex content-hash \
         tag; got {}.",
        json_quote(trimmed)
    )))
}

fn recover_header(line: &str, cwd: &Path) -> Option<PatchSection> {
    let body = line.strip_prefix('[')?.strip_suffix(']')?.trim();
    let body = APPLY_PATCH_PATH_NOISE_RE.replace(body, "").into_owned();
    if body.is_empty() {
        return None;
    }
    let (path_text, file_hash) = if let Some(captures) = RECOVERY_TAG_RE.captures(&body) {
        let whole = captures.get(0)?;
        (
            &body[..whole.start()],
            Some(captures[1].to_ascii_uppercase()),
        )
    } else {
        (body.trim_end(), None)
    };
    if path_text.contains('#') || header_path_has_orphan_bracket(path_text) {
        return None;
    }
    let path = normalize_hashline_path(path_text, Some(cwd));
    (!path.is_empty()).then_some(PatchSection {
        path,
        file_hash,
        diff: String::new(),
        interleaved: false,
    })
}

/// Unwrap leading bracketed `apply_patch` envelope markers from a row.
///
/// Models that mix `apply_patch` framing into hashline nest the sentinel in the
/// section header (`[*** Begin Patch] [src/a.ts#1A2B]`, or unclosed as
/// `[*** Begin Patch [src/a.ts#1A2B]`) or put it alone on a bracketed row
/// (`[*** End Patch]`). Bare sentinel rows are already consumed by the
/// tokenizer, so unwrapping the bracketed shape routes it down the same path;
/// otherwise the whole row parses as one header and the edit targets a file
/// called `Begin Patch] [src/a.ts`. A row carrying no such group comes back
/// unchanged; a row that is nothing but one comes back as the bare marker.
fn unbracket_envelope_markers(line: &str) -> &str {
    let mut rest = line;
    loop {
        let Some(inner) = rest.strip_prefix('[').map(str::trim_start) else {
            return rest;
        };
        let Some(marker) = ENVELOPE_MARKERS
            .iter()
            .find(|marker| inner.starts_with(**marker))
        else {
            return rest;
        };
        let tail = inner[marker.len()..].trim_start();
        let tail = tail.strip_prefix(']').unwrap_or(tail).trim_start();
        if tail.is_empty() {
            return marker;
        }
        rest = tail;
    }
}

fn strip_leading_blanks(input: &str) -> String {
    let input = input.strip_prefix('\u{feff}').unwrap_or(input);
    let mut lines: Vec<&str> = input.split('\n').collect();
    let leading = lines
        .iter()
        .take_while(|line| {
            let clean = unbracket_envelope_markers(line.trim_end_matches('\r'));
            clean.trim().is_empty()
                || matches!(classify_line(clean, 0), Token::EnvelopeBegin { .. })
        })
        .count();
    lines.drain(..leading);
    lines.join("\n")
}

fn split_raw_sections(input: &str, cwd: &Path) -> Result<Vec<PatchSection>, EditError> {
    // omp validates every header row up to the first well-formed one before
    // splitting, so a malformed header anywhere above it is reported as such.
    for line in input.strip_prefix('\u{feff}').unwrap_or(input).lines() {
        if parse_header_line(line, cwd)?.is_some() {
            break;
        }
    }
    let stripped = strip_leading_blanks(input);
    let lines: Vec<&str> = stripped
        .split('\n')
        .map(|line| line.strip_suffix('\r').unwrap_or(line))
        .collect();
    let first = lines.first().copied().unwrap_or("");
    if parse_header_line(first, cwd)?.is_none() {
        if UNIFIED_HUNK_RE.is_match(first.trim_end()) {
            return Err(EditError::parse(
                "unified-diff hunk header (`@@ -N,M +N,M @@`) is not valid in hashline. File sections \
                 start with `[path#HASH]`; use `replace`, `delete`, or `insert` ops.",
            ));
        }
        let preview: String = first.chars().take(120).collect();
        return Err(EditError::parse(format!(
            "input must begin with \"[PATH#HASH]\" on the first non-blank line for anchored edits; \
             got: {}. Example: \"[src/foo.ts#{}]\" then edit ops.",
            json_quote(&preview),
            HL_FILE_HASH_EXAMPLES[0]
        )));
    }
    let mut sections = Vec::new();
    let mut current: Option<PatchSection> = None;
    let mut body = Vec::new();
    for line in lines {
        let clean = unbracket_envelope_markers(line.trim_end());
        match classify_line(clean, 0) {
            Token::EnvelopeEnd { .. } | Token::Abort { .. } => break,
            Token::EnvelopeBegin { .. } => continue,
            Token::Blank { .. }
            | Token::Header { .. }
            | Token::OpBlock { .. }
            | Token::PayloadLiteral { .. }
            | Token::Raw { .. } => {}
        }
        if clean.starts_with('[') {
            if let Some(header) = parse_header_line(clean, cwd)? {
                flush_section(&mut sections, &mut current, &mut body);
                current = Some(header);
                continue;
            }
        }
        body.push(line);
    }
    flush_section(&mut sections, &mut current, &mut body);
    Ok(sections)
}

fn flush_section(
    sections: &mut Vec<PatchSection>,
    current: &mut Option<PatchSection>,
    body: &mut Vec<&str>,
) {
    let Some(mut section) = current.take() else {
        body.clear();
        return;
    };
    if body.iter().any(|line| !line.trim().is_empty()) {
        section.diff = body.join("\n");
        sections.push(section);
    }
    body.clear();
}

fn merge_same_path_sections(sections: Vec<PatchSection>) -> Result<Vec<PatchSection>, EditError> {
    let mut result: Vec<PatchSection> = Vec::new();
    let mut positions = HashMap::<String, usize>::new();
    let mut previous: Option<String> = None;
    for section in sections {
        if let Some(&index) = positions.get(&section.path) {
            let existing = &mut result[index];
            if let (Some(first), Some(second)) = (&existing.file_hash, &section.file_hash) {
                if first != second {
                    return Err(EditError::parse(format!(
                        "Conflicting hashline snapshot tags for {}: #{first} and #{second}. Re-read \
                         the file and retry with one current header.",
                        section.path
                    )));
                }
            }
            if existing.file_hash.is_none() {
                existing.file_hash = section.file_hash;
            }
            if previous.as_deref() != Some(&section.path) {
                existing.interleaved = true;
            }
            existing.diff.push('\n');
            existing.diff.push_str(&section.diff);
            previous = Some(section.path);
            continue;
        }
        positions.insert(section.path.clone(), result.len());
        previous = Some(section.path.clone());
        result.push(section);
    }
    Ok(result)
}
