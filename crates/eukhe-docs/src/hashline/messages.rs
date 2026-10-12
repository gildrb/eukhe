//! Model-facing hashline errors and warnings (omp
//! `modes/hashline/messages.rs`). Models are trained on these strings: keep
//! them byte-identical to omp and change one only with a tool revision bump.

use std::collections::{BTreeSet, HashSet};

/// Number of hexadecimal characters in a snapshot tag.
pub(crate) const HL_FILE_HASH_LENGTH: usize = 4;
/// Representative snapshot tags used in diagnostics.
pub(crate) const HL_FILE_HASH_EXAMPLES: [&str; 3] = ["1A2B", "3C4D", "9F3E"];
const HL_FILE_PREFIX: &str = "[";
const HL_FILE_SUFFIX: &str = "]";
const HL_PAYLOAD_REPLACE: &str = "+";
const HL_PUT_KEYWORD: &str = "PUT";
const HL_CUT_KEYWORD: &str = "CUT";
const HL_FILE_HASH_SEP: &str = "#";
const HL_RANGE_SEP: &str = ".=";
const HL_LINE_BODY_SEP: &str = ":";

#[inline]
fn format_numbered_line(line_number: u32, line: &str) -> String {
    format!("{line_number}{HL_LINE_BODY_SEP}{line}")
}

/// Tiny JS-compatible `JSON.stringify(str)` that escapes `"`, `\`, and control
/// characters, emitting other UTF-8 characters as-is.
pub(crate) fn json_quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\x08' => out.push_str("\\b"),
            '\x0C' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => {
                const HEX: &[u8; 16] = b"0123456789abcdef";
                let code = c as usize;
                out.push_str("\\u00");
                out.push(char::from(HEX[code >> 4]));
                out.push(char::from(HEX[code & 0xf]));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Lines of context shown either side of a hash mismatch.
const MISMATCH_CONTEXT: u32 = 2;

/// Numbered `LINE:TEXT` rows around `anchor_lines` (±[`MISMATCH_CONTEXT`]),
/// `*`-marking anchors, `...` between non-adjacent runs. Out-of-range anchors
/// contribute no rows.
pub(crate) fn format_anchored_context<S: AsRef<str>>(
    anchor_lines: &[u32],
    file_lines: &[S],
) -> Vec<String> {
    let mut display_lines = BTreeSet::new();
    for &line in anchor_lines {
        if line < 1 || (line as usize) > file_lines.len() {
            continue;
        }
        let lo = line.saturating_sub(MISMATCH_CONTEXT).max(1);
        let hi = (line + MISMATCH_CONTEXT).min(file_lines.len() as u32);
        for line_num in lo..=hi {
            display_lines.insert(line_num);
        }
    }
    let anchor_set: HashSet<u32> = anchor_lines.iter().copied().collect();
    let mut rows = Vec::new();
    let mut previous: Option<u32> = None;
    for &line_num in &display_lines {
        if previous.is_some_and(|prev| line_num > prev + 1) {
            rows.push("...".to_string());
        }
        previous = Some(line_num);
        let marker = if anchor_set.contains(&line_num) {
            "*"
        } else {
            " "
        };
        let text = file_lines
            .get((line_num - 1) as usize)
            .map_or("", |s| s.as_ref());
        rows.push(format!("{marker}{}", format_numbered_line(line_num, text)));
    }
    rows
}

/// Concrete range operation rejected because its absolute end precedes its
/// start.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum AbsoluteRangeOp {
    Replace,
    Cut,
}

impl std::fmt::Display for AbsoluteRangeOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Replace => write!(f, "replace"),
            Self::Cut => write!(f, "cut"),
        }
    }
}

fn reg_suffix(register: Option<&str>) -> String {
    match register {
        Some(reg) => format!(" @{reg}"),
        None => String::new(),
    }
}

fn range_op_single(op: AbsoluteRangeOp, line: u32, register: Option<&str>) -> String {
    let suffix = reg_suffix(register);
    match op {
        AbsoluteRangeOp::Replace => {
            if register.is_some() {
                format!("{HL_PUT_KEYWORD} {line}{suffix}")
            } else {
                format!("{HL_PUT_KEYWORD} {line}:")
            }
        }
        AbsoluteRangeOp::Cut => format!("{HL_CUT_KEYWORD} {line}{suffix}"),
    }
}

fn range_op_range(op: AbsoluteRangeOp, start: u32, end: u32, register: Option<&str>) -> String {
    let suffix = reg_suffix(register);
    match op {
        AbsoluteRangeOp::Replace => {
            if register.is_some() {
                format!("{HL_PUT_KEYWORD} {start}{HL_RANGE_SEP}{end}{suffix}")
            } else {
                format!("{HL_PUT_KEYWORD} {start}{HL_RANGE_SEP}{end}:")
            }
        }
        AbsoluteRangeOp::Cut => format!("{HL_CUT_KEYWORD} {start}{HL_RANGE_SEP}{end}{suffix}"),
    }
}

fn block_form_at(op: AbsoluteRangeOp, line: u32, register: Option<&str>) -> String {
    let suffix = reg_suffix(register);
    match op {
        AbsoluteRangeOp::Replace => {
            if register.is_some() {
                format!("{HL_PUT_KEYWORD} {line}*{suffix}")
            } else {
                format!("{HL_PUT_KEYWORD} {line}*:")
            }
        }
        AbsoluteRangeOp::Cut => format!("{HL_CUT_KEYWORD} {line}*{suffix}"),
    }
}

/// Explain absolute range endpoints and provide safe, non-applying retry forms.
///
/// omp also names the syntactic block starting at `start` when tree-sitter
/// finds one; without grammars that sentence never applies.
pub(crate) fn invalid_absolute_range_message(
    patch_line: u32,
    start: u32,
    end: u32,
    op: AbsoluteRangeOp,
    register: Option<&str>,
) -> String {
    let single = range_op_single(op, start, register);
    let message = format!(
        "line {patch_line}: Invalid absolute range: start {start}, end {end}. The value after \
         `{HL_RANGE_SEP}` is an absolute source line, not a line count or replacement length. For \
         one line use `{single}`."
    );
    match start.checked_add(end).and_then(|sum| sum.checked_sub(1)) {
        Some(counted_end) if counted_end >= start => {
            let counted = range_op_range(op, start, counted_end, register);
            format!("{message} For {end} lines starting at {start}, use `{counted}`.")
        }
        Some(_) | None => message,
    }
}

/// Optional patch envelope start marker; silently consumed.
pub(crate) const BEGIN_PATCH_MARKER: &str = "*** Begin Patch";

/// Optional patch envelope end marker; terminates parsing.
pub(crate) const END_PATCH_MARKER: &str = "*** End Patch";

/// Truncation sentinel emitted by an agent loop mid-call. Ends parsing like
/// [`END_PATCH_MARKER`], without a warning.
pub(crate) const ABORT_MARKER: &str = "*** Abort";

/// Exact-range duplicate hunks were normalized to the final hunk.
pub(crate) const REPLACE_PAIR_COALESCED_WARNING: &str =
    "Multiple hunks targeted the same exact range; \
                                                  kept only the last. Issue one `PUT` or `CUT` \
                                                  hunk per range.";

/// Replacement body indentation was aligned from unchanged structural rows.
pub(crate) const REPLACEMENT_INDENT_AUTO_SHIFT_WARNING: &str =
    "Auto-indented a replacement body to match unchanged structural rows in its source range.";

/// Bare body rows auto-converted to literal `+` rows.
pub(crate) const BARE_BODY_AUTO_PIPED_WARNING: &str =
    "Auto-prefixed bare body row(s) with `+`. Body rows must be `+TEXT` literal lines.";

/// Top-level read-output rows recovered as single-line replacements.
pub(crate) const SNAPSHOT_ROWS_AUTO_PUT_WARNING: &str =
    "Recovered top-level `N:TEXT` snapshot row(s) as \
                                                  single-line `PUT N.=N:` replacements. Use \
                                                  explicit `PUT` headers for reliable edits.";

/// Two or more top-level `N:TEXT` read-output rows named the same source line.
///
/// Each recovered row lowers to a single-line `PUT N.=N:`, so the coalescer
/// would keep only the last and silently drop the others — reject and teach the
/// format instead.
pub(crate) fn repeated_snapshot_row_message(line: u32) -> String {
    format!(
        "two or more pasted `{line}:TEXT` read-output rows name line {line}. Such rows are \
         recovered as single-line `PUT {line}{HL_RANGE_SEP}{line}:` replacements, so repeating a \
         number would keep only the last row and drop the rest. Write the hunk explicitly: one `PUT \
         {line}{HL_RANGE_SEP}M:` header covering exactly the lines that change, followed by `+TEXT` \
         body rows holding their complete final content."
    )
}

/// A `+` body row whose text is itself a valid hunk header.
///
/// The op was written with the payload prefix, so it is inserted into the file
/// as literal text instead of executing. Warned rather than rejected: a literal
/// `CUT …` line is legitimate content in documentation and test fixtures.
pub(crate) fn literal_op_row_warning(line: u32, text: &str) -> String {
    format!(
        "line {line}: body row `{HL_PAYLOAD_REPLACE}{text}` is itself a valid hunk header, so it \
         was inserted into the file as literal text rather than executed. Ops are never \
         `{HL_PAYLOAD_REPLACE}`-prefixed — drop the `{HL_PAYLOAD_REPLACE}` to run it, and re-issue \
         if this line landed in the file by mistake."
    )
}

/// Bare range header recovered as an implicit replacement hunk.
pub(crate) const BARE_RANGE_AUTO_PUT_WARNING: &str =
    "Recovered a bare `N.=M:` header as `PUT N.=M:`. Prefix replacement ranges with `PUT`.";

/// Copied read-output elision rows were ignored rather than written as source.
pub(crate) const READ_METADATA_IGNORED_WARNING: &str =
    "Ignored copied read-output elision row(s). Re-read elided ranges before editing them.";

/// Empty span/block PUT recovered as a delete-only edit.
pub(crate) const EMPTY_PUT_AUTO_CUT_WARNING: &str =
    "Interpreted an empty `PUT` body as deletion. Use `CUT N.=M` or `CUT N*` for bodyless deletes.";

/// A bodyless CUT carried a harmless trailing colon.
pub(crate) const CUT_COLON_IGNORED_WARNING: &str =
    "Ignored a trailing `:` on bodyless `CUT`. Prefer `CUT N.=M` / `CUT N*` without a colon.";

/// Bare `-` body rows accepted as literal Markdown bullets.
///
/// Only emitted when the hunk is unambiguously a bullet list: every `-` row is
/// bullet-shaped (`- item`) and the body has no unified-diff `+new` counterpart
/// rows.
pub(crate) const MINUS_BULLET_AUTO_PIPED_WARNING: &str =
    "Auto-prefixed bare `- ` bullet row(s) as literal content. `-` rows never remove lines — the \
     range does that; always prefix literal body rows with `+`: `+- item`.";

/// Unified-diff old rows were discarded; explicit `+` rows are final content.
pub(crate) const DIFF_OLD_ROWS_IGNORED_WARNING: &str =
    "Ignored unified-diff `-old` row(s); the range \
                                                 already removes old content, so only `+new` rows \
                                                 were kept.";

/// Unified-diff-style `-` row in a hunk body.
pub(crate) const MINUS_ROW_REJECTED: &str =
    "`-` rows are not valid; the range already names the lines \
                                      being changed. For Markdown bullets or other literal `-` \
                                      lines, prefix the literal row with `+`: `+- item`.";

/// A block-anchored replace/cut could not resolve to a syntactic block,
/// followed by the [`format_anchored_context`] preview around the anchor.
/// `PUT >N*` never reaches this path; it lowers to `PUT >N`.
///
/// omp also suggests the next or enclosing block when tree-sitter finds one;
/// without grammars there is never one to suggest.
pub(crate) fn block_unresolved_message(
    line: u32,
    op: AbsoluteRangeOp,
    file_lines: &[&str],
    register: Option<&str>,
) -> String {
    let phrase = block_form_at(op, line, register);
    let fallback = match (op, register) {
        (AbsoluteRangeOp::Replace, Some(reg)) => {
            format!("{HL_PUT_KEYWORD} {line}{HL_RANGE_SEP}M @{reg}")
        }
        (AbsoluteRangeOp::Replace, None) => format!("{HL_PUT_KEYWORD} {line}{HL_RANGE_SEP}M:"),
        (AbsoluteRangeOp::Cut, Some(reg)) => {
            format!("{HL_CUT_KEYWORD} {line}{HL_RANGE_SEP}M @{reg}")
        }
        (AbsoluteRangeOp::Cut, None) => format!("{HL_CUT_KEYWORD} {line}{HL_RANGE_SEP}M"),
    };
    let mut message = format!(
        "`{phrase}` could not resolve a syntactic block beginning on line {line} (unsupported \
         language, blank/closer line, or parse error). Use `{fallback}` with explicit lines."
    );
    let context = format_anchored_context(&[line], file_lines);
    if !context.is_empty() {
        message.push_str("\n\n");
        message.push_str(&context.join("\n"));
    }
    message
}

fn closer_lowered_warning(block_form: &str, plain_form: &str) -> String {
    format!(
        "`{block_form}` anchors on a closing delimiter, so it was applied as plain `{plain_form}`. \
         Anchor on the line that OPENS the construct."
    )
}

fn unresolved_lowered_warning(block_form: &str, line: u32, plain_form: &str) -> String {
    format!(
        "`{block_form}` could not resolve a syntactic block on line {line}, so it was applied as \
         plain `{plain_form}`. Verify the landing line; anchor on a line that OPENS a construct."
    )
}

/// `PUT >N*:` anchored on a closing-delimiter line; applied as `PUT >N:`.
pub(crate) fn insert_after_block_closer_lowered_warning(line: u32) -> String {
    closer_lowered_warning(&format!("PUT >{line}*:"), &format!("PUT >{line}:"))
}

/// `PUT >N*:` anchor unresolvable; applied as `PUT >N:`.
pub(crate) fn insert_after_block_unresolved_lowered_warning(line: u32) -> String {
    unresolved_lowered_warning(&format!("PUT >{line}*:"), line, &format!("PUT >{line}:"))
}

/// Register `PUT >N*` anchored on a closing-delimiter line; applied as
/// `PUT >N`.
pub(crate) fn paste_after_block_closer_lowered_warning(line: u32) -> String {
    closer_lowered_warning(&format!("PUT >{line}*"), &format!("PUT >{line}"))
}

/// Register `PUT >N*` anchor unresolvable; applied as `PUT >N`.
pub(crate) fn paste_after_block_unresolved_lowered_warning(line: u32) -> String {
    unresolved_lowered_warning(&format!("PUT >{line}*"), line, &format!("PUT >{line}"))
}

/// Which boundary side an ambiguous echo appeared on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum BoundarySide {
    Leading,
    Trailing,
}

impl std::fmt::Display for BoundarySide {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Leading => write!(f, "leading"),
            Self::Trailing => write!(f, "trailing"),
        }
    }
}

/// A one-sided exact boundary echo cannot cover the selected range.
///
/// After the duplicated body rows are removed, applying or dropping it would
/// lose distinct range content, so the edit is rejected unless a
/// parse-restoring boundary combination proves another reading.
pub(crate) fn ambiguous_boundary_echo_message(
    start_line: u32,
    end_line: u32,
    side: BoundarySide,
    count: u32,
) -> String {
    let where_clause = match side {
        BoundarySide::Leading => {
            format!("opens by restating the {count} line(s) just above the range")
        }
        BoundarySide::Trailing => {
            format!("ends by restating the {count} line(s) just below the range")
        }
    };
    format!(
        "`PUT {start_line}{HL_RANGE_SEP}{end_line}:` rejected: the body {where_clause}, but is too \
         short to be the full final content of the selected range. Re-issue with the range covering \
         exactly the lines that change and the body as their complete final content."
    )
}

/// Exact-text boundary rows were removed because the remaining payload covers
/// the selected range and the same rows already survive immediately outside it.
pub(crate) fn textual_boundary_echo_warning(
    start_line: u32,
    leading: u32,
    trailing: u32,
) -> String {
    let mut parts = Vec::new();
    if leading > 0 {
        parts.push(format!("{leading} leading"));
    }
    if trailing > 0 {
        parts.push(format!("{trailing} trailing"));
    }
    let joined = parts.join(" and ");
    format!(
        "Auto-repaired a replacement boundary echo at line {start_line}: dropped {joined} body \
         line(s) already present outside the range. Issue the body as final content for the \
         selected range only."
    )
}

/// Internal invariant: `applyEdits` received an unresolved block edit;
/// `resolveBlockEdits` must run first.
pub(crate) const UNRESOLVED_BLOCK_INTERNAL: &str =
    "internal error: unresolved block edit reached the applier (resolveBlockEdits was not run).";

/// Internal invariant: clipboard edits must be concrete before application.
pub(crate) const UNRESOLVED_CLIPBOARD_INTERNAL: &str = "internal error: unresolved clipboard edit \
                                                 reached the applier (resolveClipboardEdits was \
                                                 not run).";

/// `REM` deletes the whole file and takes no body rows or line ops. Issue it
/// alone under the header.
pub(crate) const REM_TAKES_NO_BODY: &str =
    "`REM` deletes the whole file and takes no body rows or line \
                                     ops. Issue it alone under the header.";

/// `MV DEST` does not take body rows. Put line edits above the `MV` row; the
/// destination path follows `MV` on the same line.
pub(crate) const MOVE_TAKES_NO_BODY: &str =
    "`MV DEST` does not take body rows. Put line edits above the \
                                      `MV` row; the destination path follows `MV` on the same \
                                      line.";

/// `CUT` hunk received a body row.
pub(crate) const CUT_TAKES_NO_BODY: &str =
    "`CUT` deletes (and captures) the named lines and takes no \
                                     body rows. To write new content, use `PUT N.=M:` with \
                                     `+TEXT` rows.";

/// Register `PUT` header carried a `:`.
pub(crate) const COLON_ON_REGISTER_PUT: &str =
    "`PUT … @name` pastes the register and never takes `:` — \
                                         the colon promises body rows. Drop the colon (`PUT >40 \
                                         @name`), or drop `@name` and write `+TEXT` body rows.";

/// Register `PUT` hunk received a body row.
pub(crate) const REGISTER_PUT_TAKES_NO_BODY: &str =
    "A register `PUT` pastes captured lines and takes no \
                                              `+` body rows. To write literal text, drop the \
                                              `@name` and use `PUT …:` with body rows.";

/// Colonless `PUT` hunk received a body row.
pub(crate) const COLONLESS_PUT_TAKES_NO_BODY: &str =
    "`PUT` without `:` is clipboard-backed and takes no \
                                               body rows. Add `:` after the locator to write \
                                               literal content (`PUT >40:` then `+TEXT` rows).";

/// Colonless anonymous `PUT` on a span target.
pub(crate) const COLONLESS_SPAN_PUT: &str =
    "Colonless `PUT` is clipboard-backed, and span targets need \
                                      a named register (`PUT 5.=9 @name`); the anonymous register \
                                      pastes only at gaps (`PUT >40`). To write literal content, \
                                      add `:` and `+TEXT` body rows.";

/// Anonymous paste ran with an empty anonymous register.
pub(crate) const EMPTY_PASTE: &str =
    "Nothing to paste: no unlabeled `CUT` precedes this `PUT` in this \
                               call, and the anonymous register never carries across calls. Put \
                               `CUT N.=M` / `CUT N*` above it, or use named registers (`CUT … \
                               @name` → `PUT … @name`) for cross-call moves.";

/// Named paste read a register that holds nothing; a gap paste applies as
/// empty.
pub(crate) fn empty_register_paste_warning(name: &str, known: &[&str]) -> String {
    let base = format!(
        "`@{name}` was empty — no `CUT … @{name}` precedes this op in this call and no persisted \
         register has that name — so nothing was pasted."
    );
    if known.is_empty() {
        base
    } else {
        let available = known
            .iter()
            .map(|k| format!("`@{k}`"))
            .collect::<Vec<_>>()
            .join(", ");
        format!("{base} Available registers: {available}.")
    }
}

/// Named paste over a *span* read a register that holds nothing.
///
/// Pasting empty would delete the span, which the author never asked for —
/// almost always a mistyped or never-captured register name — so the edit is
/// rejected instead.
pub(crate) fn empty_register_span_paste_message(name: &str, known: &[&str]) -> String {
    let base = format!(
        "`@{name}` is empty — no `CUT … @{name}` precedes this op in this call and no persisted \
         register has that name — so pasting it over a range would delete those lines and write \
         nothing back. Capture the register first (`CUT … @{name}`), or use `CUT` if deleting the \
         range is what you meant."
    );
    if known.is_empty() {
        base
    } else {
        let available = known
            .iter()
            .map(|k| format!("`@{k}`"))
            .collect::<Vec<_>>()
            .join(", ");
        format!("{base} Available registers: {available}.")
    }
}

/// Unlabeled paste with two or more unlabeled cuts pending.
pub(crate) fn ambiguous_anonymous_paste_message(pending: &[&str]) -> String {
    let count = pending.len();
    let joined = pending.join(", ");
    format!(
        "{count} unlabeled `CUT`s are pending ({joined}) — an unlabeled paste cannot tell which one \
         you meant. Label the moves (`CUT … @name` → `PUT … @name`), or keep at most one unlabeled \
         `CUT` before each unlabeled paste."
    )
}

/// Clipboard ops in a same-path section merged across another file's section.
///
/// Same-path sections coalesce into their first occurrence, so an interleaved
/// layout would silently reorder the register sequence.
pub(crate) const CLIPBOARD_INTERLEAVED_SECTIONS: &str =
    "`CUT`/register-`PUT` ops cannot be used in a file whose sections are interleaved with another \
     file's: same-path sections merge into the first occurrence, which would reorder the register \
     sequence. Keep each file's ops under ONE `[path#TAG]` header.";

/// Gap `PUT` with `:` but no body.
pub(crate) const EMPTY_INSERT: &str =
    "`PUT <N:` / `PUT >N:` promises body rows and got none. Write \
                                `+TEXT` rows, or drop the `:` to paste a register (`PUT >N` = \
                                anonymous, `PUT >N @name` = named).";

/// `insert after` body indented shallower than the anchor: the landing slid
/// forward past trailing closer lines — the common "anchored on the last line
/// I read instead of after the block" mistake.
pub(crate) fn after_insert_landing_shift_warning(
    anchor_line: u32,
    landing_line: u32,
    crossed: u32,
) -> String {
    let s = if crossed == 1 { "" } else { "s" };
    format!(
        "PUT >{anchor_line}: body indented shallower than the anchor, so the landing moved past \
         {crossed} closing line{s} to after line {landing_line}. For the deeper position inside the \
         block, re-issue with the body indented to match."
    )
}

/// `Recovery`: an external write matched a cached snapshot.
pub(crate) const RECOVERY_EXTERNAL_WARNING: &str =
    "Recovered from a stale file hash using a previous \
                                             read snapshot (file changed externally between read \
                                             and edit).";

/// `Recovery`: a prior in-session edit advanced the hash.
pub(crate) const RECOVERY_SESSION_CHAIN_WARNING: &str =
    "Recovered from a stale file hash using an \
                                                  earlier in-session snapshot (a prior edit in \
                                                  this session advanced the hash).";

/// `Recovery`: stale anchors were relocated to unchanged live lines after
/// drift.
pub(crate) const RECOVERY_LINE_REMAP_WARNING: &str =
    "Recovered by remapping stale line anchors to \
                                               unchanged current lines (file changed since the \
                                               tagged read). Verify the diff matches your intent.";

/// `Recovery`: anchor remap failed, but the edit only touched regions the
/// other writer left unchanged (eukhe; omp rebases in its document server).
pub(crate) const RECOVERY_REBASE_WARNING: &str =
    "Recovered by rebasing your edit onto the current file (it changed since the tagged read; \
     your edit touched only regions that are unchanged since then). Verify the diff matches your \
     intent.";

/// `insert head:`/`insert tail:` applied despite a stale snapshot tag.
/// Head/tail position is content-independent, so drift is non-fatal: apply
/// onto live content and warn instead of hard-failing.
pub(crate) const HEADTAIL_DRIFT_WARNING: &str =
    "Applied the `PUT <1:`/`PUT >$:` edit despite a stale snapshot tag (file changed since your \
     read) — head/tail position is content-independent. Re-read if the drift was unexpected.";

/// Disk content after write differs from what was sent (e.g. IDE format on
/// save).
///
/// See `WriteResult.text` — most commonly an ACP-connected editor reformatting
/// the buffer on save (e.g. `format_on_save` with tab/space settings that don't
/// match the file). The recorded snapshot is re-keyed on the real, post-write
/// content so the next edit's tag validation matches reality instead of
/// silently drifting.
pub(crate) fn write_drift_warning(path: &str) -> String {
    format!(
        "{path}: the file on disk after this write differs from what was sent — the client \
         (editor/IDE) likely reformatted it on save (e.g. format-on-save, tab/space settings). The \
         returned snapshot reflects the actual file; re-read before further edits if the extra \
         changes were unexpected."
    )
}

/// Section omitted the mandatory snapshot tag. Shared by the apply
/// (`Patcher.prepare`) and preview/diff paths so both stay in lockstep.
pub(crate) fn missing_snapshot_tag_message(section_path: &str) -> String {
    format!(
        "Missing hashline snapshot tag for {section_path}; use \
         `{HL_FILE_PREFIX}{section_path}{HL_FILE_HASH_SEP}tag{HL_FILE_SUFFIX}` from your latest \
         read/search output. To create a new file, use the write tool."
    )
}

/// Section named a nonexistent path matching an earlier snapshot's name and
/// tag.
///
/// The model gave the bare filename (or wrong directory) for a file it just
/// read. The edit was rebound to that file's full path. Surfaced as a warning
/// so the model (and user) learn the corrected path and stop reusing the wrong
/// one.
pub(crate) fn path_recovered_from_tag_message(
    authored_path: &str,
    resolved_path: &str,
    tag: &str,
) -> String {
    format!(
        "Path \"{authored_path}\" does not exist; matched its filename and snapshot tag \
         {HL_FILE_HASH_SEP}{tag} to {resolved_path} (read earlier this session). Anchor future \
         edits on {HL_FILE_PREFIX}{resolved_path}{HL_FILE_HASH_SEP}TAG{HL_FILE_SUFFIX}."
    )
}

/// Compress a line list into a sorted `1-4, 7, 10-12` range string.
fn format_line_ranges(lines: &[u32]) -> String {
    let set: BTreeSet<u32> = lines.iter().copied().collect();
    if set.is_empty() {
        return String::new();
    }
    let sorted: Vec<u32> = set.into_iter().collect();
    let mut parts = Vec::new();
    let mut start = sorted[0];
    let mut prev = sorted[0];
    for &current in &sorted[1..] {
        if current == prev + 1 {
            prev = current;
            continue;
        }
        if start == prev {
            parts.push(format!("{start}"));
        } else {
            parts.push(format!("{start}-{prev}"));
        }
        start = current;
        prev = current;
    }
    if start == prev {
        parts.push(format!("{start}"));
    } else {
        parts.push(format!("{start}-{prev}"));
    }
    parts.join(", ")
}

/// One anchored line whose actual content is being surfaced in an error
/// message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RevealedLine {
    pub(crate) line: u32,
    pub(crate) text: String,
}

/// Content preview handed to [`unseen_lines_message`].
///
/// `lines` are the unseen anchor lines whose actual file content we surface
/// inline (from the tagged snapshot the caller matched). `truncated` = true
/// means the anchor range exceeded the inline reveal cap; the caller only
/// revealed a prefix and the remaining unseen lines still require a range
/// re-read.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct UnseenLinesReveal {
    pub(crate) lines: Vec<RevealedLine>,
    pub(crate) truncated: bool,
}

/// Edit referenced lines never displayed by the cited tag's read.
///
/// Editing lines not read (partial range or collapsed summary) mangles files.
/// When `reveal.lines` is non-empty, the caller has already inlined the actual
/// file content at those lines and merged them into the snapshot's seen-line
/// set, so the message points the model at a straight retry with the same
/// `[path#tag]` header; when the reveal is empty or truncated, the message
/// falls back to instructing a range re-read.
pub(crate) fn unseen_lines_message(
    section_path: &str,
    unseen_lines: &[u32],
    tag: &str,
    reveal: &UnseenLinesReveal,
) -> String {
    let ranges = format_line_ranges(unseen_lines);
    let selector = ranges.replace(", ", ",");
    let header = format!(
        "This edit anchors to lines {ranges} of {section_path} that \
         {HL_FILE_PREFIX}{section_path}{HL_FILE_HASH_SEP}{tag}{HL_FILE_SUFFIX} never displayed (it \
         showed a partial range, a search hit, or a folded summary)."
    );
    if reveal.lines.is_empty() {
        return format!(
            "{header} Re-read them in full first with a ranged read like `{section_path}:{selector}` \
             — it skips summarization and mints a fresh tag (a plain re-read just re-folds them) — \
             then re-issue the edit."
        );
    }
    let preview = reveal
        .lines
        .iter()
        .map(|r| format!("  {}", format_numbered_line(r.line, &r.text)))
        .collect::<Vec<_>>()
        .join("\n");
    if reveal.truncated {
        return format!(
            "{header} Preview of the actual file content at the first {} unseen \
             line(s):\n{preview}\nThe range exceeds the inline preview cap — re-read the remainder \
             with `{section_path}:{selector}` before re-issuing the edit.",
            reveal.lines.len()
        );
    }
    format!(
        "{header} Actual file content at those lines:\n{preview}\nVerify the content matches what \
         you intend to touch, then re-issue the edit with the same \
         {HL_FILE_PREFIX}path{HL_FILE_HASH_SEP}tag{HL_FILE_SUFFIX} header — a straight retry now \
         succeeds without a re-read. If the content does NOT match, fix your line numbers."
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_anchored_context() {
        let lines = [
            "alpha", "bravo", "charlie", "delta", "echo", "foxtrot", "golf", "hotel", "india",
            "juliet",
        ];
        // Anchors at line 2 and 8 with a gap between 4 and 6.
        let context = format_anchored_context(&[2, 8], &lines);
        assert_eq!(
            context,
            vec![
                " 1:alpha",
                "*2:bravo",
                " 3:charlie",
                " 4:delta",
                "...",
                " 6:foxtrot",
                " 7:golf",
                "*8:hotel",
                " 9:india",
                " 10:juliet",
            ]
        );

        // Out-of-range anchor ignored.
        let context_oor = format_anchored_context(&[999], &lines);
        assert!(context_oor.is_empty());
    }

    #[test]
    fn test_invalid_absolute_range_message() {
        let msg = invalid_absolute_range_message(12, 5, 3, AbsoluteRangeOp::Replace, None);
        assert_eq!(
            msg,
            "line 12: Invalid absolute range: start 5, end 3. The value after `.=` is an absolute \
             source line, not a line count or replacement length. For one line use `PUT 5:`. For 3 \
             lines starting at 5, use `PUT 5.=7:`."
        );

        // Cut with register and no block
        let msg_cut = invalid_absolute_range_message(10, 4, 1, AbsoluteRangeOp::Cut, Some("clip"));
        assert_eq!(
            msg_cut,
            "line 10: Invalid absolute range: start 4, end 1. The value after `.=` is an absolute \
             source line, not a line count or replacement length. For one line use `CUT 4 @clip`. \
             For 1 lines starting at 4, use `CUT 4.=4 @clip`."
        );
    }

    #[test]
    fn test_empty_register_paste_warning() {
        // 0 known registers
        let msg_empty = empty_register_paste_warning("temp", &[]);
        assert_eq!(
            msg_empty,
            "`@temp` was empty — no `CUT … @temp` precedes this op in this call and no persisted \
             register has that name — so nothing was pasted."
        );

        // N known registers
        let msg_known = empty_register_paste_warning("temp", &["foo", "bar"]);
        assert_eq!(
            msg_known,
            "`@temp` was empty — no `CUT … @temp` precedes this op in this call and no persisted \
             register has that name — so nothing was pasted. Available registers: `@foo`, `@bar`."
        );
    }

    #[test]
    fn test_unseen_lines_message() {
        // Empty reveal
        let msg_empty = unseen_lines_message(
            "src/foo.ts",
            &[5, 6, 7, 10],
            "AB12",
            &UnseenLinesReveal::default(),
        );
        assert_eq!(
            msg_empty,
            "This edit anchors to lines 5-7, 10 of src/foo.ts that [src/foo.ts#AB12] never displayed \
             (it showed a partial range, a search hit, or a folded summary). Re-read them in full \
             first with a ranged read like `src/foo.ts:5-7,10` — it skips summarization and mints a \
             fresh tag (a plain re-read just re-folds them) — then re-issue the edit."
        );

        // Non-empty reveal, not truncated
        let reveal = UnseenLinesReveal {
            lines: vec![RevealedLine {
                line: 5,
                text: "let x = 1;".to_string(),
            }],
            truncated: false,
        };
        let msg_reveal = unseen_lines_message("src/foo.ts", &[5], "AB12", &reveal);
        assert_eq!(
            msg_reveal,
            "This edit anchors to lines 5 of src/foo.ts that [src/foo.ts#AB12] never displayed (it \
             showed a partial range, a search hit, or a folded summary). Actual file content at \
             those lines:\n  5:let x = 1;\nVerify the content matches what you intend to touch, then \
             re-issue the edit with the same [path#tag] header — a straight retry now succeeds \
             without a re-read. If the content does NOT match, fix your line numbers."
        );

        // Truncated reveal
        let reveal_trunc = UnseenLinesReveal {
            lines: vec![RevealedLine {
                line: 5,
                text: "let x = 1;".to_string(),
            }],
            truncated: true,
        };
        let msg_trunc = unseen_lines_message("src/foo.ts", &[5, 6], "AB12", &reveal_trunc);
        assert_eq!(
            msg_trunc,
            "This edit anchors to lines 5-6 of src/foo.ts that [src/foo.ts#AB12] never displayed (it \
             showed a partial range, a search hit, or a folded summary). Preview of the actual file \
             content at the first 1 unseen line(s):\n  5:let x = 1;\nThe range exceeds the inline \
             preview cap — re-read the remainder with `src/foo.ts:5-6` before re-issuing the edit."
        );
    }

    #[test]
    fn test_boundary_warnings_and_json_quote() {
        assert_eq!(
            textual_boundary_echo_warning(10, 1, 2),
            "Auto-repaired a replacement boundary echo at line 10: dropped 1 leading and 2 trailing \
             body line(s) already present outside the range. Issue the body as final content for the \
             selected range only."
        );
        assert_eq!(
            json_quote("hello \"world\"\n\t\\"),
            "\"hello \\\"world\\\"\\n\\t\\\\\""
        );
    }
}
