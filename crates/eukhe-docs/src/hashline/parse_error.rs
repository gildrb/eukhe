//! Why a hashline section body did not parse. The `Display` of each
//! variant is the model-facing teaching text ported from omp; change one
//! only with a tool revision bump.

use super::messages::{
    invalid_absolute_range_message, json_quote, repeated_snapshot_row_message, AbsoluteRangeOp,
    COLONLESS_PUT_TAKES_NO_BODY, COLONLESS_SPAN_PUT, COLON_ON_REGISTER_PUT, CUT_TAKES_NO_BODY,
    EMPTY_INSERT, MINUS_ROW_REJECTED, MOVE_TAKES_NO_BODY, REGISTER_PUT_TAKES_NO_BODY,
    REM_TAKES_NO_BODY,
};

/// A hashline section body that did not parse.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error(transparent)]
pub struct HashlineParseError(#[from] pub(crate) ParseFailure);

/// The failures of [`HashlineParseError`].
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum ParseFailure {
    /// The row at payload `line` broke the grammar.
    #[error("line {line}: {fault}")]
    At { line: u32, fault: Fault },
    /// A range whose absolute end precedes its start.
    #[error(
        "{}",
        invalid_absolute_range_message(*line, *start, *end, *op, register.as_deref())
    )]
    InvertedRange {
        line: u32,
        start: u32,
        end: u32,
        op: AbsoluteRangeOp,
        register: Option<String>,
    },
    /// `REM` together with line ops in one section.
    #[error("`REM` deletes the whole file and cannot be combined with line ops.")]
    RemWithLineOps,
}

/// What a row did wrong.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum Fault {
    #[error("{}", COLON_ON_REGISTER_PUT)]
    ColonOnRegisterPut,
    #[error("{}", MOVE_TAKES_NO_BODY)]
    MoveTakesNoBody,
    #[error("{}", REM_TAKES_NO_BODY)]
    RemTakesNoBody,
    #[error("{}", CUT_TAKES_NO_BODY)]
    CutTakesNoBody,
    #[error("{}", REGISTER_PUT_TAKES_NO_BODY)]
    RegisterPutTakesNoBody,
    #[error("{}", COLONLESS_PUT_TAKES_NO_BODY)]
    ColonlessPutTakesNoBody,
    #[error("{}", COLONLESS_SPAN_PUT)]
    ColonlessSpanPut,
    #[error("{}", EMPTY_INSERT)]
    EmptyInsert,
    #[error("{}", MINUS_ROW_REJECTED)]
    MinusRow,
    #[error("only one file-level op (`REM` or `MV`) per section. Merge them under one header.")]
    SecondFileOp,
    /// A `+` row before any header; `text` is the row without its `+`.
    #[error("payload line has no preceding hunk header. Got {}.", json_quote(&format!("+{text}")))]
    OrphanLiteral { text: String },
    /// A bare row before any header.
    #[error(
        "payload line has no preceding hunk header. Use `PUT N.=M:`, `CUT N.=M`, or `PUT \
         <N:`/`PUT >N:` above the body. Got {}.",
        json_quote(text)
    )]
    OrphanRow { text: String },
    /// Two pasted `N:TEXT` read rows name the same source line.
    #[error("{}", repeated_snapshot_row_message(*line))]
    RepeatedSnapshotRow { line: u32 },
    /// A hunk whose lines another hunk already targets; `prior` is that
    /// hunk's header line when one hunk holds them.
    #[error(
        "anchor line {first} is already targeted by another hunk on line {}. Issue ONE hunk per \
         range; payload is only the final desired content, never a before/after pair.",
        prior.map_or_else(|| "an earlier line".to_owned(), |line| line.to_string())
    )]
    Overlap { first: u32, prior: Option<u32> },
    /// A range past the expansion limit.
    #[error("{op} range spans {span} lines; the maximum is {max}. Split it into smaller hunks.")]
    RangeTooLong {
        op: AbsoluteRangeOp,
        span: u32,
        max: u32,
    },
    /// An `apply_patch` file sentinel; `preview` is the clipped row.
    #[error(
        "apply_patch sentinel {} is not valid in hashline. File sections start with `[path#HASH]` \
         (no `Update File:` / `Add File:` keyword). Use `PUT N.=M:`, `CUT N.=M`, or `PUT \
         <N:`/`PUT >N:` ops.",
        json_quote(preview)
    )]
    ApplyPatchSentinel { preview: String },
    #[error(
        "unified-diff hunk header (`@@ -N,M +N,M @@`) is not valid in hashline. Use `PUT N.=M:`, \
         `CUT N.=M`, or `PUT <N:`/`PUT >N:` ops."
    )]
    UnifiedHunkHeader,
    /// An `@@`-bracketed header; `preview` is the clipped row.
    #[error(
        "`@@`-bracketed hunk header {} is not valid in hashline. Drop the `@@ ... @@` brackets and \
         write a header such as `PUT N.=M:`.",
        json_quote(preview)
    )]
    BracketedHunkHeader { preview: String },
    /// A row holding one bare line number.
    #[error(
        "hunk headers need a verb and both endpoints. Use `PUT {line}.={line}:` to replace, or \
         `CUT {line}.={line}` to delete."
    )]
    BareLineNumber { line: String },
    /// A row holding two bare numbers.
    #[error(
        "bare range hunk header {} is not valid. Hunk headers need a verb: use `PUT N.=M:` or `CUT \
         N.=M`.",
        json_quote(text)
    )]
    BareRange { text: String },
}
