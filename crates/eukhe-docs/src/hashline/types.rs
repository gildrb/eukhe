//! Data shared by the hashline tokenizer, parser, applier, and patcher
//! (omp `modes/hashline/types.rs`). Nothing here touches a filesystem.

/// A 1-indexed line anchor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Anchor {
    pub(crate) line: u32,
}

/// Where an insert lands relative to existing content.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Cursor {
    Bof,
    Eof,
    BeforeAnchor(Anchor),
    AfterAnchor(Anchor),
}

/// A parsed `A.=B` inclusive line range.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ParsedRange {
    pub(crate) start: Anchor,
    pub(crate) end: Anchor,
}

/// Where a paste lands: an insertion gap, or a span it replaces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PasteTarget {
    Gap { cursor: Cursor },
    Span { range: ParsedRange },
}

/// One low-level edit produced by the parser and consumed by the applier.
/// Multi-line replacements decompose to one `Insert` per replacement line
/// plus one `Delete` per consumed line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Edit {
    Insert {
        cursor: Cursor,
        text: String,
        /// 1-indexed payload line this edit came from (for messages).
        line_num: u32,
        /// Position in the section's op list.
        index: u32,
        /// Replacement-payload insert (vs. literal insertion).
        replacement: bool,
    },
    Delete {
        anchor: Anchor,
        line_num: u32,
        index: u32,
    },
    /// Clipboard cut (`CUT N.=M @r`); captures range lines during the
    /// clipboard pre-pass and lowers to per-line deletes.
    Cut {
        range: ParsedRange,
        register: Option<String>,
        line_num: u32,
        index: u32,
    },
    /// Clipboard insertion or replacement (`PUT <N @r` / `PUT >N @r` /
    /// `PUT N.=M @r` or the anonymous equivalents).
    Paste {
        at: PasteTarget,
        register: Option<String>,
        line_num: u32,
        index: u32,
    },
    /// Block-locator edit (`PUT N*:`, `PUT >N*:`, `CUT N*`, register forms).
    /// eukhe has no block resolver, so staging rejects it.
    Block { anchor: Anchor, line_num: u32 },
}

impl Edit {
    /// Payload line number the edit was parsed from.
    pub(crate) const fn line_num(&self) -> u32 {
        match self {
            Self::Insert { line_num, .. }
            | Self::Delete { line_num, .. }
            | Self::Cut { line_num, .. }
            | Self::Paste { line_num, .. }
            | Self::Block { line_num, .. } => *line_num,
        }
    }
}

/// File-level operation parsed from a section body (`REM` / `MV`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FileOp {
    Rem,
    Move { dest: String },
}

/// Whether an apply made a new change, or found the change on disk already.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum Landing {
    /// The text is the result of this apply.
    #[default]
    Fresh,
    /// The section was applied before (a retry with the old tag): the text
    /// is the live text, unchanged.
    Already,
}

/// Result of applying parsed edits to a text body.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ApplyResult {
    pub(crate) text: String,
    /// 1-indexed first changed line; `None` for a no-op apply.
    pub(crate) first_changed_line: Option<u32>,
    pub(crate) warnings: Vec<String>,
    /// For each line of `text` (split on `\n`): the 0-based index of the
    /// input line it came from, or `None` for a new or replaced line.
    pub(crate) origins: Vec<Option<usize>>,
    pub(crate) landing: Landing,
}
