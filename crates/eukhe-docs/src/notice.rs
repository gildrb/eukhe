//! Structured notices attached to a read or search result: pagination,
//! limits, skipped inputs. Rendered as omp's `<diag>` line, outside the result data.
//!
//! Ported from omp `crates/tools/src/diag.rs` and the `<diag>` projection in
//! `crates/session/src/projection.rs`.

use std::fmt;

/// How much a notice matters.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Severity {
    /// Expected and complete; informs the next call.
    Info,
    /// Something was skipped or cut.
    Warn,
}

impl Severity {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Info => "info",
            Self::Warn => "warn",
        }
    }
}

/// What a notice reports.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NoticeKind {
    /// The result is one page of a larger set; `continuation` fetches the next.
    Pagination,
    /// A requested offset lies beyond the end of the result.
    RangeOutOfBounds,
    /// A fixed result cap was hit; `omitted` counts what was dropped.
    LimitReached,
    /// Work stopped at a deadline with partial results.
    Timeout,
    /// Requested paths did not exist and were skipped.
    MissingPaths,
    /// Inputs were skipped because the tool cannot process them.
    Skipped,
    /// Only a prefix of the input was examined.
    PartialScan,
    /// A shown file has no tag, so `edit` cannot change it.
    NotEditable,
}

impl NoticeKind {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Pagination => "pagination",
            Self::RangeOutOfBounds => "range_out_of_bounds",
            Self::LimitReached => "limit_reached",
            Self::Timeout => "timeout",
            Self::MissingPaths => "missing_paths",
            Self::Skipped => "skipped",
            Self::PartialScan => "partial_scan",
            Self::NotEditable => "not_editable",
        }
    }
}

/// Unit of content counted by [`Omitted`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unit {
    /// Files.
    Files,
    /// Lines.
    Lines,
    /// Directory entries.
    Entries,
}

impl Unit {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Files => "files",
            Self::Lines => "lines",
            Self::Entries => "entries",
        }
    }
}

/// Count of content left out of the result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Omitted {
    /// Number of units not shown.
    pub count: u64,
    /// What was counted.
    pub unit: Unit,
}

/// One notice: a sentence plus the typed facts a caller acts on.
///
/// `Display` is the model-facing line:
/// `<diag severity="info" kind="pagination" continuation="skip=20" omitted="3 files">files 1-20 of 23</diag>`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Notice {
    /// How much the notice matters.
    pub severity: Severity,
    /// What the notice reports.
    pub kind: NoticeKind,
    /// The sentence shown to the model.
    pub text: String,
    /// The argument that continues the result, such as `skip=20`.
    pub continuation: Option<String>,
    /// Content left out.
    pub omitted: Option<Omitted>,
}

impl Notice {
    pub(crate) fn info(kind: NoticeKind, text: String) -> Self {
        Self {
            severity: Severity::Info,
            kind,
            text,
            continuation: None,
            omitted: None,
        }
    }

    pub(crate) fn warn(kind: NoticeKind, text: String) -> Self {
        Self {
            severity: Severity::Warn,
            ..Self::info(kind, text)
        }
    }
}

/// Examples a notice names for one class of skipped inputs.
pub(crate) const NOTICE_EXAMPLES: usize = 3;

/// One class of skipped or cut inputs: how many there were and the first
/// few of them, for one notice.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Tally {
    /// Inputs in the class.
    pub(crate) count: u64,
    /// The first [`NOTICE_EXAMPLES`] of them, in the order found.
    pub(crate) examples: Vec<String>,
}

impl Tally {
    /// Count one more input; `example` names it while there is room.
    pub(crate) fn add(&mut self, example: impl FnOnce() -> String) {
        self.count = self.count.saturating_add(1);
        if self.examples.len() < NOTICE_EXAMPLES {
            self.examples.push(example());
        }
    }

    /// Add every input of `other` to this class.
    pub(crate) fn absorb(&mut self, other: Self) {
        self.count = self.count.saturating_add(other.count);
        let room = NOTICE_EXAMPLES.saturating_sub(self.examples.len());
        self.examples.extend(other.examples.into_iter().take(room));
    }

    /// `{count} {what}: a, b, c` (with `, ...` when more were counted than
    /// named); `None` when the class is empty.
    pub(crate) fn describe(&self, what: &str) -> Option<String> {
        if self.count == 0 {
            return None;
        }
        let named = u64::try_from(self.examples.len()).unwrap_or(u64::MAX);
        let more = if self.count > named { ", ..." } else { "" };
        Some(format!(
            "{} {what}: {}{more}",
            self.count,
            self.examples.join(", ")
        ))
    }
}

impl fmt::Display for Notice {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "<diag severity=\"{}\" kind=\"{}\"",
            self.severity.as_str(),
            self.kind.as_str()
        )?;
        if let Some(continuation) = &self.continuation {
            write!(formatter, " continuation=\"{continuation}\"")?;
        }
        if let Some(omitted) = self.omitted {
            write!(
                formatter,
                " omitted=\"{} {}\"",
                omitted.count,
                omitted.unit.as_str()
            )?;
        }
        write!(formatter, ">{}</diag>", self.text)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn renders_the_omp_diag_shape() {
        let notice = Notice {
            continuation: Some("skip=20".to_owned()),
            omitted: Some(Omitted {
                count: 3,
                unit: Unit::Files,
            }),
            ..Notice::info(NoticeKind::Pagination, "files 1-20 of 23".to_owned())
        };
        assert_eq!(
            notice.to_string(),
            r#"<diag severity="info" kind="pagination" continuation="skip=20" omitted="3 files">files 1-20 of 23</diag>"#
        );
        assert_eq!(
            Notice::warn(NoticeKind::MissingPaths, "gone".to_owned()).to_string(),
            r#"<diag severity="warn" kind="missing_paths">gone</diag>"#
        );
    }
}
