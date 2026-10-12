//! Structured notices attached to a search result: pagination, limits,
//! skipped inputs. Rendered as omp's `<diag>` line, outside the result data.
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
        }
    }
}

/// Unit of content counted by [`Omitted`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unit {
    /// Files.
    Files,
}

impl Unit {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Files => "files",
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
