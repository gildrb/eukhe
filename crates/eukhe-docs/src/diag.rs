//! Structured notices kept outside the data: `<diag severity="info"
//! kind="pagination" continuation=":401" omitted="1600 lines">1600 lines
//! remain in src/a.rs.</diag>` (omp's `Diag` projection).

use std::fmt;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Severity {
    Info,
    Warn,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DiagKind {
    /// More lines follow the shown window.
    Pagination,
    /// A requested line or range lies past the end.
    RangeOutOfBounds,
    /// A result list hit its limit.
    Truncated,
}

/// One notice.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diag {
    pub severity: Severity,
    pub kind: DiagKind,
    pub message: String,
    /// The selector or argument that continues the read (`:401`).
    pub continuation: Option<String>,
    /// Lines left out.
    pub omitted_lines: Option<usize>,
}

impl Diag {
    #[must_use]
    pub fn info(kind: DiagKind, message: String) -> Self {
        Self {
            severity: Severity::Info,
            kind,
            message,
            continuation: None,
            omitted_lines: None,
        }
    }

    #[must_use]
    pub fn warn(kind: DiagKind, message: String) -> Self {
        Self {
            severity: Severity::Warn,
            ..Self::info(kind, message)
        }
    }

    #[must_use]
    pub fn continuation(self, continuation: String) -> Self {
        Self {
            continuation: Some(continuation),
            ..self
        }
    }

    #[must_use]
    pub fn omitted_lines(self, lines: usize) -> Self {
        Self {
            omitted_lines: Some(lines),
            ..self
        }
    }
}

impl Severity {
    fn as_str(self) -> &'static str {
        match self {
            Self::Info => "info",
            Self::Warn => "warn",
        }
    }
}

impl DiagKind {
    fn as_str(self) -> &'static str {
        match self {
            Self::Pagination => "pagination",
            Self::RangeOutOfBounds => "range_out_of_bounds",
            Self::Truncated => "truncated",
        }
    }
}

impl fmt::Display for Diag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "<diag severity=\"{}\" kind=\"{}\"",
            self.severity.as_str(),
            self.kind.as_str()
        )?;
        if let Some(continuation) = &self.continuation {
            write!(f, " continuation=\"{continuation}\"")?;
        }
        if let Some(lines) = self.omitted_lines {
            write!(f, " omitted=\"{lines} lines\"")?;
        }
        write!(f, ">{}</diag>", self.message)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn renders_attributes_in_order() {
        let diag = Diag::info(DiagKind::Pagination, "3 lines remain in a.rs.".to_owned())
            .continuation(":5".to_owned())
            .omitted_lines(3);
        assert_eq!(
            diag.to_string(),
            "<diag severity=\"info\" kind=\"pagination\" continuation=\":5\" omitted=\"3 lines\">3 lines remain in a.rs.</diag>"
        );
    }
}
