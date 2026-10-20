//! The error every document operation returns.
//!
//! The `Display` output of each variant is the model-facing message: the
//! teaching contract ported from omp. Models are trained on these strings;
//! change one only with a tool revision bump.

use std::path::PathBuf;

/// Failure raised while parsing, locating, staging, or writing an edit.
#[derive(Debug, thiserror::Error)]
pub enum EditError {
    /// The wire payload could not be parsed. `line` is the 1-indexed payload
    /// line when the parser knows it.
    #[error("{message}")]
    Parse {
        /// Message.
        message: String,
        /// Line.
        line: Option<u32>,
    },
    /// The payload parsed but could not be applied (missing file, overlap,
    /// invalid op, auto-generated target, no-op, …).
    #[error("{0}")]
    Apply(String),
    /// A search anchor could not be located in the target text.
    #[error("{0}")]
    Match(String),
    /// The host's gate refused a write (the path policy, or the user).
    #[error("{0}")]
    Refused(String),
    /// Filesystem failure reading or writing a target; the message names
    /// the path, so a payload of many files shows which one failed.
    #[error("{display}: {source}")]
    Io {
        /// The path as the model wrote it.
        display: String,
        /// The absolute path.
        path: PathBuf,
        #[source]
        /// Source.
        source: std::io::Error,
    },
}

impl EditError {
    /// Parse failure without a line number.
    pub fn parse(message: impl Into<String>) -> Self {
        Self::Parse {
            message: message.into(),
            line: None,
        }
    }

    /// Parse failure at a known payload line.
    pub fn parse_at(message: impl Into<String>, line: u32) -> Self {
        Self::Parse {
            message: message.into(),
            line: Some(line),
        }
    }

    /// Apply failure carrying a preformatted message.
    pub fn apply(message: impl Into<String>) -> Self {
        Self::Apply(message.into())
    }

    /// Match failure carrying a preformatted message.
    pub fn matched(message: impl Into<String>) -> Self {
        Self::Match(message.into())
    }

    /// Whether this is `File not found` (ENOENT) for the given path.
    #[must_use]
    pub fn is_not_found(&self) -> bool {
        matches!(self, Self::Io { source, .. } if source.kind() == std::io::ErrorKind::NotFound)
    }
}

/// Convenience alias used throughout the crate.
pub type EditResult<T> = Result<T, EditError>;
