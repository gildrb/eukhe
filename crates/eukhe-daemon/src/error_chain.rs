//! The wire text of an error with its causes: the error, then each source
//! in turn, joined by `": "` (the text `anyhow`'s `{:#}` renders). Typed
//! errors keep their sources; a response renders the chain once.

use std::fmt;

/// Display of `error` followed by every source of it, `": "`-joined.
pub(crate) struct ErrorChain<'a>(pub(crate) &'a (dyn std::error::Error + 'static));

impl fmt::Display for ErrorChain<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)?;
        let mut source = self.0.source();
        while let Some(cause) = source {
            write!(f, ": {cause}")?;
            source = cause.source();
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::ErrorChain;

    #[derive(Debug, thiserror::Error)]
    #[error("outer")]
    struct Outer(#[source] std::io::Error);

    #[test]
    fn renders_like_anyhow_alternate() {
        let error = Outer(std::io::Error::other("inner"));
        let expected = format!(
            "{:#}",
            anyhow::Error::new(Outer(std::io::Error::other("inner")))
        );
        assert_eq!(ErrorChain(&error).to_string(), expected);
    }
}
