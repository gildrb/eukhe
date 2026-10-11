//! The user-facing text of a failed auth HTTP exchange: the bounded
//! response text an endpoint answered (trimmed to one line a login panel
//! can show) and a transport failure with its cause chain.

/// The longest body excerpt an error carries (characters).
const MAX_SNIPPET_CHARS: usize = 300;

/// The response body as one bounded line: whitespace runs collapse to a
/// single space, the text is cut at [`MAX_SNIPPET_CHARS`] with a `...`
/// marker, and an empty body reads `(empty body)`.
#[must_use]
pub fn response_snippet(body: &str) -> String {
    let mut words = body.split_whitespace();
    let Some(first) = words.next() else {
        return "(empty body)".to_string();
    };
    let mut line = first.to_string();
    for word in words {
        line.push(' ');
        line.push_str(word);
    }
    match line.char_indices().nth(MAX_SNIPPET_CHARS) {
        Some((cut, _)) => format!("{}...", &line[..cut]),
        None => line,
    }
}

/// A transport failure with its cause chain (TS `formatErrorDetails`
/// appends `cause=`): reqwest's own message names only the URL, the
/// chain carries the reason (DNS, TLS, proxy, refused connect).
#[must_use]
pub fn transport_failure(error: &reqwest::Error) -> String {
    use std::fmt::Write as _;
    let mut message = error.to_string();
    let mut source = std::error::Error::source(error);
    while let Some(cause) = source {
        // Writing into a String cannot fail.
        let _ = write!(message, "; cause={cause}");
        source = cause.source();
    }
    message
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_snippet_is_one_bounded_line() {
        assert_eq!(response_snippet("  no\n grant \t here "), "no grant here");
        assert_eq!(response_snippet(" \n "), "(empty body)");
        let long = "x".repeat(MAX_SNIPPET_CHARS + 50);
        assert_eq!(
            response_snippet(&long),
            format!("{}...", "x".repeat(MAX_SNIPPET_CHARS))
        );
        let exact = "y".repeat(MAX_SNIPPET_CHARS);
        assert_eq!(response_snippet(&exact), exact);
    }
}
