//! Read/search line prefixes copied into payloads (omp
//! `modes/hashline/prefixes.rs`).

use std::sync::LazyLock;

use regex::Regex;

static HL_PREFIX_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^\s*(?:(?:>>>|>>)\s*)?(?:[+*-]\s*)?\d+[:|]").expect("valid regex")
});
static READ_RANGE_ELISION_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^\s*[1-9]\d*\s*-\s*[1-9]\d*:.*(?:…|\.\.\.).*$").expect("valid regex")
});
static READ_SINGLE_ELISION_RE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^\s*(?:…|\.\.\.)\s*$").expect("valid regex"));

/// Whether a row is display-only elision metadata emitted by `read`.
pub(crate) fn is_read_metadata_line(line: &str) -> bool {
    READ_RANGE_ELISION_RE.is_match(line) || READ_SINGLE_ELISION_RE.is_match(line)
}

/// Strip at most one leading read/search line-number prefix.
pub(crate) fn strip_one_leading_hashline_prefix(line: &str) -> String {
    HL_PREFIX_RE.replace(line, "").into_owned()
}
