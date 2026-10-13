//! Read selectors: `path:50-120`, `path:raw`, `path:raw:10-20` (port of omp
//! `read/selector.rs`, the file subset).

/// One inclusive, one-based line range.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LineRange {
    pub start_line: u64,
    /// `None` extends to the end of the file.
    pub end_line: Option<u64>,
}

/// A parsed read selector.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Selector {
    /// No selector: the whole file, numbered.
    Whole,
    /// The whole file verbatim, without numbers or header.
    Raw,
    /// Sorted, merged line ranges; `raw` drops numbering and the header.
    Lines { ranges: Vec<LineRange>, raw: bool },
}

impl Selector {
    #[must_use]
    pub fn is_raw(&self) -> bool {
        match self {
            Self::Raw => true,
            Self::Lines { raw, .. } => *raw,
            Self::Whole => false,
        }
    }
}

/// A selector syntax or bounds error; the message is model-facing.
#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
#[error("{0}")]
pub struct SelectorError(String);

impl SelectorError {
    /// A comma-separated range list aimed at a directory.
    pub(crate) fn directory_multi_range() -> Self {
        Self("Multi-range line selectors are not supported for directory listings.".to_owned())
    }
}

/// Whether one-based `line` falls inside any of `ranges`.
pub(crate) fn line_in_ranges(line: u64, ranges: &[LineRange]) -> bool {
    ranges
        .iter()
        .any(|range| line >= range.start_line && range.end_line.is_none_or(|end| line <= end))
}

/// Parse one `N`, `N-M`, `N-`, `N+K`, `N..M`, or `N..` chunk.
fn parse_line_range_chunk(input: &str) -> Result<Option<LineRange>, SelectorError> {
    let input = strip_line_prefix(input);
    let digit_end = input.bytes().take_while(u8::is_ascii_digit).count();
    if digit_end == 0 {
        return Ok(None);
    }
    let start = parse_u64(&input[..digit_end])?;
    if start == 0 {
        return Err(SelectorError(
            "Line selector 0 is invalid; lines are 1-indexed. Use :1.".to_owned(),
        ));
    }
    let rest = &input[digit_end..];
    if rest.is_empty() {
        return Ok(Some(LineRange {
            start_line: start,
            end_line: None,
        }));
    }
    let (count, rhs) = if let Some(rhs) = rest.strip_prefix("..") {
        (false, rhs)
    } else if let Some(rhs) = rest.strip_prefix('-') {
        (false, rhs)
    } else if let Some(rhs) = rest.strip_prefix('+') {
        (true, rhs)
    } else {
        return Ok(None);
    };
    let rhs = strip_line_prefix(rhs);
    if rhs.bytes().any(|byte| !byte.is_ascii_digit()) {
        return Ok(None);
    }
    if rhs.is_empty() {
        return Ok((!count).then_some(LineRange {
            start_line: start,
            end_line: None,
        }));
    }
    let value = parse_u64(rhs)?;
    if count {
        if value == 0 {
            return Err(SelectorError(format!(
                "Invalid range {start}+0: count must be >= 1."
            )));
        }
        let end = start.checked_add(value - 1).ok_or_else(|| {
            SelectorError(format!(
                "Invalid range {start}+{value}: count is too large."
            ))
        })?;
        return Ok(Some(LineRange {
            start_line: start,
            end_line: Some(end),
        }));
    }
    if value < start {
        return Err(SelectorError(format!(
            "Invalid range {start}-{value}: end must be >= start."
        )));
    }
    Ok(Some(LineRange {
        start_line: start,
        end_line: Some(value),
    }))
}

fn strip_line_prefix(input: &str) -> &str {
    input
        .strip_prefix('L')
        .or_else(|| input.strip_prefix('l'))
        .unwrap_or(input)
}

fn parse_u64(input: &str) -> Result<u64, SelectorError> {
    input
        .parse()
        .map_err(|_| SelectorError(format!("Line selector '{input}' is too large.")))
}

/// Parse, sort, and merge a comma-separated list of line ranges.
fn parse_line_ranges(input: &str) -> Result<Option<Vec<LineRange>>, SelectorError> {
    let mut ranges = Vec::new();
    for chunk in input.split(',') {
        let Some(range) = parse_line_range_chunk(chunk)? else {
            return Ok(None);
        };
        ranges.push(range);
    }
    ranges.sort_unstable_by_key(|range| range.start_line);
    let mut merged: Vec<LineRange> = Vec::with_capacity(ranges.len());
    for current in ranges {
        let Some(last) = merged.last_mut() else {
            merged.push(current);
            continue;
        };
        let Some(last_end) = last.end_line else {
            continue;
        };
        if current.start_line <= last_end.saturating_add(1) {
            match current.end_line {
                None => last.end_line = None,
                Some(end) if end > last_end => last.end_line = Some(end),
                Some(_) => {}
            }
        } else {
            merged.push(current);
        }
    }
    Ok((!merged.is_empty()).then_some(merged))
}

/// Parse a selector (without its leading colon).
///
/// # Errors
///
/// A malformed range, or a selector made only of read-like chunks that do
/// not combine.
pub fn parse_selector(input: Option<&str>) -> Result<Selector, SelectorError> {
    let Some(input) = input.filter(|value| !value.is_empty()) else {
        return Ok(Selector::Whole);
    };
    if let Some((first, second)) = input.split_once(':') {
        if !second.contains(':') {
            let range = if first.eq_ignore_ascii_case("raw") {
                Some(second)
            } else if second.eq_ignore_ascii_case("raw") {
                Some(first)
            } else {
                None
            };
            if let Some(ranges) = range.map(parse_line_ranges).transpose()?.flatten() {
                return Ok(Selector::Lines { ranges, raw: true });
            }
        }
        return Err(invalid_selector(input));
    }
    if input.eq_ignore_ascii_case("raw") {
        return Ok(Selector::Raw);
    }
    match parse_line_ranges(input)? {
        Some(ranges) => Ok(Selector::Lines { ranges, raw: false }),
        None => Err(invalid_selector(input)),
    }
}

fn invalid_selector(input: &str) -> SelectorError {
    SelectorError(format!(
        "Invalid selector ':{input}'. Use :N, :N-M, :N+K, :N- (open-ended), a comma-separated list \
         of ranges, :raw, or a range combined with raw (e.g. :raw:50-100)."
    ))
}

/// A path with its trailing selector peeled off.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SplitPath<'a> {
    pub path: &'a str,
    /// Selector text without its leading colon.
    pub selector: Option<&'a str>,
}

/// Peel a selector from the end of `raw_path` (`a.rs:10-20`, `a.rs:raw`,
/// `a.rs:raw:10-20`, `a.rs:10-20:raw`).
#[must_use]
pub fn split_path_and_selector(raw_path: &str) -> SplitPath<'_> {
    let Some(colon) = raw_path.rfind(':').filter(|colon| *colon > 0) else {
        return SplitPath {
            path: raw_path,
            selector: None,
        };
    };
    let candidate = &raw_path[colon + 1..];
    if !is_simple_selector(candidate) {
        return SplitPath {
            path: raw_path,
            selector: None,
        };
    }
    let mut path = &raw_path[..colon];
    let mut selector = candidate;
    if let Some(inner_colon) = path.rfind(':').filter(|colon| *colon > 0) {
        let inner = &path[inner_colon + 1..];
        let compound = (inner.eq_ignore_ascii_case("raw") && is_range_list(candidate))
            || (is_range_list(inner) && candidate.eq_ignore_ascii_case("raw"));
        if compound {
            path = &path[..inner_colon];
            selector = &raw_path[inner_colon + 1..];
        }
    }
    SplitPath {
        path,
        selector: Some(selector),
    }
}

fn is_simple_selector(input: &str) -> bool {
    input.eq_ignore_ascii_case("raw") || is_range_list(input)
}

fn is_range_list(input: &str) -> bool {
    !input.is_empty() && input.split(',').all(is_range_chunk_syntax)
}

fn is_range_chunk_syntax(input: &str) -> bool {
    let input = strip_line_prefix(input);
    let digit_end = input.bytes().take_while(u8::is_ascii_digit).count();
    if digit_end == 0 {
        return false;
    }
    let rest = &input[digit_end..];
    if rest.is_empty() || rest == "-" || rest == ".." {
        return true;
    }
    let Some(rhs) = rest
        .strip_prefix('-')
        .or_else(|| rest.strip_prefix('+'))
        .or_else(|| rest.strip_prefix(".."))
    else {
        return false;
    };
    let rhs = strip_line_prefix(rhs);
    !rhs.is_empty() && rhs.bytes().all(|byte| byte.is_ascii_digit())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn range(start_line: u64, end_line: Option<u64>) -> LineRange {
        LineRange {
            start_line,
            end_line,
        }
    }

    #[test]
    fn parses_range_forms_and_merges() {
        assert_eq!(
            parse_selector(Some("L5..L7,1-2,3,10+2")).unwrap(),
            Selector::Lines {
                ranges: vec![range(1, None)],
                raw: false
            }
        );
        assert_eq!(
            parse_selector(Some("1-2,3-5,20+3")).unwrap(),
            Selector::Lines {
                ranges: vec![range(1, Some(5)), range(20, Some(22))],
                raw: false
            }
        );
        assert_eq!(
            parse_selector(Some("raw:50-100")).unwrap(),
            Selector::Lines {
                ranges: vec![range(50, Some(100))],
                raw: true
            }
        );
        assert_eq!(parse_selector(Some("RAW")).unwrap(), Selector::Raw);
        assert_eq!(parse_selector(None).unwrap(), Selector::Whole);
    }

    #[test]
    fn rejects_bad_ranges_with_teaching_messages() {
        assert_eq!(
            [
                parse_selector(Some("0")).unwrap_err().to_string(),
                parse_selector(Some("9-3")).unwrap_err().to_string(),
                parse_selector(Some("4+0")).unwrap_err().to_string(),
            ],
            [
                "Line selector 0 is invalid; lines are 1-indexed. Use :1.",
                "Invalid range 9-3: end must be >= start.",
                "Invalid range 4+0: count must be >= 1.",
            ]
        );
    }

    #[test]
    fn splits_trailing_selectors_only() {
        let split = |raw| {
            let SplitPath { path, selector } = split_path_and_selector(raw);
            (path, selector)
        };
        assert_eq!(split("src/a.rs:50-120"), ("src/a.rs", Some("50-120")));
        assert_eq!(split("src/a.rs:raw:10-20"), ("src/a.rs", Some("raw:10-20")));
        assert_eq!(split("src/a.rs:10-20:raw"), ("src/a.rs", Some("10-20:raw")));
        assert_eq!(split("src/a.rs"), ("src/a.rs", None));
        assert_eq!(split("C:dir"), ("C:dir", None));
    }
}
