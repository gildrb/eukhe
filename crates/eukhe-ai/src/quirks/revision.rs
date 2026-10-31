//! Model revisions: the `major.minor.patch`
//! triple that a model id names, and the range a family can require. A
//! port of omp's taxonomy revisions (`packages/catalog/src/compat/
//! revision.ts`, `taxonomy.ts` `extractRevision`).

use std::cmp::Ordering;

/// A `major.minor.patch` triple; an omitted component is 0.
pub(super) type Revision = [u8; 3];

/// A comparison of a range term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Op {
    Ge,
    Gt,
    Le,
    Lt,
    Eq,
}

/// A revision range: a conjunction of comparisons (`>=3.8`, `>=2.5 <4`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Range {
    terms: Vec<(Op, Revision)>,
}

/// One component: one or more ASCII digits, at most 255.
fn component(digits: &[u8]) -> Option<u8> {
    if digits.is_empty() || !digits.iter().all(u8::is_ascii_digit) {
        return None;
    }
    digits.iter().try_fold(0u8, |value, digit| {
        value.checked_mul(10)?.checked_add(digit - b'0')
    })
}

/// The revision at the start of `value` (which starts with a digit): up
/// to three components, separated by `.` or by `-` with a digit after it.
/// Digits that run into a letter are a size (`32b`), not a component.
fn leading(value: &[u8]) -> Option<Revision> {
    let mut out = [0u8; 3];
    let mut count = 0;
    let mut index = 0;
    while count < 3 {
        let start = index;
        while value.get(index).is_some_and(u8::is_ascii_digit) {
            index += 1;
        }
        let size = value.get(index).is_some_and(u8::is_ascii_alphabetic);
        let Some(part) = component(&value[start..index]).filter(|_| !size) else {
            return (count > 0).then_some(out);
        };
        out[count] = part;
        count += 1;
        let Some(&separator) = value.get(index) else {
            break;
        };
        let digit_next = value.get(index + 1).is_some_and(u8::is_ascii_digit);
        if !matches!(separator, b'.' | b'-') || !digit_next {
            break;
        }
        index += 1;
    }
    Some(out)
}

/// The revision that `id` names after `prefix`: the bare name (the
/// lowercased id after its last `/`) starts with `prefix`, and the
/// revision starts at the first digit after it. `None`: no revision.
pub(super) fn of(id: &str, prefix: &str) -> Option<Revision> {
    let lower = id.trim().to_lowercase();
    let bare = lower.rsplit('/').next().unwrap_or_default();
    let tail = bare.strip_prefix(prefix)?;
    let digit = tail.find(|c: char| c.is_ascii_digit())?;
    leading(&tail.as_bytes()[digit..])
}

impl Range {
    /// Parse a range: comparisons (`>=`, `>`, `<=`, `<`, `=`) with an
    /// operand of one to three components separated by `.`, separated by
    /// white space.
    pub(super) fn parse(text: &str) -> Result<Self, String> {
        let terms = text
            .split_whitespace()
            .map(|term| {
                let (op, operand) = [
                    (">=", Op::Ge),
                    (">", Op::Gt),
                    ("<=", Op::Le),
                    ("<", Op::Lt),
                    ("=", Op::Eq),
                ]
                .into_iter()
                .find_map(|(sign, op)| term.strip_prefix(sign).map(|operand| (op, operand)))
                .ok_or_else(|| format!("`{term}` has no comparison"))?;
                let parts = operand
                    .split('.')
                    .map(|part| component(part.as_bytes()))
                    .collect::<Option<Vec<u8>>>()
                    .filter(|parts| (1..=3).contains(&parts.len()))
                    .ok_or_else(|| format!("`{term}` has no revision of 1 to 3 components"))?;
                let mut revision = [0u8; 3];
                revision[..parts.len()].copy_from_slice(&parts);
                Ok((op, revision))
            })
            .collect::<Result<Vec<_>, String>>()?;
        if terms.is_empty() {
            return Err("the range has no comparison".to_owned());
        }
        Ok(Self { terms })
    }

    /// Whether `revision` satisfies every comparison.
    pub(super) fn holds(&self, revision: Revision) -> bool {
        self.terms.iter().all(|(op, bound)| {
            let order = revision.cmp(bound);
            match op {
                Op::Ge => order != Ordering::Less,
                Op::Gt => order == Ordering::Greater,
                Op::Le => order != Ordering::Greater,
                Op::Lt => order == Ordering::Less,
                Op::Eq => order == Ordering::Equal,
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{of, Range};

    /// omp's extraction: the revision starts at the first digit after the
    /// prefix, a size token is not a component, and a component past 255
    /// ends the revision.
    #[test]
    fn a_revision_is_read_after_the_prefix_of_the_bare_name() {
        let ids = [
            "qwen3.8-27b",
            "Qwen/Qwen3.8-2.4T-A95B",
            "qwen3-32b",
            "qwen3-8b",
            "qwen3.5-122b-a10b",
            "qwen.qwen3-32b-v1:0",
            "accounts/fireworks/models/qwen3p8-max",
            "qwen-max",
            "qwen-plus-2025-01-25",
            "qwq-32b",
            "qwen35",
            "qwen3.800",
            "workers-ai/@cf/qwen/qwen3.8-27b",
        ];
        assert_eq!(
            ids.map(|id| of(id, "qwen")),
            [
                Some([3, 8, 0]),
                Some([3, 8, 2]),
                Some([3, 0, 0]),
                Some([3, 0, 0]),
                Some([3, 5, 0]),
                Some([3, 0, 0]),
                None,
                None,
                None,
                None,
                Some([35, 0, 0]),
                Some([3, 0, 0]),
                Some([3, 8, 0]),
            ]
        );
    }

    #[test]
    fn a_range_is_a_conjunction_of_comparisons() {
        let below = Range::parse("<3.8").unwrap();
        let from = Range::parse(">=3.8").unwrap();
        let band = Range::parse(">=2.5 <4").unwrap();
        let exact = Range::parse("=3").unwrap();
        let after = Range::parse(">3.8 <=4.0.1").unwrap();
        let revisions = [[0, 0, 0], [3, 7, 9], [3, 8, 0], [4, 0, 1], [4, 0, 2]];
        assert_eq!(
            revisions.map(|revision| [
                below.holds(revision),
                from.holds(revision),
                band.holds(revision),
                exact.holds(revision),
                after.holds(revision),
            ]),
            [
                [true, false, false, false, false],
                [true, false, true, false, false],
                [false, true, true, false, false],
                [false, true, false, false, true],
                [false, true, false, false, false],
            ]
        );
        assert_eq!(
            ["", "3.8", ">=3-8", ">=1.2.3.4", ">=256"].map(|text| Range::parse(text).is_ok()),
            [false; 5]
        );
    }
}
