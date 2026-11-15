//! The budget amounts a user types, read the same by every surface (the
//! CLI's `--budget-*` flags and `eukhe budget`, `/budget set` and `/budget
//! add`, a message's `/b` prefix).
//!
//! Cost in dollars (`1.50`, `$1.50`; stored in micro-dollars, rounded up),
//! tokens (`200000`, `200k`, `1.5m`), time (`90s`, `10m`, `2h`; stored in
//! milliseconds: the wall-clock duration of the budget from when it is
//! set, or by how much `add` moves the deadline), tool calls and model
//! requests (plain integers). Each is more than zero and at most
//! [`BUDGET_AMOUNT_MAX`] in its stored unit.

use crate::budget::{BudgetDimension, BudgetLimits, LimitValue, RunLimits, BUDGET_AMOUNT_MAX};

/// The keys of `/budget set` and `/budget add`, as their errors list them.
const KEYS: &str = "cost=<dollars>, tokens=<n>, time=<duration>, calls=<n>, requests=<n>";

/// Why typed text is not a budget amount. `name` is what the user typed
/// the value for: a flag (`--budget-cost`) or a key (`cost`).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum BudgetTextError {
    /// The value does not read as an amount of its dimension.
    #[error("{name} \"{value}\": expected {expected}")]
    Malformed {
        name: String,
        value: String,
        expected: &'static str,
    },
    /// The value reads as zero.
    #[error("{name} \"{value}\": a budget amount is more than zero")]
    Zero { name: String, value: String },
    /// The value is past what a budget holds.
    #[error("{name} \"{value}\": a budget holds at most {max}")]
    TooLarge {
        name: String,
        value: String,
        max: String,
    },
    /// A word of `/budget set` or `/budget add` that is not `key=value`
    /// with a known key.
    #[error("\"{word}\": expected one of {KEYS}")]
    UnknownWord { word: String },
    /// A key given more than once.
    #[error("{name} is given twice")]
    Repeated { name: String },
    /// No `key=value` word at all.
    #[error("name at least one of {KEYS}")]
    NoAmount,
}

/// `number` (`digits` or `digits.digits`) times `scale`, rounded up and
/// saturating; `None` when it is not such a number. A number starts with
/// a digit: `.50` is what an unquoted `$1.50` leaves of itself in a
/// shell, and must not read as half a dollar.
fn scaled(number: &str, scale: u64) -> Option<u128> {
    let (whole, fraction) = match number.split_once('.') {
        Some((whole, fraction)) if !fraction.is_empty() => (whole, fraction),
        Some(_) => return None,
        None => (number, ""),
    };
    let digits = |text: &str| text.bytes().all(|byte| byte.is_ascii_digit());
    if whole.is_empty() || !digits(whole) || !digits(fraction) {
        return None;
    }
    let value = |text: &str| {
        text.bytes().fold(0_u128, |sum, byte| {
            sum.saturating_mul(10)
                .saturating_add(u128::from(byte - b'0'))
        })
    };
    // Twelve fraction digits are past every scale's precision: the rest
    // only decides the rounding.
    let (kept, rest) = fraction.split_at(fraction.len().min(12));
    let numerator = value(kept) * u128::from(scale);
    let denominator = 10_u128.pow(u32::try_from(kept.len()).unwrap_or(0));
    let rounds_up = numerator % denominator != 0 || rest.bytes().any(|byte| byte != b'0');
    Some(
        value(whole)
            .saturating_mul(u128::from(scale))
            .saturating_add(numerator / denominator)
            .saturating_add(u128::from(rounds_up)),
    )
}

/// `text` without its last character when that is `suffix` in either
/// case.
fn strip_unit(text: &str, suffix: char) -> Option<&str> {
    let last = text.chars().next_back()?;
    last.eq_ignore_ascii_case(&suffix)
        .then(|| &text[..text.len() - last.len_utf8()])
}

/// A whole number (no fraction, no unit).
fn whole(text: &str) -> Option<u128> {
    if text.contains('.') {
        None
    } else {
        scaled(text, 1)
    }
}

/// The amount of `dimension` that `text` names, in the dimension's stored
/// unit; `name` is what the user typed it for.
///
/// # Errors
///
/// Text that is not an amount of the dimension, zero, or an amount past
/// [`BUDGET_AMOUNT_MAX`]: the error names `name` and the text.
pub fn parse_amount(
    dimension: BudgetDimension,
    name: &str,
    text: &str,
) -> Result<u64, BudgetTextError> {
    let text = text.trim();
    let (amount, expected) = match dimension {
        BudgetDimension::Cost => (
            scaled(text.strip_prefix('$').unwrap_or(text), 1_000_000),
            "dollars, like 1.50 or $1.50",
        ),
        BudgetDimension::Tokens => (
            if let Some(thousands) = strip_unit(text, 'k') {
                scaled(thousands, 1_000)
            } else if let Some(millions) = strip_unit(text, 'm') {
                scaled(millions, 1_000_000)
            } else {
                scaled(text, 1)
            },
            "a token count, like 200000, 200k or 1.5m",
        ),
        BudgetDimension::Time => (
            if let Some(seconds) = strip_unit(text, 's') {
                scaled(seconds, 1_000)
            } else if let Some(minutes) = strip_unit(text, 'm') {
                scaled(minutes, 60_000)
            } else if let Some(hours) = strip_unit(text, 'h') {
                scaled(hours, 3_600_000)
            } else {
                None
            },
            "a duration, like 90s, 10m or 2h",
        ),
        BudgetDimension::ToolCalls => (whole(text), "a whole number of tool calls, like 50"),
        BudgetDimension::Requests => (whole(text), "a whole number of model requests, like 30"),
    };
    let stored = amount.map(|amount| {
        u64::try_from(amount)
            .ok()
            .filter(|amount| *amount <= BUDGET_AMOUNT_MAX)
    });
    let (name, value) = match stored {
        Some(Some(amount)) if amount > 0 => return Ok(amount),
        Some(Some(_) | None) | None => (name.to_string(), text.to_string()),
    };
    Err(match stored {
        Some(Some(_)) => BudgetTextError::Zero { name, value },
        Some(None) => BudgetTextError::TooLarge {
            name,
            value,
            max: match dimension {
                BudgetDimension::Cost => format!(
                    "${}.{:06}",
                    BUDGET_AMOUNT_MAX / 1_000_000,
                    BUDGET_AMOUNT_MAX % 1_000_000
                ),
                BudgetDimension::Tokens => format!("{BUDGET_AMOUNT_MAX} tokens"),
                BudgetDimension::Time => format!("{}h", BUDGET_AMOUNT_MAX / 3_600_000),
                BudgetDimension::ToolCalls => format!("{BUDGET_AMOUNT_MAX} tool calls"),
                BudgetDimension::Requests => format!("{BUDGET_AMOUNT_MAX} requests"),
            },
        },
        None => BudgetTextError::Malformed {
            name,
            value,
            expected,
        },
    })
}

/// A limit the principal sets for `dimension`: an amount
/// ([`parse_amount`]) or `unlimited`.
///
/// # Errors
///
/// What [`parse_amount`] refuses, `unlimited` aside.
pub fn parse_limit(
    dimension: BudgetDimension,
    name: &str,
    text: &str,
) -> Result<LimitValue, BudgetTextError> {
    if text.trim() == LimitValue::UNLIMITED {
        return Ok(LimitValue::Unlimited);
    }
    parse_amount(dimension, name, text).map(LimitValue::At)
}

/// The `key=value` words of `/budget set`, `/budget add` and `/b`:
/// `cost`, `tokens`, `time`, `calls` and `requests`, any subset, each at
/// most once; `unlimited` only where `unlimited` is a limit (`set`).
fn assignments(text: &str, unlimited: bool) -> Result<RunLimits, BudgetTextError> {
    let mut limits = RunLimits::default();
    for word in text.split_whitespace() {
        let unknown = || BudgetTextError::UnknownWord {
            word: word.to_string(),
        };
        let (key, value) = word.split_once('=').ok_or_else(unknown)?;
        let dimension = key_dimension(key).ok_or_else(unknown)?;
        if limits.get(dimension).is_some() {
            return Err(BudgetTextError::Repeated {
                name: key.to_string(),
            });
        }
        let limit = if unlimited {
            parse_limit(dimension, key, value)?
        } else {
            LimitValue::At(parse_amount(dimension, key, value)?)
        };
        limits = limits.with(dimension, Some(limit));
    }
    if limits.is_unset() {
        return Err(BudgetTextError::NoAmount);
    }
    Ok(limits)
}

/// The dimension a `key=value` key names.
#[must_use]
pub fn key_dimension(key: &str) -> Option<BudgetDimension> {
    match key {
        "cost" => Some(BudgetDimension::Cost),
        "tokens" => Some(BudgetDimension::Tokens),
        "time" => Some(BudgetDimension::Time),
        "calls" => Some(BudgetDimension::ToolCalls),
        "requests" => Some(BudgetDimension::Requests),
        _ => None,
    }
}

/// The `key=value` words of `/budget add`: amounts only.
///
/// # Errors
///
/// A word that is not `key=value` with one of the five keys, a key given
/// twice, no word at all, or a value [`parse_amount`] refuses.
pub fn parse_assignments(text: &str) -> Result<BudgetLimits, BudgetTextError> {
    assignments(text, false).map(|limits| limits.counted())
}

/// The `key=value` words of `/budget set`: each an amount or
/// `unlimited`.
///
/// # Errors
///
/// As [`parse_assignments`]; `unlimited` is a value here.
pub fn parse_limits(text: &str) -> Result<RunLimits, BudgetTextError> {
    assignments(text, true)
}

#[cfg(test)]
mod tests;
