//! Finite JSON numbers with JS `Number` semantics and `Number.prototype.toString`
//! formatting.

use std::fmt;

/// Largest integer `n` such that every integer in `[-n, n]` is exactly a double
/// (`Number.MAX_SAFE_INTEGER`).
pub const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;

/// A finite JS double. `NaN` and the infinities are not JSON and cannot be
/// constructed. `-0` is kept (JS keeps it) and prints as `0`.
///
/// Equality is JS `===`: `0 == -0`.
///
/// ```
/// use eukhe_chord::json::JsonNumber;
/// let n = JsonNumber::new(1e21).unwrap();
/// assert_eq!(n.to_string(), "1e+21");
/// assert!(JsonNumber::new(f64::NAN).is_none());
/// ```
#[derive(Clone, Copy, Debug, Default)]
pub struct JsonNumber(f64);

impl JsonNumber {
    /// The number, or `None` when `value` is not finite.
    #[must_use]
    pub fn new(value: f64) -> Option<Self> {
        value.is_finite().then_some(Self(value))
    }

    /// The double.
    #[must_use]
    pub fn get(self) -> f64 {
        self.0
    }

    /// Whether the value is integral (`Number.isInteger`).
    #[must_use]
    pub fn is_integer(self) -> bool {
        self.0.fract() == 0.0
    }

    /// The value as `u64` when it is an integer that `u64` holds exactly.
    #[must_use]
    pub fn as_u64(self) -> Option<u64> {
        if !self.is_integer() || self.0 < 0.0 || self.0 >= 18_446_744_073_709_551_616.0 {
            return None;
        }
        // In range and integral: the conversion is exact.
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // checked above
        Some(self.0 as u64)
    }

    /// The value as `i64` when it is an integer that `i64` holds exactly.
    #[must_use]
    pub fn as_i64(self) -> Option<i64> {
        if !self.is_integer()
            || self.0 < -9_223_372_036_854_775_808.0
            || self.0 >= 9_223_372_036_854_775_808.0
        {
            return None;
        }
        #[allow(clippy::cast_possible_truncation)] // checked above
        Some(self.0 as i64)
    }

    /// The value as `usize` when it is an integer that `usize` holds exactly.
    #[must_use]
    pub fn as_usize(self) -> Option<usize> {
        self.as_u64().and_then(|value| usize::try_from(value).ok())
    }

    /// The safe integer this number is, when integral and within
    /// [`MAX_SAFE_INTEGER`].
    #[must_use]
    pub(crate) fn as_safe_integer(self) -> Option<i64> {
        (self.is_integer() && self.0.abs() <= MAX_SAFE_INTEGER)
            .then(|| self.as_i64())
            .flatten()
    }
}

impl PartialEq for JsonNumber {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl fmt::Display for JsonNumber {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut text = String::new();
        write_js_number(&mut text, self.0);
        formatter.write_str(&text)
    }
}

macro_rules! exact_from {
    ($($source:ty),*) => {$(
        impl From<$source> for JsonNumber {
            fn from(value: $source) -> Self {
                Self(f64::from(value))
            }
        }
    )*};
}
exact_from!(i8, i16, i32, u8, u16, u32);

/// Append JS `Number.prototype.toString()` of a finite double (ECMA-262
/// `Number::toString`, radix 10: shortest round-trip digits, ties to even,
/// decimal notation for `1e-6 <= |x| < 1e21`). `-0` prints `0`.
pub(crate) fn write_js_number(out: &mut String, value: f64) {
    if value == 0.0 {
        out.push('0');
        return;
    }
    out.push_str(ryu_js::Buffer::new().format_finite(value));
}

#[cfg(test)]
mod tests {
    use super::write_js_number;

    fn js(value: f64) -> String {
        let mut out = String::new();
        write_js_number(&mut out, value);
        out
    }

    #[test]
    fn formats_like_number_to_string() {
        for (value, expected) in [
            (0.0, "0"),
            (-0.0, "0"),
            (1.0, "1"),
            (-1.5, "-1.5"),
            (0.1, "0.1"),
            (1e21, "1e+21"),
            (1e20, "100000000000000000000"),
            (123_456_789_012_345_680_000.0, "123456789012345680000"),
            (1e-6, "0.000001"),
            (1e-7, "1e-7"),
            (1.5e-7, "1.5e-7"),
            (5e-324, "5e-324"),
            (f64::MAX, "1.7976931348623157e+308"),
            (2f64.powi(60), "1152921504606847000"),
            (0.000_123, "0.000123"),
            (-155_222_902_588.078_12, "-155222902588.07812"),
            (123.456, "123.456"),
        ] {
            assert_eq!(js(value), expected, "{value:e}");
        }
    }
}
