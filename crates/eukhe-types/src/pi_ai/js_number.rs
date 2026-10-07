//! Serde helpers that print `f64` fields the way JavaScript `JSON.stringify`
//! prints numbers where serde can express it: integral values below 2^53 as
//! integers (`0`, not `0.0`), every other finite value through `serde_json`'s
//! shortest round-trip form. Non-finite values serialize as `null`, like
//! `JSON.stringify(NaN)`.

use serde::Serializer;

/// Largest magnitude below which an integral `f64` is printed as an integer.
const MAX_EXACT_INTEGER: f64 = 9_007_199_254_740_992.0;

/// Serialize one JS number.
///
/// # Errors
///
/// Returns the serializer's error.
// serde's `serialize_with` contract passes the field by reference.
#[allow(clippy::trivially_copy_pass_by_ref)]
pub fn serialize<S: Serializer>(value: &f64, serializer: S) -> Result<S::Ok, S::Error> {
    let value = *value;
    if !value.is_finite() {
        return serializer.serialize_none();
    }
    if value.fract() == 0.0 && value.abs() < MAX_EXACT_INTEGER {
        // The guard proves the conversion exact: whole value, |v| < 2^53.
        #[allow(clippy::cast_possible_truncation)]
        let whole = value as i64;
        return serializer.serialize_i64(whole);
    }
    serializer.serialize_f64(value)
}

/// `Option<f64>` variant of [`serialize`] for optional fields (always paired
/// with `skip_serializing_if = "Option::is_none"`).
pub mod option {
    use serde::Serializer;

    /// Serialize an optional JS number.
    ///
    /// # Errors
    ///
    /// Returns the serializer's error.
    // serde's `serialize_with` contract passes the field by reference.
    #[allow(clippy::ref_option)]
    pub fn serialize<S: Serializer>(value: &Option<f64>, serializer: S) -> Result<S::Ok, S::Error> {
        match value {
            Some(number) => super::serialize(number, serializer),
            None => serializer.serialize_none(),
        }
    }
}
