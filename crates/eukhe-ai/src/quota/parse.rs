//! Shared pieces of the providers' quota readers: number and time fields,
//! window names, and the usage endpoint request.

use reqwest::header::HeaderMap;
use serde_json::Value;

use super::QuotaError;
use crate::api::bedrock_converse_stream::js_date_parse;
use crate::auth::oauth::http::{fetch, FetchRequest};

/// A used percentage (0..=100, more on overage) in permille.
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "clamped to 0..=u32::MAX before the cast"
)]
pub(super) fn permille(percent: f64) -> Option<u32> {
    percent
        .is_finite()
        .then(|| (percent * 10.0).round().clamp(0.0, f64::from(u32::MAX)) as u32)
}

/// A JSON number, or a number written as a string.
pub(super) fn number(value: Option<&Value>) -> Option<f64> {
    match value? {
        Value::Number(number) => number.as_f64(),
        Value::String(text) => text.trim().parse().ok(),
        _ => None,
    }
    .filter(|number: &f64| number.is_finite())
}

/// A header's value as a number.
pub(super) fn header_number(headers: &HeaderMap, name: &str) -> Option<f64> {
    headers
        .get(name)?
        .to_str()
        .ok()?
        .trim()
        .parse()
        .ok()
        .filter(|number: &f64| number.is_finite())
}

/// Epoch seconds, or epoch milliseconds past the year 33658, in
/// milliseconds.
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "positive and finite, checked before the cast"
)]
pub(super) fn epoch_ms(value: f64) -> Option<u64> {
    if !(value.is_finite() && value > 0.0) {
        return None;
    }
    Some(if value > 1e12 { value } else { value * 1000.0 } as u64)
}

/// An ISO 8601 date or date-time in epoch milliseconds.
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "positive and finite, checked before the cast"
)]
pub(super) fn iso_ms(value: Option<&Value>) -> Option<u64> {
    let ms = js_date_parse(value?.as_str()?.trim());
    (ms.is_finite() && ms > 0.0).then_some(ms as u64)
}

/// A window's name from its length: "5h", "7d", "90m".
pub(super) fn window_label(minutes: u64) -> String {
    if minutes > 0 && minutes.is_multiple_of(1440) {
        format!("{}d", minutes / 1440)
    } else if minutes > 0 && minutes.is_multiple_of(60) {
        format!("{}h", minutes / 60)
    } else {
        format!("{minutes}m")
    }
}

/// Whole minutes of a positive length in minutes.
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "positive and finite, checked before the cast"
)]
pub(super) fn minutes(value: f64) -> Option<u64> {
    (value.is_finite() && value >= 1.0).then(|| value.round() as u64)
}

/// GET a usage endpoint and read its JSON body.
pub(super) async fn get_json(request: FetchRequest) -> Result<Value, QuotaError> {
    let response = fetch(request, None)
        .await
        .map_err(|error| QuotaError::Transport {
            message: crate::utils::diagnostics::format_thrown_value(&error),
        })?;
    if !response.ok() {
        return Err(QuotaError::Status {
            status: response.status,
        });
    }
    response.json().map_err(|_| QuotaError::Unreadable)
}
