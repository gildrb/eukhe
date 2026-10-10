//! Scan order and cursors of the built-in storage backends (`storage/scan.ts`).

use eukhe_chord::json::{JsonNumber, JsonObject, JsonValue};

use crate::errors::StorageError;
use crate::types::{Cursor, ScanOrder};

/// Where a built-in storage scan starts: its order and the last ID a previous
/// page returned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ScanStart {
    pub(crate) order: ScanOrder,
    pub(crate) after: Option<i64>,
}

/// Resolve a scan's order and position. A cursor continues in the order it
/// was created with, whether the query repeats that order or omits it; a
/// different `order` fails. A cursor without an order, written before scans
/// had one, continues in the scan's default order.
///
/// TS also rejects an invalid requested order (`Invalid scan order: …`); a
/// [`ScanOrder`] cannot hold one.
pub(crate) fn scan_start(
    requested: Option<ScanOrder>,
    cursor: Option<&Cursor>,
    fallback: ScanOrder,
) -> Result<ScanStart, StorageError> {
    let Some(cursor) = cursor else {
        return Ok(ScanStart {
            order: requested.unwrap_or(fallback),
            after: None,
        });
    };
    let after = match cursor.get("after").and_then(JsonValue::as_number) {
        Some(number)
            if number.is_integer() && number.get().abs() <= eukhe_chord::json::MAX_SAFE_INTEGER =>
        {
            #[expect(
                clippy::cast_possible_truncation,
                reason = "a safe integer fits i64 exactly"
            )]
            let after = number.get() as i64;
            after
        }
        _ => return Err(StorageError::request("Invalid storage cursor")),
    };
    let stored = match cursor.get("order") {
        None => None,
        Some(JsonValue::String(order)) if &**order == "ascending" => Some(ScanOrder::Ascending),
        Some(JsonValue::String(order)) if &**order == "descending" => Some(ScanOrder::Descending),
        Some(_) => return Err(StorageError::request("Invalid storage cursor")),
    };
    let order = stored.unwrap_or(fallback);
    if let Some(requested) = requested {
        if requested != order {
            return Err(StorageError::request(format!(
                "The cursor continues a {} scan; the query asks for {}",
                order.as_str(),
                requested.as_str()
            )));
        }
    }
    Ok(ScanStart {
        order,
        after: Some(after),
    })
}

/// The continuation of a scan whose last returned item has `id`.
pub(crate) fn next_cursor(id: u64, order: ScanOrder) -> Cursor {
    let mut state = JsonObject::new();
    #[expect(clippy::cast_precision_loss, reason = "IDs are safe integers")]
    let after = JsonNumber::new(id as f64).map_or(JsonValue::Null, JsonValue::Number);
    state.insert("after", after);
    state.insert("order", JsonValue::from(order.as_str()));
    Cursor::new(state)
}
