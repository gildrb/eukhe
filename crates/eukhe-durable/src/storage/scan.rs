//! Scan order and cursors of the built-in storage backends (`storage/scan.ts`).

use eukhe_bend::rules::scan;
use eukhe_bend::{expect_core, Entry};
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

/// Resolve a scan's order and position. The compiled core decides
/// (`eukhe_bend::rules::scan`, `laws/scan.bend`) from what the cursor holds:
/// a cursor continues in the order it was created with, whether the query
/// repeats that order or omits it; a different `order` fails. A cursor
/// without an order, written before scans had one, continues in the scan's
/// default order.
///
/// TS also rejects an invalid requested order (`Invalid scan order: …`); a
/// [`ScanOrder`] cannot hold one.
pub(crate) fn scan_start(
    requested: Option<ScanOrder>,
    cursor: Option<&Cursor>,
    fallback: ScanOrder,
) -> Result<ScanStart, StorageError> {
    let after = cursor.and_then(|cursor| safe_after(cursor.get("after")));
    let read = cursor.map(|cursor| scan::Cursor {
        after: match (cursor.get("after"), after) {
            (None, _) => scan::After::Absent,
            (Some(_), None) => scan::After::NotSafe,
            (Some(_), Some(_)) => scan::After::Safe,
        },
        mark: match cursor.get("order") {
            None => scan::Mark::Absent,
            Some(JsonValue::String(order)) if &**order == "ascending" => scan::Mark::Ascending,
            Some(JsonValue::String(order)) if &**order == "descending" => scan::Mark::Descending,
            Some(_) => scan::Mark::Other,
        },
    });
    match expect_core(
        Entry::Scan,
        scan::start(requested.map(order_of), read, order_of(fallback)),
    ) {
        scan::Start::Begin { order, after: from } => Ok(ScanStart {
            order: match order {
                scan::Order::Ascending => ScanOrder::Ascending,
                scan::Order::Descending => ScanOrder::Descending,
            },
            after: if from { after } else { None },
        }),
        scan::Start::Refused(text) => Err(StorageError::request(text)),
    }
}

/// A cursor's `after` value, when it is a safe integer.
pub(crate) fn safe_after(after: Option<&JsonValue>) -> Option<i64> {
    match after.and_then(JsonValue::as_number) {
        Some(number)
            if number.is_integer() && number.get().abs() <= eukhe_chord::json::MAX_SAFE_INTEGER =>
        {
            #[expect(
                clippy::cast_possible_truncation,
                reason = "a safe integer fits i64 exactly"
            )]
            let after = number.get() as i64;
            Some(after)
        }
        _ => None,
    }
}

fn order_of(order: ScanOrder) -> scan::Order {
    match order {
        ScanOrder::Ascending => scan::Order::Ascending,
        ScanOrder::Descending => scan::Order::Descending,
    }
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
