//! Leaf-by-leaf JSON assignment into a draft (`harness/json.ts`).

use eukhe_chord::delta::{Draft, DraftItem, Seg, TrackerError};
use eukhe_chord::json::JsonValue;

/// Assign `value` at `target[key]` leaf by leaf. Chord records a container
/// assignment as one full set and only emits an append when a string leaf is
/// reassigned with a longer string, so writing the partial whole would store
/// and publish the complete message on every flush.
///
/// # Errors
///
/// Draft failures.
pub fn assign_json(
    target: &Draft,
    key: impl Into<Seg>,
    value: &JsonValue,
) -> Result<(), TrackerError> {
    let key = key.into();
    let current = target.get(key.clone())?;
    if let Some(DraftItem::Draft(current)) = &current {
        if let (false, Some(fields)) = (current.is_array(), value.as_object()) {
            for name in current.keys()? {
                if !fields.contains_key(&name) {
                    current.delete(name.as_str())?;
                }
            }
            for (name, child) in fields.iter() {
                assign_json(current, name, child)?;
            }
            return Ok(());
        }
        if let (true, Some(items)) = (current.is_array(), value.as_array()) {
            let length = current.len()?;
            if length <= items.len() {
                for (index, item) in items.iter().enumerate() {
                    if index < length {
                        assign_json(current, index, item)?;
                    } else {
                        current.push([item.clone()])?;
                    }
                }
                return Ok(());
            }
        }
    }
    // `current !== value`: a container draft is never the plain value.
    let unchanged =
        matches!(&current, Some(DraftItem::Value(existing)) if existing.strict_equals(value));
    if !unchanged {
        target.set(key, value.clone())?;
    }
    Ok(())
}
