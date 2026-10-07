//! Shared helpers for the ported delta tests.

#![allow(dead_code)] // each test crate uses a subset

use eukhe_chord::delta::{apply, Op, WireOp};
use eukhe_chord::json::JsonValue;

/// Parse JSON text.
pub fn j(text: &str) -> JsonValue {
    JsonValue::parse(text).unwrap_or_else(|error| panic!("invalid json {text}: {error}"))
}

/// Parse an op batch written as TS tuples.
pub fn ops(text: &str) -> Vec<Op> {
    serde_json::from_str(text).unwrap_or_else(|error| panic!("invalid ops {text}: {error}"))
}

/// Parse a wire batch written as TS tuples.
pub fn wire(text: &str) -> Vec<WireOp> {
    serde_json::from_str(text).unwrap_or_else(|error| panic!("invalid wire ops {text}: {error}"))
}

/// A batch as its JSON text.
pub fn ops_text(ops: &[Op]) -> String {
    JsonValue::from(ops.iter().map(Op::to_json).collect::<Vec<_>>()).to_string()
}

/// `JSON.parse(JSON.stringify(value))`: a detached deep copy.
pub fn clone(value: &JsonValue) -> JsonValue {
    eukhe_chord::json::copy_json(value)
}

/// Replay a batch on a detached copy of `base` (the TS `replay` helper).
pub fn replay(base: &JsonValue, operations: &[Op]) -> JsonValue {
    apply(clone(base), operations).expect("replay")
}

/// Panics when one container allocation appears at two places.
pub fn expect_alias_free(value: &JsonValue) {
    fn visit(value: &JsonValue, path: &str, seen: &mut std::collections::HashMap<usize, String>) {
        let address = match value {
            JsonValue::Array(items) => std::sync::Arc::as_ptr(items) as usize,
            JsonValue::Object(object) => std::sync::Arc::as_ptr(object) as usize,
            _ => return,
        };
        if let Some(previous) = seen.insert(address, path.to_owned()) {
            panic!("container at {path} aliases {previous}");
        }
        match value {
            JsonValue::Array(items) => {
                for (index, item) in items.iter().enumerate() {
                    visit(item, &format!("{path}[{index}]"), seen);
                }
            }
            JsonValue::Object(object) => {
                for (key, item) in object.iter() {
                    visit(item, &format!("{path}.{key}"), seen);
                }
            }
            _ => {}
        }
    }
    visit(value, "$root", &mut std::collections::HashMap::new());
}
