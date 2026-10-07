//! Port of `test/state-fuzz.test.ts`.
//!
//! TS runs one `mutate` against both the plain expected document and the
//! draft; Rust has one mutation function per representation
//! ([`mutate_expected`] on a `serde_json::Value`, [`mutate_draft`] on a
//! [`Draft`]) with the same cases. `clone(...)` (a `JSON.stringify` round trip)
//! becomes [`copy_json`] for values and a text round trip for operations.

use std::collections::HashMap;
use std::sync::Arc;

use serde_json::json as j;

use super::{json, ops_json};
use crate::delta::{apply_immutable, track, Draft, DraftItem, Op, TrackerError};
use crate::json::{copy_json, utf16_len, utf16_skip, JsonValue};

/// The TS mulberry32 `random(seed)`, returning the unsigned 32-bit sample
/// that TS divides by 2^32.
struct Random(i32);

/// JS `value >>> bits` read back as an int32 operand.
fn unsigned_shift(value: i32, bits: u32) -> i32 {
    (value.cast_unsigned() >> bits).cast_signed()
}

impl Random {
    fn next(&mut self) -> u32 {
        self.0 = self.0.wrapping_add(0x6d2b_79f5);
        let seed = self.0;
        let mut value = (seed ^ unsigned_shift(seed, 15)).wrapping_mul(1 | seed);
        // 0x3d = 61, the TS literal.
        value = value.wrapping_add((value ^ unsigned_shift(value, 7)).wrapping_mul(0x3d | value))
            ^ value;
        (value ^ unsigned_shift(value, 14)).cast_unsigned()
    }

    /// `Math.floor(rng() * cases)`: the sample over 2^32 times `cases` is
    /// exact in a double (under 2^53), so the floor is the integer quotient.
    fn below(&mut self, cases: u64) -> u64 {
        (u64::from(self.next()) * cases) >> 32
    }
}

/// The first twelve `Math.floor(rng() * 14)` choices, recorded from the TS
/// `random` under Node.
#[test]
fn random_matches_the_ts_generator() {
    for (seed, expected) in [
        (1, [8, 0, 7, 13, 13, 3, 8, 10, 5, 13, 6, 6]),
        (57, [10, 2, 1, 8, 6, 8, 3, 7, 6, 6, 7, 8]),
        (100, [2, 4, 7, 12, 7, 9, 0, 7, 3, 7, 8, 2]),
    ] {
        let mut rng = Random(seed);
        assert_eq!(expected.map(|_| rng.below(14)), expected, "seed {seed}");
    }
}

fn item(value: i64) -> serde_json::Value {
    j!({ "id": value, "text": format!("item-{value}"), "score": value % 7 })
}

fn index(value: i64, length: usize) -> usize {
    usize::try_from(value).unwrap() % length
}

fn mutate_expected(document: &mut serde_json::Value, choice: u64, value: i64) {
    match choice {
        0 => {
            let text = format!("{}-{value}", document["text"].as_str().unwrap());
            document["text"] = j!(text);
        }
        1 => {
            let current = document["text"].as_str().unwrap();
            let text = format!("{}{value}", utf16_skip(current, utf16_len(current).min(2)));
            document["text"] = j!(text);
        }
        2 => document["items"].as_array_mut().unwrap().push(item(value)),
        3 => document["items"]
            .as_array_mut()
            .unwrap()
            .insert(0, item(value)),
        4 => {
            let items = document["items"].as_array_mut().unwrap();
            if !items.is_empty() {
                items.remove(0);
            }
        }
        5 => {
            document["items"].as_array_mut().unwrap().pop();
        }
        6 => {
            let items = document["items"].as_array_mut().unwrap();
            let at = if items.is_empty() {
                0
            } else {
                index(value, items.len() + 1)
            };
            let remove = if items.is_empty() { 0 } else { index(value, 2) };
            let end = (at + remove).min(items.len());
            items.splice(at..end, [item(value)]);
        }
        7 => document["items"].as_array_mut().unwrap().reverse(),
        8 => document["items"]
            .as_array_mut()
            .unwrap()
            .sort_by_key(|item| item["id"].as_i64().unwrap()),
        9 => {
            let items = document["items"].as_array_mut().unwrap();
            if !items.is_empty() {
                let at = index(value, items.len());
                items[at]["score"] = j!(value);
            }
        }
        10 => {
            let meta = &mut document["meta"];
            meta["revision"] = j!(meta["revision"].as_i64().unwrap() + 1);
            meta["label"] = j!(format!("revision-{value}"));
        }
        11 => {
            document["meta"]
                .as_object_mut()
                .unwrap()
                .shift_remove("label");
        }
        12 => {
            let items = document["items"].as_array_mut().unwrap();
            if items.len() > 1 {
                items[1] = items[0].clone();
            }
        }
        _ => {
            let items = document["items"].as_array_mut().unwrap();
            for slot in items.iter_mut().take(2) {
                *slot = item(value);
            }
        }
    }
}

fn text(document: &Draft) -> Result<String, TrackerError> {
    let item = document.get("text")?.unwrap();
    Ok(item
        .as_value()
        .and_then(JsonValue::as_str)
        .unwrap()
        .to_owned())
}

fn number(item: &DraftItem, key: &str) -> Result<f64, TrackerError> {
    let field = item.as_draft().unwrap().get(key)?.unwrap();
    Ok(field.as_value().and_then(JsonValue::as_f64).unwrap())
}

fn mutate_draft(document: &Draft, choice: u64, value: i64) -> Result<(), TrackerError> {
    let items = document.child("items")?;
    let placed = || json(item(value));
    match choice {
        0 => document.set("text", format!("{}-{value}", text(document)?))?,
        1 => {
            let current = text(document)?;
            let skipped = utf16_skip(&current, utf16_len(&current).min(2));
            document.set("text", format!("{skipped}{value}"))?;
        }
        2 => {
            items.push([placed()])?;
        }
        3 => {
            items.unshift([placed()])?;
        }
        4 => {
            if !items.is_empty()? {
                items.shift()?;
            }
        }
        5 => {
            if !items.is_empty()? {
                items.pop()?;
            }
        }
        6 => {
            let length = items.len()?;
            let at = if length == 0 {
                0
            } else {
                index(value, length + 1)
            };
            let remove = if length == 0 { 0 } else { index(value, 2) };
            items.splice(
                i64::try_from(at).unwrap(),
                i64::try_from(remove).unwrap(),
                [placed()],
            )?;
        }
        7 => {
            items.reverse()?;
        }
        8 => {
            items.sort_by(|left, right| {
                let left = number(left, "id").unwrap();
                let right = number(right, "id").unwrap();
                (left - right).total_cmp(&0.0)
            })?;
        }
        9 => {
            let length = items.len()?;
            if length > 0 {
                items
                    .child(index(value, length))?
                    .set("score", JsonValue::try_from(value).unwrap())?;
            }
        }
        10 => {
            let meta = document.child("meta")?;
            let revision = meta.get("revision")?.unwrap();
            let next = revision.as_value().and_then(JsonValue::as_f64).unwrap() + 1.0;
            meta.set("revision", JsonValue::try_from(next).unwrap())?;
            meta.set("label", format!("revision-{value}"))?;
        }
        11 => document.child("meta")?.delete("label")?,
        12 => {
            if items.len()? > 1 {
                items.set(1, copy_json(&items.child(0)?.value()?))?;
            }
        }
        _ => {
            for at in 0..items.len()?.min(2) {
                items.set(at, placed())?;
            }
        }
    }
    Ok(())
}

/// Panic when two container slots share one allocation (`expectAliasFree`).
fn expect_alias_free(value: &JsonValue) {
    fn visit(current: &JsonValue, path: &str, seen: &mut HashMap<*const (), String>) {
        let pointer = match current {
            JsonValue::Array(items) => Arc::as_ptr(items).cast::<()>(),
            JsonValue::Object(object) => Arc::as_ptr(object).cast::<()>(),
            JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::String(_) => {
                return
            }
        };
        if let Some(previous) = seen.get(&pointer) {
            panic!("container at {path} aliases {previous}");
        }
        seen.insert(pointer, path.to_owned());
        match current {
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
            JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::String(_) => {}
        }
    }
    visit(value, "$root", &mut HashMap::new());
}

#[test]
fn converges_across_randomized_prepared_revisions() {
    for seed in 1..=100 {
        let mut rng = Random(seed);
        let items: Vec<_> = (0..4)
            .map(|id| j!({ "id": id, "text": format!("item-{id}"), "score": 0 }))
            .collect();
        let initial = json(j!({ "items": items, "text": "start", "meta": { "revision": 0 } }));
        let tracker = track(initial.clone()).unwrap();
        let mut expected = serde_json::Value::from(&copy_json(&initial));
        let mut replica = copy_json(&tracker.value());
        for step in 0..100 {
            let choice = rng.below(14);
            let value = i64::from(seed) * 1_000 + step;
            let context = format!("seed {seed} step {step} choice {choice}");
            let base_root = tracker.value();
            let base = copy_json(&base_root);
            mutate_expected(&mut expected, choice, value);
            let change = tracker.begin_change();
            mutate_draft(&change.state().unwrap(), choice, value).unwrap();
            let prepared = change.prepare().unwrap();
            let wire = JsonValue::parse(&ops_json(prepared.ops()).to_string()).unwrap();
            let operations: Vec<Op> = wire
                .as_array()
                .unwrap()
                .iter()
                .map(|op| Op::from_json(op).unwrap())
                .collect();
            assert_eq!(base_root, base, "prepare base {context}");
            assert!(prepared.base().strict_equals(&base_root), "{context}");
            replica = apply_immutable(&replica, &operations).unwrap();
            assert_eq!(&replica, prepared.value(), "replay {context}");
            tracker.adopt(&prepared).unwrap();
            assert_eq!(base_root, base, "adopt base {context}");
            assert!(tracker.value().strict_equals(prepared.value()), "{context}");
            let expected_value = json(expected.clone());
            assert_eq!(tracker.value(), expected_value, "state {context}");
            assert_eq!(replica, expected_value, "replica {context}");
            expect_alias_free(&tracker.value());
        }
    }
}
