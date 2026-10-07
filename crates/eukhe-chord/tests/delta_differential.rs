//! Replays draft-operation sequences recorded from the TS tracker
//! (`@earendil-works/chord` v1.0.4) and asserts identical reads, errors, op
//! batches (byte-exact JSON), and values (byte-exact JSON, key order
//! included). The fixture holds 50 seeded random cases (random JSON roots,
//! 1–3 transactions of mixed object writes and deletes, string rewrites,
//! every array mutator, sorts, held handles, and draft placements).

use std::cmp::Ordering;

use eukhe_chord::delta::{track, Draft, DraftItem, Op, Placement, Seg};
use eukhe_chord::json::JsonValue;

const FIXTURE: &str = include_str!("fixtures/tracker_differential.json");

fn seg(value: &JsonValue) -> Seg {
    match value {
        JsonValue::String(key) => Seg::Key(key.clone()),
        other => {
            Seg::Index(usize::try_from(other.as_u64().expect("index segment")).expect("index"))
        }
    }
}

fn int(value: &JsonValue) -> i64 {
    value.as_i64().expect("integer argument")
}

fn optional_int(value: &JsonValue) -> i64 {
    if value.is_null() {
        i64::MAX
    } else {
        int(value)
    }
}

fn show(item: Option<DraftItem>) -> JsonValue {
    match item {
        None => JsonValue::from("undefined"),
        Some(item) => JsonValue::from(item.to_value().expect("readable").to_string()),
    }
}

struct Replay {
    state: Draft,
    held: Vec<Option<Draft>>,
}

impl Replay {
    fn navigate(&self, path: &JsonValue) -> Result<Draft, String> {
        let mut handle = self.state.clone();
        for segment in path.as_array().expect("path") {
            handle = match handle
                .get(seg(segment))
                .map_err(|error| error.to_string())?
            {
                Some(DraftItem::Draft(child)) => child,
                _ => return Err("hold of non-container".to_owned()),
            };
        }
        Ok(handle)
    }

    fn resolve(&self, target: &JsonValue) -> Result<Draft, String> {
        if let Some(id) = target.get("held") {
            let id = usize::try_from(id.as_u64().expect("held id")).expect("held id");
            return self.held[id]
                .clone()
                .ok_or_else(|| "missing held handle".to_owned());
        }
        self.navigate(&target["path"])
    }

    fn placement(&self, value: &JsonValue) -> Result<Placement, String> {
        if let Some(json) = value.get("json") {
            return Ok(Placement::Value(json.clone()));
        }
        Ok(Placement::Draft(self.resolve(&value["draft"])?))
    }

    fn placements(&self, items: &JsonValue) -> Result<Vec<Placement>, String> {
        items
            .as_array()
            .expect("items")
            .iter()
            .map(|item| self.placement(item))
            .collect()
    }

    #[allow(clippy::too_many_lines)] // one arm per recorded operation kind
    fn apply(&mut self, op: &JsonValue) -> Result<JsonValue, String> {
        let kind = op["op"].as_str().expect("op kind");
        match kind {
            "hold" => {
                let handle = self.navigate(&op["path"])?;
                self.store(op, handle);
                return Ok(JsonValue::Null);
            }
            "holdIndex" => {
                let from = self.resolve(&op["from"])?;
                let handle = from
                    .child(seg(&op["index"]))
                    .map_err(|error| error.to_string())?;
                self.store(op, handle);
                return Ok(JsonValue::Null);
            }
            _ => {}
        }
        let handle = self.resolve(&op["target"])?;
        let error = |error: eukhe_chord::delta::TrackerError| error.to_string();
        Ok(match kind {
            "set" => {
                let placement = self.placement(&op["value"])?;
                handle.set(seg(&op["key"]), placement).map_err(error)?;
                JsonValue::Null
            }
            "del" => {
                handle.delete(seg(&op["key"])).map_err(error)?;
                JsonValue::Null
            }
            "text" => {
                let key = seg(&op["key"]);
                let current = handle.get(key.clone()).map_err(error)?;
                let current = current
                    .and_then(|item| item.as_value().and_then(|v| v.as_str().map(str::to_owned)));
                let current = current.expect("text value");
                let n = usize::try_from(op["n"].as_u64().expect("n")).expect("n");
                let suffix = op["suffix"].as_str().expect("suffix");
                let skipped: String = current.chars().skip(n).collect();
                let next = match op["mode"].as_str().expect("mode") {
                    "append" => format!("{current}{suffix}"),
                    "rotate" => format!("{skipped}{suffix}"),
                    "trunc" => skipped,
                    _ => suffix.to_owned(),
                };
                handle.set(key, next).map_err(error)?;
                JsonValue::Null
            }
            "keys" => JsonValue::from(handle.keys().map_err(error)?),
            "get" => show(handle.get(seg(&op["key"])).map_err(error)?),
            "has" => JsonValue::Bool(handle.has(seg(&op["key"])).map_err(error)?),
            "push" => {
                let items = self.placements(&op["items"])?;
                JsonValue::try_from(handle.push(items).map_err(error)?).expect("length")
            }
            "pop" => show(handle.pop().map_err(error)?),
            "shift" => show(handle.shift().map_err(error)?),
            "unshift" => {
                let items = self.placements(&op["items"])?;
                JsonValue::try_from(handle.unshift(items).map_err(error)?).expect("length")
            }
            "splice" => {
                let items = if op["del"].is_null() {
                    Vec::new()
                } else {
                    self.placements(&op["items"])?
                };
                let removed = handle
                    .splice(int(&op["start"]), optional_int(&op["del"]), items)
                    .map_err(error)?;
                let values: Vec<JsonValue> = removed
                    .iter()
                    .map(|item| item.to_value().expect("readable"))
                    .collect();
                JsonValue::from(JsonValue::from(values).to_string())
            }
            "reverse" => {
                handle.reverse().map_err(error)?;
                JsonValue::Null
            }
            "sort" => {
                handle.sort().map_err(error)?;
                JsonValue::Null
            }
            "sortBy" => {
                let key_of = |item: &DraftItem| -> f64 {
                    match item {
                        DraftItem::Value(value) => value.as_f64().unwrap_or(0.0),
                        DraftItem::Draft(draft) if !draft.is_array() => match draft.get("id") {
                            Ok(Some(DraftItem::Value(JsonValue::Number(number)))) => number.get(),
                            _ => 0.0,
                        },
                        DraftItem::Draft(_) => 0.0,
                    }
                };
                handle
                    .sort_by(|left, right| {
                        key_of(left)
                            .partial_cmp(&key_of(right))
                            .unwrap_or(Ordering::Equal)
                    })
                    .map_err(error)?;
                JsonValue::Null
            }
            "fill" => {
                let placement = self.placement(&op["value"])?;
                handle
                    .fill(placement, int(&op["start"]), optional_int(&op["end"]))
                    .map_err(error)?;
                JsonValue::Null
            }
            "copyWithin" => {
                handle
                    .copy_within(int(&op["t"]), int(&op["s"]), optional_int(&op["e"]))
                    .map_err(error)?;
                JsonValue::Null
            }
            "len" => {
                let length = usize::try_from(op["n"].as_u64().expect("n")).expect("n");
                handle.set_len(length).map_err(error)?;
                JsonValue::Null
            }
            other => panic!("unknown op {other}"),
        })
    }

    fn store(&mut self, op: &JsonValue, handle: Draft) {
        let id = usize::try_from(op["id"].as_u64().expect("id")).expect("id");
        if self.held.len() <= id {
            self.held.resize(id + 1, None);
        }
        self.held[id] = Some(handle);
    }
}

fn ops_json(ops: &[Op]) -> String {
    JsonValue::from(ops.iter().map(Op::to_json).collect::<Vec<_>>()).to_string()
}

fn replay_cases(cases: &JsonValue) -> usize {
    let mut count = 0;
    for case in cases.as_array().expect("cases") {
        let seed = &case["seed"];
        let initial =
            JsonValue::parse(case["initial"].as_str().expect("initial")).expect("initial json");
        let tracker = track(initial).expect("container root");
        for (index, transaction) in case["transactions"]
            .as_array()
            .expect("transactions")
            .iter()
            .enumerate()
        {
            let change = tracker.begin_change();
            let mut replay = Replay {
                state: change.state().expect("open"),
                held: Vec::new(),
            };
            for op in transaction["operations"].as_array().expect("operations") {
                let actual = match replay.apply(op) {
                    Ok(value) => value,
                    Err(message) => {
                        let mut object = eukhe_chord::json::JsonObject::new();
                        object.insert("error", JsonValue::from(message));
                        JsonValue::from(object)
                    }
                };
                assert_eq!(
                    actual, op["result"],
                    "seed {seed} transaction {index} op {op}"
                );
            }
            let prepared = change.prepare().expect("prepare");
            assert_eq!(
                ops_json(prepared.ops()),
                transaction["ops"].as_str().expect("ops"),
                "seed {seed} transaction {index} ops"
            );
            assert_eq!(
                prepared.value().to_string(),
                transaction["value"].as_str().expect("value"),
                "seed {seed} transaction {index} value"
            );
            tracker.adopt(&prepared).expect("adopt");
        }
        count += 1;
    }
    count
}

#[test]
fn replays_ts_tracker_recordings() {
    let cases = JsonValue::parse(FIXTURE).expect("fixture json");
    assert_eq!(replay_cases(&cases), 50);
}
