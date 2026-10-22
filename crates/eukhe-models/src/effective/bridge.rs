//! The bridge between the effective catalog and its Bend model
//! (`bend/catalog_union.bend`, whose laws `LAWS.bend` section `catalog_union` and
//! `PROOF.bend` prove): both run the same generated catalogs and must
//! print the same union, byte for byte. `bend/bridge_catalog_union.bend`
//! documents the scenario format.
//!
//! An entry of the model is a key, an api, the data the bundle always
//! states and one optional field. Here the key is a `(provider, id)`, the
//! api a wire API, the data every required field at once (`name`,
//! `baseUrl`, `reasoning`, `cost`, `contextWindow`, `maxTokens`), and each
//! scenario puts its values in one optional field of the four, so each
//! field follows the model's rule on its own.
//!
//! [`compare`] runs them (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::JsNumber;
use serde_json::{json, Value};

use super::effective_catalog;
use crate::Model;

const PROVIDERS: [&str; 2] = ["anthropic", "openai"];
const APIS: [&str; 2] = ["anthropic-messages", "openai-completions"];

/// The optional field a scenario puts its values in.
#[derive(Debug, Clone, Copy)]
enum Field {
    ThinkingLevelMap,
    Compat,
    Featured,
    Headers,
}

impl Field {
    const ALL: [Field; 4] = [
        Field::ThinkingLevelMap,
        Field::Compat,
        Field::Featured,
        Field::Headers,
    ];

    /// The largest value the field holds (`featured` is a bool: 1 false,
    /// 2 true).
    fn top(self) -> u64 {
        match self {
            Field::ThinkingLevelMap | Field::Compat | Field::Headers => 9,
            Field::Featured => 2,
        }
    }

    /// The field's JSON key and the value `v` in its form.
    fn json(self, v: u64) -> (&'static str, Value) {
        match self {
            Field::ThinkingLevelMap => ("thinkingLevelMap", json!({ "high": format!("v{v}") })),
            Field::Compat => ("compat", json!({ "v": v })),
            Field::Featured => ("featured", json!(v == 2)),
            Field::Headers => ("headers", json!({ "x-v": v.to_string() })),
        }
    }

    /// The value the field of `model` holds (0: none; `?`: a shape no
    /// entry was given).
    fn read(self, model: &Model) -> String {
        let value = match self {
            Field::ThinkingLevelMap => model.thinking_level_map.as_ref().map(|map| json!(map)),
            Field::Compat => model.compat.as_ref().map(|compat| json!(compat)),
            Field::Featured => model.featured.map(|featured| json!(featured)),
            Field::Headers => model.headers.as_ref().map(|headers| json!(headers)),
        };
        let Some(value) = value else {
            return "0".into();
        };
        (1..=self.top())
            .find(|v| self.json(*v).1 == value)
            .map_or_else(|| "?".into(), |v| v.to_string())
    }
}

/// One entry as the model reads it.
#[derive(Clone, Copy)]
struct Entry {
    key: u64,
    api: u64,
    data: u32,
    opt: u64,
}

impl Entry {
    fn model(self, field: Field) -> Model {
        let mut value = json!({
            "id": format!("m{}", self.key / 2),
            "provider": PROVIDERS[usize::from(self.key % 2 == 1)],
            "name": format!("d{}", self.data),
            "api": APIS[usize::from(self.api == 1)],
            "baseUrl": format!("https://d{}.test", self.data),
            "reasoning": self.data % 2 == 1,
            "input": ["text"],
            "cost": {"input": self.data, "output": 0, "cacheRead": 0, "cacheWrite": 0},
            "contextWindow": self.data,
            "maxTokens": self.data,
        });
        if self.opt > 0 {
            let (name, opt) = field.json(self.opt);
            value[name] = opt;
        }
        serde_json::from_value(value).expect("a registry model")
    }
}

/// The model's line for one entry of the union: `m K A D O` (`?` for a
/// part that is no entry's).
fn line(model: &Model, field: Field) -> String {
    let key = PROVIDERS
        .iter()
        .position(|provider| *provider == model.provider)
        .zip(
            model
                .id
                .strip_prefix('m')
                .and_then(|id| id.parse::<usize>().ok()),
        )
        .map_or_else(|| "?".into(), |(odd, half)| (half * 2 + odd).to_string());
    let api = APIS
        .iter()
        .position(|api| *api == model.api)
        .map_or_else(|| "?".into(), |api| api.to_string());
    let data = model
        .name
        .strip_prefix('d')
        .and_then(|data| data.parse::<u32>().ok())
        .filter(|data| {
            model.base_url == format!("https://d{data}.test")
                && model.reasoning == (data % 2 == 1)
                && model.cost.input == JsNumber(f64::from(*data))
                && model.context_window == u64::from(*data)
                && model.max_tokens == u64::from(*data)
        })
        .map_or_else(|| "?".into(), |data| data.to_string());
    format!("m {key} {api} {data} {}\n", field.read(model))
}

/// A source of `rng`'s choosing: distinct keys below 8, in any order,
/// two apis, small data, and the optional field set about half the time.
fn source(rng: &mut Rng, field: Field) -> Vec<Entry> {
    let mut keys: Vec<u64> = (0..8).filter(|_| rng.chance(50)).collect();
    for at in (1..keys.len()).rev() {
        let bound = u64::try_from(at + 1).expect("a bound");
        let other = usize::try_from(rng.below(bound)).expect("an index");
        keys.swap(at, other);
    }
    keys.into_iter()
        .map(|key| Entry {
            key,
            api: rng.below(2),
            data: u32::try_from(rng.range(0, 40)).expect("small data"),
            opt: if rng.chance(50) {
                rng.range(1, field.top())
            } else {
                0
            },
        })
        .collect()
}

/// The union bridge: generated bundled and compiled catalogs, read in
/// either order with their lines interleaved; the union each makes.
#[test]
fn the_rust_union_equals_the_bend_model() {
    let mut rng = Rng(0x00c4_7a10_9d1e_5eed);
    let mut scenarios = Vec::new();
    for case in 0..240 {
        let field = Field::ALL[case % Field::ALL.len()];
        let bundled = source(&mut rng, field);
        let compiled = source(&mut rng, field);
        let (mut bundled_rest, mut compiled_rest) = (bundled.iter(), compiled.iter());
        let (mut bundled_next, mut compiled_next) = (bundled_rest.next(), compiled_rest.next());
        let mut events = String::new();
        loop {
            let take_bundled = match (bundled_next, compiled_next) {
                (None, None) => break,
                (Some(_), None) => true,
                (None, Some(_)) => false,
                (Some(_), Some(_)) => rng.chance(50),
            };
            let (tag, entry) = if take_bundled {
                ('b', bundled_next.expect("a bundled entry"))
            } else {
                ('c', compiled_next.expect("a compiled entry"))
            };
            writeln!(
                events,
                "{tag} {} {} {} {}",
                entry.key, entry.api, entry.data, entry.opt
            )
            .expect("write to a string");
            if take_bundled {
                bundled_next = bundled_rest.next();
            } else {
                compiled_next = compiled_rest.next();
            }
        }
        let compiled_models: Vec<Model> = compiled.iter().map(|entry| entry.model(field)).collect();
        let union = effective_catalog(
            bundled.iter().map(|entry| entry.model(field)).collect(),
            &compiled_models,
        );
        let transcript = union.iter().map(|model| line(model, field)).collect();
        scenarios.push(Scenario {
            name: format!("{case}-{field:?}"),
            events,
            transcript,
        });
    }
    compare("bend/bridge_catalog_union.bend", scenarios);
}
