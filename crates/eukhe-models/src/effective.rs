//! The effective catalog: the union of the bundled snapshot and the
//! compiled catalog.
//!
//! A model is its `(provider, id)`. The effective catalog has every model
//! of either source, so neither source can hide a model the other has. A
//! model in both sources takes each field from one stated source:
//!
//! - the bundled entry wins every field it states: its route (`api`,
//!   `baseUrl`), its data (`name`, `reasoning`, `input`, `cost`,
//!   `contextWindow`, `maxTokens`) and each optional field it carries;
//! - the compiled entry fills each optional field the bundled entry
//!   leaves out (`thinkingLevelMap`, `compat`, `featured`, `headers`),
//!   but only when both entries use the same `api` (these fields are
//!   shaped by the wire API).
//!
//! A model that only one source has comes from that source unchanged. The
//! order: the bundled entries in bundled order, then the compiled models
//! the bundle lacks, in compiled order. Each model's fields depend only on
//! its entry in each source, so the result does not depend on the order
//! the sources are read. `laws/catalog_union.bend` states these
//! rules over `bend/catalog_union.bend`; the rule is one pure call
//! ([`union`]) over the sources projected to [`Ent`]s, and the models are
//! assembled back from what it answers.

use std::collections::HashMap;

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{call, expect_core, Entry, Error};

use crate::Model;

/// The optional fields, in the order of [`Ent::opts`] (the model's `Fld`).
const FIELDS: usize = 4;

/// One entry of a source as the rule reads it (the model's `Ent`): the
/// key and the api interned, `data` the entry's place (a bundled entry's
/// index, or the bundle's length plus a compiled entry's index), and each
/// optional field the place of the entry it comes from, when stated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Ent {
    key: usize,
    api: usize,
    data: usize,
    opts: [Option<usize>; FIELDS],
}

/// The union of the projected bundle `bs` and compiled catalog `cs`
/// (`fast` in `bend/catalog_union.bend`, which law `union_fast` pins to the
/// rule `union`), run as the compiled Bend core: an entry crosses as seven
/// Nats (key, api, data, then each field: 0 none, 1 + v the place v).
fn union(bs: &[Ent], cs: &[Ent]) -> Result<Vec<Ent>, Error> {
    let mut writer = Writer::new();
    for ents in [bs, cs] {
        writer.count(ents.len() * 7);
        for ent in ents {
            for n in [ent.key, ent.api, ent.data] {
                writer.count(n);
            }
            for field in ent.opts {
                writer.count(field.map_or(0, |place| place + 1));
            }
        }
    }
    let reply = call(Entry::CatalogUnion, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let count = reader.count()?;
    let mut nats = Vec::with_capacity(count);
    for _ in 0..count {
        nats.push(reader.count()?);
    }
    reader.end()?;
    let (ents, left) = nats.as_chunks::<7>();
    if !left.is_empty() {
        return Err(Error::Wire(WireError::Malformed {
            at: reply.len(),
            expected: "seven Nats per entry",
        }));
    }
    Ok(ents
        .iter()
        .map(|&[key, api, data, tlm, compat, featured, headers]| Ent {
            key,
            api,
            data,
            opts: [tlm, compat, featured, headers].map(|n| n.checked_sub(1)),
        })
        .collect())
}

/// The interned id of `value` in `table` (a new one the first time).
fn intern<'a>(table: &mut HashMap<&'a str, usize>, value: &'a str) -> usize {
    let next = table.len();
    *table.entry(value).or_insert(next)
}

/// The places of `model`'s optional fields that it states (`place` is its
/// own place).
fn stated(model: &Model, place: usize) -> [Option<usize>; FIELDS] {
    [
        model.thinking_level_map.is_some().then_some(place),
        model.compat.is_some().then_some(place),
        model.featured.is_some().then_some(place),
        model.headers.is_some().then_some(place),
    ]
}

/// `model` as the rule reads it, at `place`.
fn project<'a>(
    keys: &mut HashMap<(&'a str, &'a str), usize>,
    apis: &mut HashMap<&'a str, usize>,
    model: &'a Model,
    place: usize,
) -> Ent {
    let next = keys.len();
    let key = *keys
        .entry((model.provider.as_str(), model.id.as_str()))
        .or_insert(next);
    Ent {
        key,
        api: intern(apis, model.api.as_str()),
        data: place,
        opts: stated(model, place),
    }
}

/// The model at `place`: a bundled one not yet taken from `owned`, or a
/// compiled one (`owned.len()` and on).
fn source<'a>(
    compiled: &'a [Model],
    owned: &'a [Option<Model>],
    place: usize,
) -> Option<&'a Model> {
    match place.checked_sub(owned.len()) {
        Some(index) => compiled.get(index),
        None => owned.get(place).and_then(Option::as_ref),
    }
}

/// The effective catalog of `bundled` (pinned) and `compiled` (see the
/// module docs for the precedence of each field).
#[must_use]
pub fn effective_catalog(bundled: Vec<Model>, compiled: &[Model]) -> Vec<Model> {
    expect_core(Entry::CatalogUnion, assemble(bundled, compiled))
}

/// The union of the sources, projected, decided by the core and assembled
/// back into models.
fn assemble(bundled: Vec<Model>, compiled: &[Model]) -> Result<Vec<Model>, Error> {
    let base = bundled.len();
    let (bs, cs) = {
        let mut keys: HashMap<(&str, &str), usize> = HashMap::new();
        let mut apis: HashMap<&str, usize> = HashMap::new();
        let bs: Vec<Ent> = bundled
            .iter()
            .enumerate()
            .map(|(index, model)| project(&mut keys, &mut apis, model, index))
            .collect();
        let cs: Vec<Ent> = compiled
            .iter()
            .enumerate()
            .map(|(index, model)| project(&mut keys, &mut apis, model, base + index))
            .collect();
        (bs, cs)
    };
    let picked = union(&bs, &cs)?;
    let mut owned: Vec<Option<Model>> = bundled.into_iter().map(Some).collect();
    let mut models = Vec::with_capacity(picked.len());
    for ent in picked {
        let [thinking, compat, featured, headers] = ent
            .opts
            .map(|place| place.and_then(|place| source(compiled, &owned, place)));
        let thinking_level_map = thinking.and_then(|model| model.thinking_level_map.clone());
        let compat = compat.and_then(|model| model.compat.clone());
        let featured = featured.and_then(|model| model.featured);
        let headers = headers.and_then(|model| model.headers.clone());
        let model = match ent.data.checked_sub(base) {
            Some(index) => compiled.get(index).cloned(),
            None => owned.get_mut(ent.data).and_then(Option::take),
        };
        // The union answers each entry of its sources once, at its place
        // (laws/catalog_union.bend).
        let Some(mut model) = model else {
            return Err(Error::Wire(WireError::Malformed {
                at: 0,
                expected: "the place of an entry not yet taken",
            }));
        };
        model.thinking_level_map = thinking_level_map;
        model.compat = compat;
        model.featured = featured;
        model.headers = headers;
        models.push(model);
    }
    Ok(models)
}
