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
//! the sources are read. `LAWS.bend` section `catalog_union` states these
//! rules over `bend/catalog_union.bend`; the rule is one pure call
//! ([`union`]) over the sources projected to [`Ent`]s, and the models are
//! assembled back from what it answers.

use std::collections::{HashMap, HashSet};

use crate::Model;

/// The optional fields, in the order of [`Ent::opts`] (the model's `Fld`).
const FIELDS: usize = 4;

/// One entry of a source as the rule reads it (the model's `Ent`): the
/// key and the api interned, `data` the entry's place (a bundled entry's
/// index, or the bundle's length plus a compiled entry's index), and each
/// optional field the place of the entry it comes from, when stated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Ent {
    pub(crate) key: usize,
    pub(crate) api: usize,
    pub(crate) data: usize,
    pub(crate) opts: [Option<usize>; FIELDS],
}

/// The union of the projected bundle `bs` and compiled catalog `cs`
/// (`fast` in `bend/catalog_union.bend`, which law `union_fast` pins to
/// the rule `union`).
pub(crate) fn union(bs: &[Ent], cs: &[Ent]) -> Vec<Ent> {
    let mut twins: HashMap<usize, &Ent> = HashMap::with_capacity(cs.len());
    for c in cs {
        twins.entry(c.key).or_insert(c);
    }
    let bundled: HashSet<usize> = bs.iter().map(|b| b.key).collect();
    let mut out = Vec::with_capacity(bs.len() + cs.len());
    for b in bs {
        let mut merged = *b;
        if let Some(twin) = twins.get(&b.key).filter(|twin| twin.api == b.api) {
            for (field, twin_field) in merged.opts.iter_mut().zip(twin.opts) {
                if field.is_none() {
                    *field = twin_field;
                }
            }
        }
        out.push(merged);
    }
    out.extend(cs.iter().filter(|c| !bundled.contains(&c.key)).copied());
    out
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
    let picked = union(&bs, &cs);
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
        let Some(mut model) = model else {
            unreachable!("the union answers each entry of its sources once, at its place");
        };
        model.thinking_level_map = thinking_level_map;
        model.compat = compat;
        model.featured = featured;
        model.headers = headers;
        models.push(model);
    }
    models
}

#[cfg(test)]
mod bridge;
