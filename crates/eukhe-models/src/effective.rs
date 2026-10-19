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
//! the sources are read. `laws/catalog_union.bend` states these rules;
//! `bend/bridge_catalog_union.bend` runs its model against this code.

use std::collections::{HashMap, HashSet};

use crate::Model;

/// The effective catalog of `bundled` (pinned) and `compiled` (see the
/// module docs for the precedence of each field).
#[must_use]
pub fn effective_catalog(bundled: Vec<Model>, compiled: &[Model]) -> Vec<Model> {
    let mut compiled_by_key: HashMap<(&str, &str), &Model> = HashMap::with_capacity(compiled.len());
    for model in compiled {
        compiled_by_key
            .entry((model.provider.as_str(), model.id.as_str()))
            .or_insert(model);
    }
    let bundled_keys: HashSet<(&str, &str)> = bundled
        .iter()
        .map(|model| (model.provider.as_str(), model.id.as_str()))
        .collect();
    let compiled_only: Vec<&Model> = compiled
        .iter()
        .filter(|model| !bundled_keys.contains(&(model.provider.as_str(), model.id.as_str())))
        .collect();
    drop(bundled_keys);
    let mut models = Vec::with_capacity(bundled.len() + compiled_only.len());
    for mut model in bundled {
        if let Some(twin) = compiled_by_key.get(&(model.provider.as_str(), model.id.as_str())) {
            if twin.api == model.api {
                if model.thinking_level_map.is_none() {
                    model
                        .thinking_level_map
                        .clone_from(&twin.thinking_level_map);
                }
                if model.compat.is_none() {
                    model.compat.clone_from(&twin.compat);
                }
                if model.featured.is_none() {
                    model.featured = twin.featured;
                }
                if model.headers.is_none() {
                    model.headers.clone_from(&twin.headers);
                }
            }
        }
        models.push(model);
    }
    models.extend(compiled_only.into_iter().cloned());
    models
}

#[cfg(test)]
mod bridge;
