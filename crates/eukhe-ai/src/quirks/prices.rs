//! The prices that a catalog row does not carry, as two rulebook tables:
//! `service_tier_prices` (the cost multiplier of a service tier) and
//! `cache_write_1h_prices` (the price of a cache write that lives 1 hour).
//! A model that no row prices keeps the prices of its catalog row.

use std::collections::HashSet;

use regex::Regex;
use serde::de::Error as _;
use serde::{Deserialize, Deserializer};

use super::{ModelKey, Rulebook};

/// One row of `service_tier_prices`: a response of `provider` over the
/// wire API `api` whose service tier (the `service_tier` of the response,
/// else of the request) is one of `tiers` costs `multiplier` times the base
/// price. A row that names `model` (an exact model id) applies only to that
/// model, and it wins over the row without a model.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct TierPriceRow {
    provider: String,
    api: String,
    #[serde(default)]
    model: Option<String>,
    tiers: Vec<String>,
    multiplier: f64,
}

/// The `service_tier_prices` table. At most one row prices a tier for one
/// provider, API and model (or no model); each multiplier is finite and not
/// negative.
#[derive(Debug, Default)]
pub(super) struct TierPrices(Vec<TierPriceRow>);

impl<'de> Deserialize<'de> for TierPrices {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let rows = Vec::<TierPriceRow>::deserialize(deserializer)?;
        let mut priced = HashSet::new();
        for row in &rows {
            if !row.multiplier.is_finite() || row.multiplier < 0.0 {
                return Err(D::Error::custom(format!(
                    "service_tier_prices: the multiplier {} of {}/{} is not a price",
                    row.multiplier, row.provider, row.api
                )));
            }
            for tier in &row.tiers {
                if !priced.insert((&row.provider, &row.api, &row.model, tier)) {
                    return Err(D::Error::custom(format!(
                        "service_tier_prices: two rows price tier `{tier}` of {}/{} (model {:?})",
                        row.provider, row.api, row.model
                    )));
                }
            }
        }
        Ok(Self(rows))
    }
}

/// The multiplier of the shipped `service_tier_prices` row that prices
/// `tier` for `model` ([`TierPriceRow`]): the row of the model's provider,
/// API and id, else the row of its provider and API without a model.
/// `None` when no row prices the tier: the cost stays the base price.
#[must_use]
pub fn service_tier_multiplier(model: ModelKey<'_>, tier: &str) -> Option<f64> {
    let mut provider_wide = None;
    for row in Rulebook::shipped()
        .service_tier_prices
        .0
        .iter()
        .filter(|row| {
            row.provider == model.provider
                && row.api == model.api
                && row.tiers.iter().any(|priced| priced == tier)
        })
    {
        match &row.model {
            Some(id) if id == model.id => return Some(row.multiplier),
            Some(_) => {}
            None => provider_wide = Some(row.multiplier),
        }
    }
    provider_wide
}

/// One row of `cache_write_1h_prices` as the rulebook writes it.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct LongWriteEntry {
    #[serde(rename = "match")]
    pattern: String,
    input_multiplier: f64,
}

/// One row of `cache_write_1h_prices`: a 1h cache write of a model whose
/// lowercased id `pattern` matches costs `input_multiplier` times the
/// model's input rate.
#[derive(Debug)]
struct LongWriteRow {
    pattern: Regex,
    input_multiplier: f64,
}

/// The `cache_write_1h_prices` table, in rulebook order: the first row
/// that matches a model prices its 1h cache writes. Each pattern is a
/// regex; each multiplier is finite and not negative.
#[derive(Debug, Default)]
pub(super) struct LongWritePrices(Vec<LongWriteRow>);

impl<'de> Deserialize<'de> for LongWritePrices {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Vec::<LongWriteEntry>::deserialize(deserializer)?
            .into_iter()
            .map(|entry| {
                if !entry.input_multiplier.is_finite() || entry.input_multiplier < 0.0 {
                    return Err(D::Error::custom(format!(
                        "cache_write_1h_prices: the multiplier {} of `{}` is not a price",
                        entry.input_multiplier, entry.pattern
                    )));
                }
                Regex::new(&entry.pattern)
                    .map(|pattern| LongWriteRow {
                        pattern,
                        input_multiplier: entry.input_multiplier,
                    })
                    .map_err(|error| D::Error::custom(format!("cache_write_1h_prices: {error}")))
            })
            .collect::<Result<_, _>>()
            .map(Self)
    }
}

/// The multiplier of the input rate that a 1h cache write of the model
/// with id `model_id` costs: the first shipped `cache_write_1h_prices` row
/// that matches the lowercased id ([`LongWriteRow`]). `None` when no row
/// matches: a 1h cache write costs the model's own cache write rate.
#[must_use]
pub fn cache_write_1h_multiplier(model_id: &str) -> Option<f64> {
    let lower_id = model_id.to_lowercase();
    Rulebook::shipped()
        .cache_write_1h_prices
        .0
        .iter()
        .find(|row| row.pattern.is_match(&lower_id))
        .map(|row| row.input_multiplier)
}

#[cfg(test)]
mod tests;
