//! The worst case of a model request before it is sent, and what it
//! actually spent after it returned (spec/README.md B1, B3).
//!
//! A provider's charge is known only after the response: it is at most the
//! request's input tokens at the model's highest input-side price plus the
//! output cap at its highest output price. The ledger reserves that; the
//! settled amount is the cost the response's usage reports, rounded up to
//! a micro-dollar, so the ledger never charges less than the price table.

use eukhe_types::budget::{BudgetAmounts, BUDGET_AMOUNT_MAX};
use eukhe_types::pi_ai::{ModelCost, ModelCostRates, Usage};

/// The multiplier of the input price that bounds a 1h cache write (the
/// highest row of the rulebook's `cache_write_1h_prices`).
const LONG_CACHE_WRITE_MULTIPLIER: f64 = 2.0;

/// What bounds a model request before it is sent.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RequestBound {
    /// An upper bound of the request's input tokens: a tokenizer's count
    /// where one is available, else an estimate scaled up by the caller.
    pub input_tokens: u64,
    /// The request's output cap (`max_tokens`): the provider stops there.
    pub output_cap: u64,
    /// The price multiplier of the service tier the request asks for
    /// (1.0: the list price).
    pub price_multiplier: f64,
}

/// `dollars` in micro-dollars, rounded up, within a budget's range. A
/// negative or not-a-number cost is zero.
#[must_use]
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)] // The value is clamped to [0, BUDGET_AMOUNT_MAX], far below 2^53.
pub fn micros_ceil(dollars: f64) -> u64 {
    if dollars.is_nan() || dollars <= 0.0 {
        return 0;
    }
    let micros = (dollars * 1_000_000.0).ceil();
    if micros >= BUDGET_AMOUNT_MAX as f64 {
        BUDGET_AMOUNT_MAX
    } else {
        micros as u64
    }
}

fn input_rate(rates: ModelCostRates) -> f64 {
    rates
        .input
        .max(rates.cache_read)
        .max(rates.cache_write)
        .max(rates.input * LONG_CACHE_WRITE_MULTIPLIER)
}

/// The most the request can cost, in micro-dollars: every input token at
/// the highest input-side price of any pricing tier (plain input, cache
/// read, cache write, 1h cache write), the whole output cap at the highest
/// output price, times the service tier's multiplier (never below 1),
/// plus one micro-dollar: the price table's own sum of the same terms, in
/// another order of floating-point operations, never rounds past it.
#[must_use]
#[allow(clippy::cast_precision_loss)] // Token counts are far below 2^53.
pub fn worst_case_cost_micros(cost: &ModelCost, bound: RequestBound) -> u64 {
    let mut input = input_rate(cost.rates());
    let mut output = cost.output;
    for tier in cost.tiers.iter().flatten() {
        input = input.max(input_rate(tier.rates()));
        output = output.max(tier.output);
    }
    let multiplier = if bound.price_multiplier.is_nan() {
        1.0
    } else {
        bound.price_multiplier.max(1.0)
    };
    let dollars = (input * bound.input_tokens as f64 + output * bound.output_cap as f64)
        / 1_000_000.0
        * multiplier;
    micros_ceil(dollars)
        .saturating_add(1)
        .min(BUDGET_AMOUNT_MAX)
}

/// What a finished request spent: the cost its usage reports (rounded up
/// to a micro-dollar), every token the provider billed (input, output,
/// cache reads and writes), and the one request. It made no tool call;
/// time is the budget's deadline, not a spend.
#[must_use]
pub fn actual_spend(usage: &Usage) -> BudgetAmounts {
    let tokens = usage
        .input
        .saturating_add(usage.output)
        .saturating_add(usage.cache_read)
        .saturating_add(usage.cache_write);
    BudgetAmounts {
        cost_micros: micros_ceil(usage.cost.total),
        tokens: tokens.min(BUDGET_AMOUNT_MAX),
        time_ms: 0,
        tool_calls: 0,
        requests: 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::pi_ai::{ModelCostTier, UsageCost};

    fn cost() -> ModelCost {
        ModelCost {
            input: 3.0,
            output: 15.0,
            cache_read: 0.3,
            cache_write: 3.75,
            tiers: Some(vec![ModelCostTier {
                input: 6.0,
                output: 22.5,
                cache_read: 0.6,
                cache_write: 7.5,
                input_tokens_above: 200_000,
            }]),
        }
    }

    /// The cost `eukhe_ai::models::calculate_cost` computes for `usage`
    /// at `rates` (its formula, restated: the reference the bound is
    /// tested against).
    #[allow(clippy::cast_precision_loss)]
    fn billed(rates: ModelCostRates, usage: &Usage, long_multiplier: f64) -> f64 {
        let long = usage.cache_write_1h.unwrap_or(0) as f64;
        let short = usage.cache_write as f64 - long;
        (rates.input * usage.input as f64
            + rates.output * usage.output as f64
            + rates.cache_read * usage.cache_read as f64
            + rates.cache_write * short
            + rates.input * long_multiplier * long)
            / 1_000_000.0
    }

    #[test]
    fn the_worst_case_bounds_every_usage_within_the_request_at_every_tier() {
        let cost = cost();
        let bound = RequestBound {
            input_tokens: 250_000,
            output_cap: 8_000,
            price_multiplier: 1.0,
        };
        let worst = worst_case_cost_micros(&cost, bound);
        // every split of the input between plain, cached and written
        // tokens, with any output up to the cap, at either tier
        for (input, cache_read, cache_write, long) in [
            (250_000, 0, 0, 0),
            (0, 250_000, 0, 0),
            (0, 0, 250_000, 0),
            (0, 0, 250_000, 250_000),
            (100_000, 100_000, 50_000, 25_000),
        ] {
            for output in [0, 1, 8_000] {
                let usage = Usage {
                    input,
                    output,
                    cache_read,
                    cache_write,
                    cache_write_1h: Some(long),
                    ..Usage::default()
                };
                for rates in [cost.rates(), cost.tiers.as_ref().unwrap()[0].rates()] {
                    let actual = micros_ceil(billed(rates, &usage, 2.0));
                    assert!(
                        actual <= worst,
                        "usage {usage:?} costs {actual} past the worst case {worst}"
                    );
                }
            }
        }
    }

    #[test]
    fn the_worst_case_is_exact_for_plain_input_and_a_full_output() {
        let flat = ModelCost {
            input: 1.0,
            output: 5.0,
            cache_read: 0.1,
            cache_write: 1.25,
            tiers: None,
        };
        let worst = worst_case_cost_micros(
            &flat,
            RequestBound {
                input_tokens: 1_000,
                output_cap: 100,
                price_multiplier: 1.0,
            },
        );
        // 1000 input tokens at the 1h write bound ($2/M), 100 output
        // tokens at $5/M, and the micro-dollar of rounding slack
        assert_eq!(worst, 2_000 + 500 + 1);
    }

    #[test]
    fn a_service_tier_scales_the_worst_case_and_never_lowers_it() {
        let flat = ModelCost {
            input: 1.0,
            output: 1.0,
            cache_read: 1.0,
            cache_write: 1.0,
            tiers: None,
        };
        let bound = |price_multiplier| RequestBound {
            input_tokens: 1_000_000,
            output_cap: 0,
            price_multiplier,
        };
        assert_eq!(worst_case_cost_micros(&flat, bound(1.0)), 2_000_001);
        assert_eq!(worst_case_cost_micros(&flat, bound(2.0)), 4_000_001);
        assert_eq!(worst_case_cost_micros(&flat, bound(0.5)), 2_000_001);
    }

    #[test]
    fn a_cost_is_rounded_up_to_a_micro_dollar_and_kept_in_range() {
        assert_eq!(micros_ceil(0.0), 0);
        assert_eq!(micros_ceil(-1.0), 0);
        assert_eq!(micros_ceil(f64::NAN), 0);
        assert_eq!(micros_ceil(0.000_000_1), 1);
        assert_eq!(micros_ceil(1.5), 1_500_000);
        assert_eq!(micros_ceil(1e12), BUDGET_AMOUNT_MAX);
    }

    #[test]
    fn the_actual_spend_counts_every_billed_token_and_the_reported_cost() {
        let usage = Usage {
            input: 10,
            output: 20,
            cache_read: 30,
            cache_write: 40,
            cost: UsageCost {
                total: 0.001_234_5,
                ..UsageCost::default()
            },
            ..Usage::default()
        };
        assert_eq!(
            actual_spend(&usage),
            BudgetAmounts {
                cost_micros: 1_235,
                tokens: 100,
                time_ms: 0,
                tool_calls: 0,
                requests: 1,
            }
        );
    }
}
