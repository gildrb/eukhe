//! Amounts between the wire vocabulary (`eukhe_types::budget`) and the
//! compiled core's (`eukhe_bend::rules::budget`), and the dimensions a
//! budget does not limit.

use eukhe_bend::rules::budget::{Amt, Ask, Dim};
use eukhe_types::budget::{BudgetAmounts, BudgetDimension, BudgetLimits, BUDGET_AMOUNT_MAX};

/// `amounts` for the core, each within a budget's range: the spent
/// dimensions (time is the deadline, not an amount).
pub(crate) fn to_amt(amounts: BudgetAmounts) -> Amt {
    Amt {
        cost: amounts.cost_micros.min(BUDGET_AMOUNT_MAX),
        tok: amounts.tokens.min(BUDGET_AMOUNT_MAX),
        calls: amounts.tool_calls.min(BUDGET_AMOUNT_MAX),
        reqs: amounts.requests.min(BUDGET_AMOUNT_MAX),
    }
}

/// `amounts` as an ask of the core: the spent dimensions and `time_ms`
/// as its duration, each within a budget's range.
pub(crate) fn to_ask(amounts: BudgetAmounts) -> Ask {
    Ask {
        amt: to_amt(amounts),
        ms: amounts.time_ms.min(BUDGET_AMOUNT_MAX),
    }
}

pub(crate) fn from_amt(amt: Amt) -> BudgetAmounts {
    BudgetAmounts {
        cost_micros: amt.cost,
        tokens: amt.tok,
        time_ms: 0,
        tool_calls: amt.calls,
        requests: amt.reqs,
    }
}

pub(crate) fn from_ask(ask: Ask) -> BudgetAmounts {
    BudgetAmounts {
        time_ms: ask.ms,
        ..from_amt(ask.amt)
    }
}

pub(crate) fn dimension(dim: Dim) -> BudgetDimension {
    match dim {
        Dim::Cost => BudgetDimension::Cost,
        Dim::Tokens => BudgetDimension::Tokens,
        Dim::Time => BudgetDimension::Time,
        Dim::Calls => BudgetDimension::ToolCalls,
        Dim::Reqs => BudgetDimension::Requests,
    }
}

pub(crate) fn add(a: BudgetAmounts, b: BudgetAmounts) -> BudgetAmounts {
    BudgetAmounts {
        cost_micros: a.cost_micros.saturating_add(b.cost_micros),
        tokens: a.tokens.saturating_add(b.tokens),
        time_ms: a.time_ms.saturating_add(b.time_ms),
        tool_calls: a.tool_calls.saturating_add(b.tool_calls),
        requests: a.requests.saturating_add(b.requests),
    }
}

/// Each dimension's limit, 0 where there is none.
pub(crate) fn limits_amounts(limits: &BudgetLimits) -> BudgetAmounts {
    BudgetDimension::ALL
        .into_iter()
        .fold(BudgetAmounts::default(), |amounts, dimension| {
            amounts.with(dimension, limits.get(dimension).unwrap_or(0))
        })
}

/// What the account counts of `amounts`: the limited spent dimensions,
/// within a budget's range, no time.
pub(crate) fn counted(amounts: BudgetAmounts, limits: &BudgetLimits) -> BudgetAmounts {
    from_amt(to_amt(mask(amounts, limits)))
}

/// `amounts` with every dimension that `limits` leaves unlimited set to
/// zero: the ledger counts nothing there, so nothing is asked of it.
#[must_use]
pub fn mask(amounts: BudgetAmounts, limits: &BudgetLimits) -> BudgetAmounts {
    BudgetDimension::ALL.into_iter().fold(
        BudgetAmounts::default(),
        |masked, dimension| match limits.get(dimension) {
            Some(_) => masked.with(dimension, amounts.get(dimension)),
            None => masked,
        },
    )
}

/// The limits that limit exactly the non-zero dimensions of `amounts`.
#[must_use]
pub fn limits_of(amounts: BudgetAmounts) -> BudgetLimits {
    BudgetDimension::ALL.into_iter().fold(
        BudgetLimits::default(),
        |limits, dimension| match amounts.get(dimension) {
            0 => limits,
            amount => limits.with(dimension, Some(amount)),
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn amounts(
        cost_micros: u64,
        tokens: u64,
        time_ms: u64,
        tool_calls: u64,
        requests: u64,
    ) -> BudgetAmounts {
        BudgetAmounts {
            cost_micros,
            tokens,
            time_ms,
            tool_calls,
            requests,
        }
    }

    #[test]
    fn a_dimension_without_a_limit_is_not_counted() {
        let limits = BudgetLimits {
            cost_micros: Some(5),
            tool_calls: Some(0),
            requests: Some(9),
            ..BudgetLimits::default()
        };
        assert_eq!(
            mask(amounts(1, 2, 3, 4, 5), &limits),
            amounts(1, 0, 0, 4, 5)
        );
        assert_eq!(
            limits_of(amounts(1, 0, 3, 0, 2)),
            BudgetLimits {
                cost_micros: Some(1),
                time_ms: Some(3),
                requests: Some(2),
                ..BudgetLimits::default()
            }
        );
    }

    #[test]
    fn time_is_an_asks_duration_and_never_a_counted_amount() {
        let all = limits_of(amounts(1, 1, 1, 1, 1));
        assert_eq!(
            counted(amounts(1, 2, 3, 4, 5), &all),
            amounts(1, 2, 0, 4, 5)
        );
        assert_eq!(
            from_ask(to_ask(amounts(1, 2, 3, 4, BUDGET_AMOUNT_MAX + 1))),
            amounts(1, 2, 3, 4, BUDGET_AMOUNT_MAX)
        );
    }
}
