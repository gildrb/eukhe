//! The notices due before the agent's next request ([`BudgetGate::due`]):
//! what the budget's extension writes into the conversation before the
//! request reads its context.

use eukhe_types::budget::{BudgetAmounts, BudgetLimits};
use tempfile::TempDir;

use super::notices::NoticeKind;
use super::BudgetGate;

/// B8: a budget is due before the agent's first request after it was set,
/// once; adding to it makes it due again, with what is left then.
#[test]
fn the_budget_is_due_before_the_first_request_after_it_was_set() {
    let dir = TempDir::new().unwrap();
    let gate = BudgetGate::open(dir.path(), "session", None);
    gate.set(BudgetLimits {
        requests: Some(3),
        ..BudgetLimits::default()
    })
    .unwrap();
    let first: Vec<(NoticeKind, String)> = gate
        .due()
        .into_iter()
        .map(|notice| (notice.kind, notice.text))
        .collect();
    let again = gate.due();
    gate.add(BudgetAmounts {
        requests: 2,
        ..BudgetAmounts::default()
    })
    .unwrap();
    let added: Vec<String> = gate.due().into_iter().map(|notice| notice.text).collect();
    assert_eq!(
        (first, again, added),
        (
            vec![(
                NoticeKind::Set,
                "[budget] This task has a budget: 3 requests. Every model request and tool call reserves its worst case before it runs: plan your work to fit. In the Python kernel (the python tool) `await budget.status()` returns what is left.".to_owned()
            )],
            Vec::new(),
            vec!["[budget] This task has a budget: 5 requests. Every model request and tool call reserves its worst case before it runs: plan your work to fit. In the Python kernel (the python tool) `await budget.status()` returns what is left.".to_owned()],
        )
    );
}

/// A session without a budget, and a budget without limits, are due
/// nothing: limits off tell the agent nothing.
#[test]
fn nothing_is_due_without_limits() {
    let dir = TempDir::new().unwrap();
    let none = BudgetGate::open(dir.path(), "session", None);
    let unlimited = BudgetGate::open(dir.path(), "other", None);
    unlimited.set(BudgetLimits::default()).unwrap();
    assert_eq!(
        (
            none.due().len(),
            none.may_have_due(),
            unlimited.due().len(),
            unlimited.may_have_due()
        ),
        (0, false, 0, false)
    );
}
