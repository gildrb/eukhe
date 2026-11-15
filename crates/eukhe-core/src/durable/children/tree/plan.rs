//! Pure steps of a session's local crown: units refined by a split's
//! paths, scopes as masks over the units, the local bounds, the node
//! allowance of a split's children, the default hold, and the budget
//! dimension the tree's amounts count.

use std::path::Path;

use eukhe_bend::rules::agent_tree::{Bounds, Crown, Lim, Node, Scope};
use eukhe_types::budget::{BudgetDimension, BudgetLimits, BudgetReport};
use eukhe_types::pi_ai::Usage;

use crate::child_workspace::unit_of;

/// The deepest a node may sit below the root.
pub(crate) const MAX_DEPTH: u64 = 3;
/// The nodes of one tree, help leaves included: the root's allowance.
pub(crate) const MAX_NODES: u64 = 15;
/// What a child's deadline keeps before its parent's, per level, under a
/// deadline (for the parent to integrate).
pub(crate) const MARGIN_MS: u64 = 120_000;

/// A path as the tree stores it: relative, `/`-separated, no trailing
/// separator; `""` (or `.`) is the whole workspace.
#[must_use]
pub(crate) fn unit_path(path: &str) -> String {
    let trimmed = path.trim().trim_start_matches("./").trim_end_matches('/');
    if trimmed == "." {
        String::new()
    } else {
        trimmed.to_owned()
    }
}

/// `crown` and `units` with `path` a unit: a path already a unit changes
/// nothing; a new unit goes last, and in every scope of the crown it is
/// owned exactly where the unit enclosing it is (a path no unit encloses
/// is owned nowhere).
#[must_use]
pub(crate) fn refine(crown: &Crown, units: &[String], path: &str) -> (Crown, Vec<String>) {
    if units.iter().any(|unit| unit == path) {
        return (crown.clone(), units.to_vec());
    }
    let enclosing = unit_of(units, Path::new(path));
    let mut refined = units.to_vec();
    refined.push(path.to_owned());
    let column = |scope: &Scope| enclosing.is_some_and(|unit| scope[unit]);
    (
        Crown {
            tree: refine_node(&crown.tree, units.len(), &column),
            helps: crown.helps.clone(),
        },
        refined,
    )
}

fn refine_node(node: &Node, before: usize, column: &impl Fn(&Scope) -> bool) -> Node {
    let widen = |info: &eukhe_bend::rules::agent_tree::Info| {
        let mut info = info.clone();
        let owned = column(&info.scope);
        info.scope.push(owned);
        if info.patch.len() == before {
            info.patch.push(None);
        }
        info
    };
    match node {
        Node::Leaf(info) => Node::Leaf(widen(info)),
        Node::Split {
            info,
            own,
            left,
            right,
        } => {
            let mut own = own.clone();
            let owned = column(&own);
            own.push(owned);
            Node::Split {
                info: widen(info),
                own,
                left: Box::new(refine_node(left, before, column)),
                right: Box::new(refine_node(right, before, column)),
            }
        }
    }
}

/// `crown` and `units` refined by every path of `paths`, in order.
#[must_use]
pub(crate) fn refine_all(
    crown: &Crown,
    units: &[String],
    paths: &[String],
) -> (Crown, Vec<String>) {
    paths
        .iter()
        .fold((crown.clone(), units.to_vec()), |(crown, units), path| {
            refine(&crown, &units, path)
        })
}

/// The scope `paths` name over `units`: each unit inside one of them.
#[must_use]
pub(crate) fn mask(units: &[String], paths: &[String]) -> Scope {
    units
        .iter()
        .map(|unit| {
            paths
                .iter()
                .any(|path| Path::new(unit).starts_with(path.as_str()))
        })
        .collect()
}

/// What `scope` owns that neither `left` nor `right` does.
#[must_use]
pub(crate) fn rest(scope: &[bool], left: &[bool], right: &[bool]) -> Scope {
    scope
        .iter()
        .zip(left.iter().zip(right))
        .map(|(owned, (left, right))| *owned && !left && !right)
        .collect()
}

/// The paths of the units `scope` owns.
#[must_use]
pub(crate) fn paths(units: &[String], scope: &[bool]) -> Vec<String> {
    units
        .iter()
        .zip(scope)
        .filter(|(_, owned)| **owned)
        .map(|(unit, _)| unit.clone())
        .collect()
}

/// The bounds a session at tree depth `depth` passes to the core for its
/// local crown: the depth left below it, its allowance less what it gave
/// its split children beyond their first node, and the margin when it has
/// a deadline.
#[must_use]
pub(crate) fn bounds(depth: u64, allowance: u64, given: u64, deadline: Lim) -> Bounds {
    Bounds {
        max_depth: MAX_DEPTH.saturating_sub(depth),
        max_nodes: allowance.saturating_sub(given),
        margin: match deadline {
            Lim::Unlimited => 0,
            Lim::Value(_) => MARGIN_MS,
        },
    }
}

/// The nodes of `crown`: its tree's and its help leaves.
#[must_use]
pub(crate) fn size(crown: &Crown) -> u64 {
    fn nodes(node: &Node) -> u64 {
        match node {
            Node::Leaf(_) => 1,
            Node::Split { left, right, .. } => 1 + nodes(left) + nodes(right),
        }
    }
    nodes(&crown.tree) + u64::try_from(crown.helps.len()).unwrap_or(u64::MAX)
}

/// The allowances of a split's two children, for a node of `allowance`
/// whose local crown holds `size` nodes before the split: the halves of
/// what is left beyond the two new nodes, each plus its own node (root
/// 15, no help leaf: 7 and 7).
#[must_use]
pub(crate) fn child_allowances(allowance: u64, size: u64) -> (u64, u64) {
    let left = allowance.saturating_sub(size).saturating_sub(2);
    (left - left / 2 + 1, left / 2 + 1)
}

/// The default hold of a split: two worst-case requests or a tenth of
/// the room, whichever is more; nothing under an unlimited room.
#[must_use]
pub(crate) fn hold(room: Lim, worst_request: u64) -> u64 {
    match room {
        Lim::Unlimited => 0,
        Lim::Value(room) => worst_request.saturating_mul(2).max(room / 10),
    }
}

/// The budget dimension the tree's amounts count: the first one the
/// budget limits of cost, tokens, requests and tool calls; `None` when it
/// limits none of them (the tree is unlimited).
#[must_use]
pub(crate) fn dimension(limits: &BudgetLimits) -> Option<BudgetDimension> {
    [
        BudgetDimension::Cost,
        BudgetDimension::Tokens,
        BudgetDimension::Requests,
        BudgetDimension::ToolCalls,
    ]
    .into_iter()
    .find(|dimension| limits.get(*dimension).is_some())
}

/// What `usage` spent in `dimension` (a usage counts no requests or tool
/// calls: those count zero).
#[must_use]
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "a non-negative cost in micro-dollars far below u64::MAX"
)]
pub(crate) fn spent(usage: &Usage, dimension: BudgetDimension) -> u64 {
    match dimension {
        BudgetDimension::Cost => (usage.cost.total.max(0.0) * 1_000_000.0).round() as u64,
        BudgetDimension::Tokens => usage.total_tokens,
        BudgetDimension::Time | BudgetDimension::Requests | BudgetDimension::ToolCalls => 0,
    }
}

/// The limits carved for a child the core gave `amount` in `dimension`:
/// every other limited dimension but time in the same share of what is
/// free, and time up to the child's deadline (`time_left_ms`).
#[must_use]
pub(crate) fn child_limits(
    report: &BudgetReport,
    dimension: BudgetDimension,
    amount: u64,
    time_left_ms: Option<u64>,
) -> BudgetLimits {
    let base = report.free.get(dimension).max(1);
    [
        BudgetDimension::Cost,
        BudgetDimension::Tokens,
        BudgetDimension::Requests,
        BudgetDimension::ToolCalls,
    ]
    .into_iter()
    .filter(|other| report.limits.get(*other).is_some())
    .fold(BudgetLimits::default(), |limits, other| {
        let share = if other == dimension {
            amount
        } else {
            u64::try_from(
                u128::from(report.free.get(other)) * u128::from(amount) / u128::from(base),
            )
            .unwrap_or(u64::MAX)
        };
        limits.with(other, Some(share))
    })
    .with(
        BudgetDimension::Time,
        report.limits.time_ms.and(time_left_ms),
    )
}
