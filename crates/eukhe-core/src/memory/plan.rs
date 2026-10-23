//! The chat's planner: which lines the view and the compaction view hold,
//! which batch a message runs, which nodes the compactor builds next. One
//! state machine over plain data, `St` of `bend/optchat/state.bend` stepped as
//! its `stepx` (`bend/optchat/stepx.bend`): the owner keeps the texts and performs every read and
//! write, and tells the planner only what happened (a message, a node
//! built with its size, a call started or freed, a turn waiting).

use std::collections::{BTreeSet, HashMap};

use super::view::Part;
use super::{COMPACTION_CEILING, COMPACTION_FLOOR, JOBS, PLACEHOLDER, VIEW_CEILING, VIEW_FLOOR};

/// Who the compactor's next calls serve (H2.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Demand {
    /// No turn waits: the gist's order (§4).
    Background,
    /// A turn waits for the view: only the view's unbuilt lines start; the
    /// ready merges wait until the view settles.
    Turn,
}

/// The byte budgets of the two sawtooths and the compactor's job slots
/// (§3.2, §4). Only the bridge test sets other values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Budgets {
    pub ceiling: usize,
    pub floor: usize,
    pub compaction_ceiling: usize,
    pub compaction_floor: usize,
    pub jobs: usize,
}

impl Default for Budgets {
    fn default() -> Budgets {
        Budgets {
            ceiling: VIEW_CEILING,
            floor: VIEW_FLOOR,
            compaction_ceiling: COMPACTION_CEILING,
            compaction_floor: COMPACTION_FLOOR,
            jobs: JOBS,
        }
    }
}

/// What a message did to the view: the batch it ran, if any (its merged
/// parents in order, maybe none, and the view after them), and whether the
/// view is still over its floor (the next message merges what it can).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Grown {
    pub batch: Option<(Vec<Part>, Vec<Part>)>,
    pub shrinking: bool,
}

/// The planner's state (`St`): `T`, the size of every built node, the
/// view, whether a batch is still shrinking it, the compaction view, the
/// ready merges (by level, then index) and the nodes being built.
#[derive(Debug, Default)]
pub(crate) struct Planner {
    budgets: Budgets,
    total: u64,
    sizes: HashMap<Part, usize>,
    view: Vec<Part>,
    shrinking: bool,
    compaction: Vec<Part>,
    ready: BTreeSet<Part>,
    busy: BTreeSet<Part>,
}

impl Planner {
    /// The planner of a loaded chat: `total` messages, the built nodes'
    /// sizes, the view folded from the log and whether its last batch left
    /// it shrinking. With `missed` (a shrinking view whose last message has
    /// no batch line: the owner died between the two writes), that batch
    /// runs now and comes back. The compaction view starts
    /// from the view, merged down once; the ready merges are the parents
    /// whose two halves are built.
    pub(crate) fn open(
        budgets: Budgets,
        total: u64,
        sizes: HashMap<Part, usize>,
        view: Vec<Part>,
        shrinking: bool,
        missed: bool,
    ) -> (Planner, Grown) {
        let mut ready = BTreeSet::new();
        for part in sizes.keys() {
            let parent = part.parent();
            if sizes.contains_key(&part.sibling()) && !sizes.contains_key(&parent) {
                ready.insert(parent);
            }
        }
        let mut planner = Planner {
            budgets,
            total,
            sizes,
            view,
            shrinking,
            compaction: Vec::new(),
            ready,
            busy: BTreeSet::new(),
        };
        let batch = missed.then(|| {
            let mut view = std::mem::take(&mut planner.view);
            let merged = planner.fit(&mut view, budgets.floor);
            planner.shrinking = planner.size(&view) > budgets.floor;
            planner.view = view;
            (merged, planner.view.clone())
        });
        let mut compaction = planner.view.clone();
        planner.fit(&mut compaction, budgets.compaction_floor);
        planner.compaction = compaction;
        let shrinking = planner.shrinking;
        (planner, Grown { batch, shrinking })
    }

    /// Message `T` arrives: its line goes to both views; once the view
    /// passes its ceiling (or while a batch is still shrinking it), a batch
    /// merges it down to its floor as far as built parents allow (§3.2). A
    /// batch that merged restarts the compaction view from the view; else
    /// the compaction view keeps its own sawtooth (§4).
    pub(crate) fn message(&mut self) -> Grown {
        let leaf = Part {
            l: 0,
            i: self.total,
        };
        self.total += 1;
        self.view.push(leaf);
        self.compaction.push(leaf);
        if !self.shrinking && self.size(&self.view) <= self.budgets.ceiling {
            self.fit_compaction();
            return Grown {
                batch: None,
                shrinking: false,
            };
        }
        let mut view = std::mem::take(&mut self.view);
        let merged = self.fit(&mut view, self.budgets.floor);
        self.shrinking = self.size(&view) > self.budgets.floor;
        self.view = view;
        if merged.is_empty() {
            self.fit_compaction();
        } else {
            let mut compaction = self.view.clone();
            self.fit(&mut compaction, self.budgets.compaction_floor);
            self.compaction = compaction;
        }
        Grown {
            batch: Some((merged, self.view.clone())),
            shrinking: self.shrinking,
        }
    }

    /// Node `part` was built, `size` bytes: it is no longer ready nor busy,
    /// its parent becomes ready once its sibling is built too (a queue,
    /// never a scan of the tree: §4), and the compaction view keeps its
    /// sawtooth. The view merges only when a message comes.
    pub(crate) fn built(&mut self, part: Part, size: usize) {
        self.sizes.insert(part, size);
        self.ready.remove(&part);
        self.busy.remove(&part);
        let parent = part.parent();
        if self.sizes.contains_key(&part.sibling()) && !self.sizes.contains_key(&parent) {
            self.ready.insert(parent);
        }
        self.fit_compaction();
    }

    /// How many nodes are being built (or failed, waiting to be tried again).
    pub(crate) fn busy_count(&self) -> usize {
        self.busy.len()
    }

    /// The node's call started (or failed, waiting to be tried again).
    pub(crate) fn started(&mut self, part: Part) {
        self.busy.insert(part);
    }

    /// The node may start again.
    pub(crate) fn freed(&mut self, part: Part) {
        self.busy.remove(&part);
    }

    /// A turn starts to wait (H2.1, `St.wait`): every busy node that is not
    /// a view line still unbuilt stops; returns those, whose calls the
    /// owner stops.
    pub(crate) fn hold(&mut self) -> Vec<Part> {
        let mut held = Vec::new();
        let (view, sizes) = (&self.view, &self.sizes);
        self.busy.retain(|part| {
            let needed = view.contains(part) && !sizes.contains_key(part);
            if !needed {
                held.push(*part);
            }
            needed
        });
        held
    }

    /// The nodes to start now, within the free job slots (§4 "The order",
    /// `cands`): a view line not built once fewer than `jobs` unbuilt lines
    /// come before it, oldest first; then, unless a turn waits
    /// ([`Demand::Turn`], `cands.need`), the ready merges, in their order.
    pub(crate) fn candidates(&self, demand: Demand) -> Vec<Part> {
        let jobs = self.budgets.jobs;
        let room = jobs.saturating_sub(self.busy.len());
        let mut out = Vec::new();
        let mut unbuilt_before = 0;
        for part in &self.view {
            if unbuilt_before >= jobs || out.len() >= room {
                break;
            }
            if self.sizes.contains_key(part) {
                continue;
            }
            if !self.busy.contains(part) {
                out.push(*part);
            }
            unbuilt_before += 1;
        }
        match demand {
            Demand::Turn => return out,
            Demand::Background => {}
        }
        for part in &self.ready {
            if out.len() >= room {
                break;
            }
            if !self.busy.contains(part) {
                out.push(*part);
            }
        }
        out
    }

    /// A compaction's view of `part` (§4, `ctx`): the compaction view's
    /// lines before the message (it comes whole in the task), or up to a
    /// merge's last message, stopping at the first unbuilt line.
    pub(crate) fn context(&self, part: Part) -> Vec<Part> {
        let end = if part.l == 0 {
            part.start()
        } else {
            part.end()
        };
        self.compaction
            .iter()
            .take_while(|line| line.end() <= end && self.sizes.contains_key(line))
            .copied()
            .collect()
    }

    /// The compaction view (the bridge test prints it).
    #[cfg(test)]
    pub(crate) fn compaction(&self) -> &[Part] {
        &self.compaction
    }

    /// Whether a batch is still shrinking the view (the bridge test prints
    /// it).
    #[cfg(test)]
    pub(crate) fn shrinking(&self) -> bool {
        self.shrinking
    }

    /// A line's bytes: its node's, or the placeholder's.
    fn line_size(&self, part: Part) -> usize {
        self.sizes.get(&part).copied().unwrap_or(PLACEHOLDER.len())
    }

    fn size(&self, lines: &[Part]) -> usize {
        lines.iter().map(|part| self.line_size(*part)).sum()
    }

    /// The compaction view's own sawtooth: past its ceiling, down to its
    /// floor.
    fn fit_compaction(&mut self) {
        if self.size(&self.compaction) > self.budgets.compaction_ceiling {
            let mut compaction = std::mem::take(&mut self.compaction);
            self.fit(&mut compaction, self.budgets.compaction_floor);
            self.compaction = compaction;
        }
    }

    /// Merge the most due built pair of `lines` until they fit `budget`
    /// bytes or no pair has a built parent (`fit`, Last). Returns the merged
    /// parents, in merge order.
    ///
    /// A pair is due by how long ago it ended in its own line size,
    /// `(T - last) / 2^l`, written as `(T + 1)/2^l - i` (same order, shifted
    /// by 2); of equal pairs the oldest merges first. This picks the merges
    /// of Taelin's rollback `push`.
    fn fit(&self, lines: &mut Vec<Part>, budget: usize) -> Vec<Part> {
        let mut size = self.size(lines);
        let mut merged = Vec::new();
        while size > budget {
            let mut best: Option<(usize, u64, u32)> = None;
            for (at, pair) in lines.windows(2).enumerate() {
                let (left, right) = (pair[0], pair[1]);
                if left.l == right.l
                    && left.i % 2 == 0
                    && right.i == left.i + 1
                    && self.sizes.contains_key(&left.parent())
                {
                    // `T + 1 - first`: the pair ends at `first + 2^(l+1) - 1`
                    // and `right` exists, so this is at least `2^(l+1)`.
                    let age = self.total + 1 - left.start();
                    let more_due = best.is_none_or(|(_, best_age, best_l)| {
                        more_due(age, left.l, best_age, best_l)
                    });
                    if more_due {
                        best = Some((at, age, left.l));
                    }
                }
            }
            let Some((at, _, _)) = best else {
                break;
            };
            let parent = lines[at].parent();
            size = size - self.line_size(lines[at]) - self.line_size(lines[at + 1])
                + self.line_size(parent);
            lines[at] = parent;
            lines.remove(at + 1);
            merged.push(parent);
        }
        merged
    }
}

/// `age_a / 2^l_a > age_b / 2^l_b`, exactly: both sides scale by the
/// smaller power, so the shift is at most 63 and fits in `u128`. Strict:
/// of equal pairs, the earlier (older) one stays the best.
fn more_due(age_a: u64, l_a: u32, age_b: u64, l_b: u32) -> bool {
    let low = l_a.min(l_b);
    (u128::from(age_a) << (l_b - low)) > (u128::from(age_b) << (l_a - low))
}
