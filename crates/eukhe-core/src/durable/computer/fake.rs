//! A desktop for the session tests: fixed windows, a count of the
//! observations and acts it served, and an optional hold of its first
//! observation or act until the test releases it or the call is cancelled.

use std::sync::{Condvar, Mutex, MutexGuard, PoisonError};

use eukhe_desktop::{
    ActReport, Done, Effect, Error, FoundNode, Observation, ObserveOptions, Refusal, Step, Tree,
    Truncation, Window, WindowError, WindowFilter, WindowSelector, WindowSummary,
};

/// Which call the fake holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Hold {
    Nothing,
    FirstObserve,
    FirstAct,
}

/// How a held call ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Gate {
    Closed,
    Released,
    Cancelled,
}

#[derive(Debug)]
struct Served {
    observes: usize,
    acts: usize,
    gate: Gate,
}

pub struct FakeDesktop {
    windows: Vec<Window>,
    hold: Hold,
    served: Mutex<Served>,
    turn: Condvar,
}

/// The tree every fake observation prints.
pub(crate) const TREE: &str = "- button \"Send\" [ref=e1]";

impl FakeDesktop {
    pub(crate) fn new(windows: Vec<Window>, hold: Hold) -> Self {
        Self {
            windows,
            hold,
            served: Mutex::new(Served {
                observes: 0,
                acts: 0,
                gate: Gate::Closed,
            }),
            turn: Condvar::new(),
        }
    }

    fn served(&self) -> MutexGuard<'_, Served> {
        self.served.lock().unwrap_or_else(PoisonError::into_inner)
    }

    pub(crate) fn observes(&self) -> usize {
        self.served().observes
    }

    pub(crate) fn acts(&self) -> usize {
        self.served().acts
    }

    /// Lets a held call return.
    pub(crate) fn release(&self) {
        self.open(Gate::Released);
    }

    pub(crate) fn cancel(&self) {
        self.open(Gate::Cancelled);
    }

    fn open(&self, gate: Gate) {
        let mut served = self.served();
        if served.gate == Gate::Closed {
            served.gate = gate;
        }
        self.turn.notify_all();
    }

    /// Wait while the gate is closed when this is the first `call` and the
    /// fake holds it; a cancelled gate refuses.
    fn pass(&self, served: MutexGuard<'_, Served>, call: Hold) -> Result<(), Error> {
        let first = match call {
            Hold::Nothing => false,
            Hold::FirstObserve => served.observes == 1,
            Hold::FirstAct => served.acts == 1,
        };
        if !first || self.hold != call {
            return Ok(());
        }
        let served = self
            .turn
            .wait_while(served, |served| served.gate == Gate::Closed)
            .unwrap_or_else(PoisonError::into_inner);
        match served.gate {
            Gate::Closed | Gate::Released => Ok(()),
            Gate::Cancelled => Err(Error::Refused(Refusal::Cancelled)),
        }
    }

    pub(crate) fn windows(&self, filter: &WindowFilter) -> Vec<Window> {
        self.windows
            .iter()
            .filter(|window| filter.matches(window))
            .cloned()
            .collect()
    }

    pub(crate) fn window(&self, selector: &WindowSelector) -> Result<Window, Error> {
        let refused = |error: WindowError| Error::Refused(Refusal::Window(error));
        match selector {
            WindowSelector::Id(id) => self
                .windows
                .iter()
                .find(|window| window.id == *id)
                .cloned()
                .ok_or_else(|| refused(WindowError::NotFound(id.clone()))),
            WindowSelector::Filter(filter) => {
                let found = self.windows(filter);
                match found.as_slice() {
                    [only] => Ok(only.clone()),
                    [] => Err(refused(WindowError::NoMatch(filter.clone()))),
                    [..] => Err(refused(WindowError::Ambiguous {
                        candidates: found.into_iter().map(WindowSummary::from).collect(),
                    })),
                }
            }
        }
    }

    pub(crate) fn observe(
        &self,
        selector: &WindowSelector,
        options: ObserveOptions,
    ) -> Result<Observation, Error> {
        let window = self.window(selector)?;
        let mut served = self.served();
        served.observes += 1;
        self.pass(served, Hold::FirstObserve)?;
        Ok(Observation {
            window,
            screenshot: None,
            tree: options.tree.map(|_| Tree {
                text: TREE.to_owned(),
                nodes: 1,
                truncation: Truncation::Complete,
            }),
        })
    }

    pub(crate) fn find(&self, selector: &WindowSelector) -> Result<Vec<FoundNode>, Error> {
        self.window(selector).map(|_| Vec::new())
    }

    pub(crate) fn act(&self, steps: &[Step]) -> Result<ActReport, Error> {
        let mut served = self.served();
        served.acts += 1;
        self.pass(served, Hold::FirstAct)?;
        Ok(ActReport {
            steps: steps
                .iter()
                .map(|_| Effect::Confirmed {
                    done: Done::Delivered,
                })
                .collect(),
        })
    }
}
