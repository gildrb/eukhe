//! Autoresearch (port of omp `autoresearch/`, docs/workflows.md
//! "Autoresearch"): the agent builds a benchmark harness
//! (`autoresearch.sh`), measures each experiment with it, and keeps only
//! the improvements.
//!
//! Every decision is the Lab's: the compiled Bend stepper
//! [`eukhe_bend::rules::autoresearch::Lab`] (entry 430, `bend/autoresearch`
//! and its laws). This module is the host around it:
//!
//! - [`store`]: the event log of each repository branch, written before
//!   an event's effect runs, replayed on open;
//! - [`runner`]: one run of `bash autoresearch.sh` through the approval
//!   gate of the `bash` tool, each output line fed to the Lab;
//! - [`git`]: the `autoresearch/*` branch, the commit of a kept run, the
//!   reset of the others, the paths a run changed;
//! - [`ops`]: the operations (init, run, log, flag, notes, state, mode);
//! - [`host`]: the kernel host requests `autoresearch.*` of the
//!   `autoresearch` skill, and the autonomous run that continues the loop
//!   while the Lab's mode is on;
//! - [`command`]: `/autoresearch <goal> | off | status | clear`.

mod command;
mod git;
mod host;
mod ops;
mod runner;
mod store;

#[cfg(test)]
mod tests;

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use eukhe_bend::rules::autoresearch::{Event, Lab, Outcome};

pub(crate) use command::execute as execute_command;
pub(crate) use host::register_host_requests;

use self::git::Workspace;
use self::runner::RunGate;
use self::store::{Durability, Store};

/// A Lab refusal: the text tells the model why and what to do instead.
/// The Lab's state is unchanged and nothing was logged.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{0}")]
pub(crate) struct Refused(pub(crate) String);

/// Builds the approval gate of one run; the argument identifies the run's
/// questions to the user (the tool call's id).
pub(crate) type GateSource = Arc<dyn Fn(&str) -> RunGate + Send + Sync>;

/// The autoresearch host of one session: where its stores live, its
/// working directory, and the gate its runs pass.
#[derive(Clone)]
pub(crate) struct Autoresearch {
    /// `~/.eukhe/autoresearch`.
    home: PathBuf,
    cwd: PathBuf,
    gate: GateSource,
}

/// An open store and the Lab its log replays to.
struct Opened {
    store: Store,
    lab: Lab,
}

type Slot = Arc<tokio::sync::Mutex<Option<Opened>>>;

/// The open stores of this process, one lock per store directory: one
/// operation at a time per repository branch.
static OPEN: LazyLock<Mutex<HashMap<PathBuf, Slot>>> = LazyLock::new(Mutex::default);

/// The store of the workspace's branch, locked, with its Lab.
struct Session {
    workspace: Workspace,
    slot: tokio::sync::OwnedMutexGuard<Option<Opened>>,
}

impl Session {
    /// The open store and Lab; gone only after a failed append.
    fn opened(&mut self) -> anyhow::Result<&mut Opened> {
        self.slot.as_mut().ok_or_else(|| {
            anyhow::anyhow!("the autoresearch store closed after a failed write; try again")
        })
    }

    /// Step the Lab with `event` and, when it accepts, log the event
    /// before the caller runs its effect. A refusal is [`Refused`].
    ///
    /// # Errors
    ///
    /// [`Refused`], a core failure, or a failed append (the slot then
    /// closes: the next operation replays the log on disk).
    fn accept(&mut self, event: &Event, durability: Durability) -> anyhow::Result<Outcome> {
        let opened = self.opened()?;
        let outcome = match opened.lab.step(event)? {
            Ok(outcome) => outcome,
            Err(refusal) => return Err(Refused(refusal.text).into()),
        };
        if let Err(error) = opened.store.append(event, durability) {
            *self.slot = None;
            return Err(error);
        }
        Ok(outcome)
    }
}

impl Autoresearch {
    pub(crate) fn new(agent_dir: &std::path::Path, cwd: PathBuf, gate: GateSource) -> Self {
        Self {
            home: agent_dir.join("autoresearch"),
            cwd,
            gate,
        }
    }

    /// Lock and open the store of the workspace's current branch; a store
    /// whose log another process grew is replayed again.
    async fn session(&self) -> anyhow::Result<Session> {
        let workspace = Workspace::of(&self.cwd).await?;
        let dir = Store::dir_of(
            &self.home,
            &workspace.root,
            workspace.branch.as_deref(),
            workspace.repo.is_some(),
        );
        let slot = Arc::clone(
            OPEN.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .entry(dir.clone())
                .or_default(),
        );
        let mut slot = slot.lock_owned().await;
        if !slot.as_ref().is_some_and(|opened| opened.store.current()) {
            let (store, lab) = Store::open(dir)?;
            *slot = Some(Opened { store, lab });
        }
        Ok(Session { workspace, slot })
    }
}
