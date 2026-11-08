//! The first-prompt gate of sibling children: children of one parent on
//! the same model in the same working directory send the same system
//! prompt and tool list, so their first requests share one prompt-cache
//! prefix. The provider (Anthropic) makes a cache entry readable only once
//! the response of the request that writes it has begun: siblings prompted
//! at the same instant each write the whole prefix and none reads it.
//! So the first prompt of a cohort (the leader) goes at once, and the
//! others (its followers) wait until the leader's first response landed
//! (its usage shows in its stats), the leader settled without one or
//! cannot be read, or [`FOLLOWER_CAP`] passed; a cohort whose leader landed
//! lets every later prompt through at once.
//!
//! The gate is in memory, per host process: a child this process did not
//! create (a rerun after a restart) has no cohort and is prompted at once.

use std::collections::HashMap;
use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use tokio::sync::watch;
use tokio::time::Instant;

/// The longest a follower waits for its leader, and the longest the
/// leader's landing is watched.
pub(super) const FOLLOWER_CAP: Duration = Duration::from_secs(20);

/// How often the leader's landing watch reads it.
pub(super) const LANDING_POLL: Duration = Duration::from_millis(200);

/// Children whose first requests share a prompt-cache prefix.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct Cohort {
    /// The child model (`provider/id`).
    pub(super) model: String,
    /// The child's working directory.
    pub(super) cwd: String,
}

/// Where a cohort's first prompts stand.
enum Phase {
    /// The leader was prompted and its first response has not landed:
    /// a follower waits until the leader's sender drops.
    Leading(watch::Receiver<()>),
    /// The leader landed or was released: prompts go at once.
    Open,
}

/// The cohorts of one host process.
#[derive(Clone, Default)]
pub(super) struct FirstPromptGate {
    cohorts: Arc<Mutex<HashMap<Cohort, Phase>>>,
}

/// A first prompt's turn in its cohort.
pub(super) enum Turn {
    /// The first of its cohort: prompt at once, then watch the landing.
    Lead(Leader),
    /// The leader's first response is still out: wait, then prompt.
    Follow(Follower),
    /// The cohort's leader landed (or was released): prompt at once.
    Open,
}

/// A cohort's leader. Dropping it (its landing watch ended, or its prompt
/// failed) opens the cohort and releases its followers.
pub(super) struct Leader {
    gate: FirstPromptGate,
    cohort: Cohort,
    /// Dropped after the cohort opens: its followers' `changed` then ends.
    _release: watch::Sender<()>,
}

/// A follower waiting for its leader.
pub(super) struct Follower(watch::Receiver<()>);

/// One read of the leader during its landing watch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LeaderRead {
    /// Its first response landed (usage in its stats), or it cannot be
    /// read: its followers go.
    Done,
    /// Its run is in flight without a response yet.
    Running,
    /// Nothing in flight and no response. Twice in a row: it settled
    /// without one (once can precede the start of the admitted run).
    Idle,
}

impl FirstPromptGate {
    /// The turn of a first prompt of `cohort`.
    pub(super) fn turn(&self, cohort: Cohort) -> Turn {
        let mut cohorts = self.cohorts.lock().unwrap_or_else(PoisonError::into_inner);
        match cohorts.get(&cohort) {
            Some(Phase::Leading(released)) => Turn::Follow(Follower(released.clone())),
            Some(Phase::Open) => Turn::Open,
            None => {
                let (release, released) = watch::channel(());
                cohorts.insert(cohort.clone(), Phase::Leading(released));
                Turn::Lead(Leader {
                    gate: self.clone(),
                    cohort,
                    _release: release,
                })
            }
        }
    }
}

impl Leader {
    /// Read the prompted leader every [`LANDING_POLL`] until its first
    /// response landed, it settled without one, or [`FOLLOWER_CAP`]
    /// passed; then the cohort opens.
    pub(super) async fn watch<F, Fut>(self, mut read: F)
    where
        F: FnMut() -> Fut,
        Fut: Future<Output = LeaderRead>,
    {
        let until = Instant::now() + FOLLOWER_CAP;
        let mut idle = false;
        loop {
            match read().await {
                LeaderRead::Done => break,
                LeaderRead::Idle if idle => break,
                LeaderRead::Idle => idle = true,
                LeaderRead::Running => idle = false,
            }
            if Instant::now() + LANDING_POLL >= until {
                break;
            }
            tokio::time::sleep(LANDING_POLL).await;
        }
    }
}

impl Drop for Leader {
    fn drop(&mut self) {
        self.gate
            .cohorts
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(self.cohort.clone(), Phase::Open);
    }
}

impl Follower {
    /// Wait until the leader is done (landed, or released), at most
    /// [`FOLLOWER_CAP`] and never past `deadline` (the prompt's budget).
    pub(super) async fn wait(mut self, deadline: Instant) {
        let until = deadline.min(Instant::now() + FOLLOWER_CAP);
        // Every outcome lets the follower go: `changed` ends in an error
        // once the leader's sender dropped, and the timeout is the cap.
        let _released = tokio::time::timeout_at(until, self.0.changed()).await;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cohort(model: &str) -> Cohort {
        Cohort {
            model: model.to_owned(),
            cwd: "/work".to_owned(),
        }
    }

    fn kind(turn: &Turn) -> &'static str {
        match turn {
            Turn::Lead(_) => "lead",
            Turn::Follow(_) => "follow",
            Turn::Open => "open",
        }
    }

    /// The leader of a cohort goes at once, a sibling follows, another
    /// cohort is not blocked; the leader's landing (after two reads in
    /// flight) releases the follower and opens the cohort.
    #[tokio::test(start_paused = true)]
    async fn the_leader_landing_releases_its_followers() {
        let gate = FirstPromptGate::default();
        let leader = gate.turn(cohort("a/one"));
        let follower = gate.turn(cohort("a/one"));
        let other = gate.turn(cohort("b/two"));
        let kinds = [kind(&leader), kind(&follower), kind(&other)];
        let (Turn::Lead(leader), Turn::Follow(follower)) = (leader, follower) else {
            panic!("a leader and a follower: {kinds:?}");
        };
        let start = Instant::now();
        let mut reads = [LeaderRead::Running, LeaderRead::Idle, LeaderRead::Done].into_iter();
        let ((), waited) = tokio::join!(
            leader.watch(move || std::future::ready(reads.next().expect("a read"))),
            async {
                follower.wait(start + Duration::from_secs(60)).await;
                start.elapsed()
            }
        );
        assert_eq!(
            (kinds, waited, kind(&gate.turn(cohort("a/one")))),
            (["lead", "follow", "lead"], LANDING_POLL * 2, "open")
        );
    }

    /// A follower whose leader never lands goes at the cap, or at its
    /// prompt deadline when that comes first.
    #[tokio::test(start_paused = true)]
    async fn a_follower_goes_at_the_cap_or_its_deadline() {
        let gate = FirstPromptGate::default();
        let _leader = gate.turn(cohort("a/one"));
        let mut waited = Vec::new();
        for deadline in [Duration::from_secs(60), Duration::from_secs(5)] {
            let Turn::Follow(follower) = gate.turn(cohort("a/one")) else {
                panic!("a follower");
            };
            let start = Instant::now();
            follower.wait(start + deadline).await;
            waited.push(start.elapsed());
        }
        assert_eq!(waited, vec![FOLLOWER_CAP, Duration::from_secs(5)]);
    }

    /// A leader that settles without a response (idle twice in a row)
    /// opens its cohort; a leader dropped before its watch (its prompt
    /// failed) releases its follower at once.
    #[tokio::test(start_paused = true)]
    async fn a_settled_or_failed_leader_releases_its_followers() {
        let gate = FirstPromptGate::default();
        let Turn::Lead(leader) = gate.turn(cohort("a/one")) else {
            panic!("a leader");
        };
        let start = Instant::now();
        let mut reads = [
            LeaderRead::Idle,
            LeaderRead::Running,
            LeaderRead::Idle,
            LeaderRead::Idle,
        ]
        .into_iter();
        leader
            .watch(move || std::future::ready(reads.next().expect("a read")))
            .await;
        let settled = (start.elapsed(), kind(&gate.turn(cohort("a/one"))));

        let Turn::Lead(leader) = gate.turn(cohort("b/two")) else {
            panic!("a leader");
        };
        let Turn::Follow(follower) = gate.turn(cohort("b/two")) else {
            panic!("a follower");
        };
        let start = Instant::now();
        drop(leader);
        follower.wait(start + Duration::from_secs(60)).await;
        assert_eq!(
            (settled, start.elapsed(), kind(&gate.turn(cohort("b/two")))),
            ((LANDING_POLL * 3, "open"), Duration::ZERO, "open")
        );
    }
}
