//! The background focus guard: background input never leaves its target in
//! front of the user. An app that comes forward during the input, or within
//! the settle after it, without the user picking it, is sent back behind
//! the user's app, whose key window is restored (port of
//! `with_background_watch` in omp `crates/natives/src/desktop/macos/skylight.rs`).

use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use super::ax;
use super::ffi::process::uptime_ns;
use super::ffi::quartz;
use super::ffi::sky::{FrontRequest, Psn, Spi, CPS_NO_WINDOWS};
use crate::control::Sent;
use crate::error::{Error, Interruption, Intervention, Refusal, Unverified};

/// How long after the action an app coming forward is still its doing:
/// Finder's Cmd-O brings `TextEdit` forward 100-220 ms after the key.
const SETTLE: Duration = Duration::from_millis(500);
/// How often the guard reads the front app.
const SAMPLE: Duration = Duration::from_millis(5);
/// The mouse presses (`CGEventType`) by which a user picks an app.
const POINTER_PRESSES: [u32; 3] = [1, 3, 25];
/// Command and Control, which start the shortcuts that switch apps.
const SWITCH_FLAGS: u64 = 0x0010_0000 | 0x0004_0000;

/// Whether the user came to the target while the guard watched: later
/// input then stops, even once they left again.
pub(super) struct Visit<'a>(Option<&'a AtomicBool>);

impl Visit<'_> {
    /// For input into the app already in front, which no guard watches.
    pub(super) const NONE: Visit<'static> = Visit(None);

    fn happened(&self) -> bool {
        self.0
            .is_some_and(|visited| visited.load(Ordering::Acquire))
    }
}

/// The user's pointer presses the HID system has counted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Presses([u32; 3]);

impl Presses {
    fn read() -> Self {
        Self(POINTER_PRESSES.map(quartz::hid_count))
    }
}

/// What the guard makes of the front app it reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Decision {
    /// The user's app is still in front.
    Keep,
    /// Another app came forward by the user's choice: stop sending apps
    /// back; `visited` when it is the target.
    Disarm { visited: bool },
    /// Another app came forward by the input: send it back.
    Restore,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Armed {
    Armed,
    Disarmed,
}

/// Whether the user chose an app since the guard began.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Choice {
    Chose,
    Untouched,
}

fn decide(
    front: (Psn, Option<i32>),
    previous: Psn,
    target: i32,
    choice: Choice,
    armed: Armed,
) -> Decision {
    let (psn, pid) = front;
    if psn == previous {
        return Decision::Keep;
    }
    match (choice, armed) {
        (Choice::Chose, _) | (Choice::Untouched, Armed::Disarmed) => Decision::Disarm {
            visited: pid == Some(target),
        },
        (Choice::Untouched, Armed::Armed) => Decision::Restore,
    }
}

/// What the guard's sampler saw by the end.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Outcome {
    Kept,
    /// `WindowServer` refused to put the user's app back.
    RestoreRejected,
}

/// Runs `action`, background input to process `pid`, under the guard.
pub(super) fn watch<T>(
    spi: &Spi,
    pid: i32,
    action: impl FnOnce(&Visit<'_>) -> Result<T, Error>,
) -> Result<T, Error> {
    let Some((previous, previous_pid)) = spi.front_process() else {
        return Err(Error::Refused(Refusal::BackgroundUnavailable {
            detail: "the front app could not be read, so background input could not keep the \
                     user's focus"
                .into(),
        }));
    };
    if previous_pid == Some(pid) {
        return action(&Visit::NONE);
    }
    let key = previous_pid.and_then(|user| ax::focused_window_id(spi, user));
    let stopped = AtomicBool::new(false);
    let visited = AtomicBool::new(false);
    let lease = Lease {
        spi,
        previous,
        key,
        target: pid,
        baseline: Presses::read(),
        since: uptime_ns(),
    };
    thread::scope(|scope| {
        let sampler = thread::Builder::new()
            .name("eukhe-desktop-focus-guard".to_owned())
            .spawn_scoped(scope, || lease.sample(&stopped, &visited))
            .map_err(|error| {
                Error::Refused(Refusal::BackgroundUnavailable {
                    detail: format!("the focus guard did not start: {error}").into(),
                })
            })?;
        let result = action(&Visit(Some(&visited)));
        thread::sleep(SETTLE);
        stopped.store(true, Ordering::Release);
        let outcome = sampler.join().unwrap_or(Outcome::RestoreRejected);
        match (result, outcome) {
            (result, Outcome::Kept) | (result @ Err(_), Outcome::RestoreRejected) => result,
            (Ok(_), Outcome::RestoreRejected) => Err(Error::Unverified(Unverified::InputFailed {
                detail: "the input went out, but the target came in front and WindowServer \
                         refused to put the user's app back"
                    .into(),
            })),
        }
    })
}

struct Lease<'s> {
    spi: &'s Spi,
    previous: Psn,
    key: Option<u32>,
    target: i32,
    baseline: Presses,
    /// When the guard began, in uptime nanoseconds: a hand-back after the
    /// user's own press or click since is refused by `WindowServer`.
    since: u64,
}

impl Lease<'_> {
    fn sample(&self, stopped: &AtomicBool, visited: &AtomicBool) -> Outcome {
        let mut armed = Armed::Armed;
        let mut outcome = Outcome::Kept;
        loop {
            // One last read after the stop, so an app that came forward in
            // the settle's last moments is still sent back.
            let last = stopped.load(Ordering::Acquire);
            if let Some(front) = self.spi.front_process() {
                match decide(front, self.previous, self.target, self.choice(), armed) {
                    Decision::Keep => {}
                    Decision::Disarm { visited: target } => {
                        armed = Armed::Disarmed;
                        if target {
                            visited.store(true, Ordering::Release);
                        }
                    }
                    Decision::Restore => outcome = self.restore(&mut armed, visited, front.1),
                }
            }
            if last {
                return outcome;
            }
            thread::sleep(SAMPLE);
        }
    }

    fn choice(&self) -> Choice {
        if Presses::read() != self.baseline || quartz::hid_flags() & SWITCH_FLAGS != 0 {
            Choice::Chose
        } else {
            Choice::Untouched
        }
    }

    fn restore(&self, armed: &mut Armed, visited: &AtomicBool, front: Option<i32>) -> Outcome {
        let wid = self.key.unwrap_or(0);
        match self
            .spi
            .set_front_unless_user_acted(self.previous, wid, CPS_NO_WINDOWS, self.since)
        {
            FrontRequest::Done => {
                if let Some(key) = self.key {
                    // A key window not restored only leaves the user's app
                    // in front with another of its windows key.
                    self.spi.make_key(self.previous, key);
                }
                Outcome::Kept
            }
            FrontRequest::UserActed => {
                *armed = Armed::Disarmed;
                if front == Some(self.target) {
                    visited.store(true, Ordering::Release);
                }
                Outcome::Kept
            }
            FrontRequest::Rejected => Outcome::RestoreRejected,
        }
    }
}

/// Before each later press of background input: refuses once the user
/// came to the target app (`visit`), or it is in front now.
pub(super) fn still_behind(
    spi: &Spi,
    pid: i32,
    app: &str,
    visit: &Visit<'_>,
    sent: Sent,
) -> Result<(), Error> {
    let front = spi.front_process().and_then(|(_, front)| front);
    if !visit.happened() && front != Some(pid) {
        return Ok(());
    }
    Err(match sent {
        Sent::Nothing => Error::from(Intervention::DuringInput {
            app: app.to_owned(),
        }),
        Sent::Some => Error::Unverified(Unverified::Interrupted(Interruption::UserInput {
            app: app.to_owned(),
        })),
    })
}

/// Waits until `ready` holds, reading it every `poll`, at most `timeout`.
pub(super) fn wait_for(timeout: Duration, poll: Duration, mut ready: impl FnMut() -> bool) -> bool {
    let deadline = Instant::now() + timeout;
    loop {
        if ready() {
            return true;
        }
        if Instant::now() >= deadline {
            return false;
        }
        thread::sleep(poll);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn psn(low: u32) -> Psn {
        Psn::for_test(low)
    }

    #[test]
    fn the_guard_sends_back_an_app_the_input_brought_forward() {
        let user = psn(1);
        let target = (psn(2), Some(42));
        assert_eq!(
            decide((user, Some(7)), user, 42, Choice::Untouched, Armed::Armed),
            Decision::Keep
        );
        assert_eq!(
            decide(target, user, 42, Choice::Untouched, Armed::Armed),
            Decision::Restore
        );
    }

    #[test]
    fn the_users_own_pick_disarms_the_guard_and_marks_a_visit() {
        let user = psn(1);
        let target = (psn(2), Some(42));
        let third = (psn(3), Some(9));
        assert_eq!(
            decide(target, user, 42, Choice::Chose, Armed::Armed),
            Decision::Disarm { visited: true }
        );
        assert_eq!(
            decide(third, user, 42, Choice::Chose, Armed::Armed),
            Decision::Disarm { visited: false }
        );
        // Once disarmed it never fights the user again.
        assert_eq!(
            decide(target, user, 42, Choice::Untouched, Armed::Disarmed),
            Decision::Disarm { visited: true }
        );
    }
}
