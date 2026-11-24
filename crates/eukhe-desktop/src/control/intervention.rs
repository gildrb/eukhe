//! The user's own keys and clicks in the apps a session works in (port of
//! omp `crates/natives/src/desktop/control/intervention.rs`).
//!
//! Input aimed at an app the user has used since the session last read it
//! waits for them to pause, then fails without sending, so the agent reads
//! the window again; input under way stops at the user's first key or
//! click. A takeover first waits until the user has paused in every app.
//!
//! Shared state, and why: the platform monitor's thread records the user's
//! input into [`UserInputs`] while the session worker reads it.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};
use std::time::{Duration, Instant};

use super::{Sent, Token};
use crate::error::{Error, Interruption, Intervention, Unverified};
use crate::platform;
use crate::types::Pid;

/// How long the user leaves keyboard and pointer alone before input goes to
/// an app they used, or a takeover brings its target in front of them.
pub(crate) const QUIET: Duration = Duration::from_secs(5);
/// How often a takeover waiting on a key the user holds checks again.
const HELD_POLL: Duration = Duration::from_millis(50);

/// When a process started, in the platform's units: a later process reusing
/// an id starts later.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct StartTime(pub(crate) u64);

/// Reads when a process started.
type Started = fn(Pid) -> Option<StartTime>;

/// Whether the user holds a key or button down now.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code, reason = "the platform backends report every variant")]
pub(crate) enum Held {
    Holding,
    Released,
    /// The backend cannot see held input; nothing waits on it.
    Unknown,
}

struct App {
    name: String,
    started: Option<StartTime>,
    /// The user's presses and clicks since the session first touched it.
    inputs: u64,
    /// When the user last pressed or clicked there, until a read shows it.
    unread: Option<Instant>,
}

/// A process that takes input for a watched app's windows, such as the
/// service drawing its Open panel.
struct Route {
    app: Pid,
    started: Option<StartTime>,
}

#[derive(Default)]
struct State {
    apps: HashMap<Pid, App>,
    routes: HashMap<Pid, Route>,
    /// The user's presses and clicks in any app.
    presses: u64,
    last_press: Option<Instant>,
}

/// The user's input into each app the session touched, shared by the
/// platform monitor thread (writer) and the session worker (reader).
pub(crate) struct UserInputs {
    state: Mutex<State>,
    started: Started,
}

impl UserInputs {
    fn new(started: Started) -> Self {
        Self {
            state: Mutex::default(),
            started,
        }
    }

    fn state(&self) -> MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// The user pressed a key or clicked at `at`, in any app.
    pub(crate) fn pressed(&self, at: Instant) {
        let mut state = self.state();
        state.presses += 1;
        state.last_press = state.last_press.max(Some(at));
    }

    /// The monitor started at `at` and saw none of the user's earlier input:
    /// the system idle time `idle` stands in for their latest press.
    pub(crate) fn monitor_started(&self, at: Instant, idle: Option<Duration>) {
        self.pressed(idle.and_then(|idle| at.checked_sub(idle)).unwrap_or(at));
    }

    /// The user pressed a key or clicked in process `pid` at `at`.
    pub(crate) fn record(&self, pid: Pid, at: Instant) {
        let started = (self.started)(pid);
        let mut state = self.state();
        let app = match state
            .routes
            .get(&pid)
            .map(|route| (route.app, route.started))
        {
            Some((app, route_started)) if route_started == started => app,
            // Another process now has the route's id: its input is its own.
            Some(_) => {
                state.routes.remove(&pid);
                pid
            }
            None => pid,
        };
        if let Some(app) = state.apps.get_mut(&app) {
            app.inputs += 1;
            app.unread = Some(at);
        }
    }

    /// Starts recording the user's input into `pid`. A former process under
    /// the same id is forgotten.
    fn touch(&self, pid: Pid, name: &str) {
        let started = (self.started)(pid);
        let mut state = self.state();
        if state
            .apps
            .get(&pid)
            .is_some_and(|app| app.started == started)
        {
            return;
        }
        state.apps.insert(
            pid,
            App {
                name: name.to_owned(),
                started,
                inputs: 0,
                unread: None,
            },
        );
        state.routes.retain(|_, route| route.app != pid);
    }

    /// Counts the user's input into `input` as input into `app`.
    fn route(&self, input: Pid, app: Pid) {
        if input != app {
            let started = (self.started)(input);
            self.state().routes.insert(input, Route { app, started });
        }
    }

    /// A read of `pid`'s window that began at `began` reached the caller. It
    /// shows the user's input only if they had paused for [`QUIET`] by then.
    fn read(&self, pid: Pid, began: Instant) {
        if let Some(app) = self.state().apps.get_mut(&pid) {
            if app
                .unread
                .is_some_and(|last| began.saturating_duration_since(last) >= QUIET)
            {
                app.unread = None;
            }
        }
    }

    /// Admits input to `pid`: input to an app holding input no read showed
    /// waits until the user paused for [`QUIET`], at most one quiet period,
    /// then fails without sending.
    fn admit(
        self: &Arc<Self>,
        pid: Pid,
        now: impl Fn() -> Instant,
        mut wait: impl FnMut(Duration) -> Result<(), Error>,
    ) -> Result<InputWatch, Error> {
        let limit = now() + QUIET;
        loop {
            let (baseline, unread) = self.state().apps.get(&pid).map_or((0, None), |app| {
                (app.inputs, app.unread.map(|last| (last, app.name.clone())))
            });
            let Some((last, app)) = unread else {
                return Ok(InputWatch::Watching {
                    inputs: Arc::clone(self),
                    pid,
                    baseline,
                });
            };
            let now = now();
            let idle = now.saturating_duration_since(last);
            if idle >= QUIET {
                return Err(Intervention::Used { app, idle }.into());
            }
            if now >= limit {
                return Err(Intervention::StillUsing { app, idle }.into());
            }
            wait((last + QUIET).min(limit).saturating_duration_since(now))?;
        }
    }

    /// Waits until the user has pressed nothing for [`QUIET`] in any app; a
    /// key they hold makes no presses, so the quiet runs from its release.
    /// Returns the press count a takeover compares against.
    fn pause_before_takeover(
        &self,
        limit: Instant,
        now: impl Fn() -> Instant,
        mut held: impl FnMut() -> Held,
        mut wait: impl FnMut(Duration) -> Result<(), Error>,
    ) -> Result<u64, Error> {
        let mut held_at = None;
        loop {
            let (presses, last) = {
                let state = self.state();
                (state.presses, state.last_press)
            };
            let now = now();
            let holding = held();
            if holding == Held::Holding {
                held_at = Some(now);
            }
            let Some(last) = last.max(held_at) else {
                return Ok(presses);
            };
            let idle = now.saturating_duration_since(last);
            if idle >= QUIET {
                return Ok(presses);
            }
            if now >= limit {
                return Err(Intervention::StillActive { idle }.into());
            }
            let quiet = (last + QUIET).min(limit).saturating_duration_since(now);
            wait(match holding {
                Held::Holding => HELD_POLL.min(quiet),
                Held::Released | Held::Unknown => quiet,
            })?;
        }
    }

    fn presses(&self) -> u64 {
        self.state().presses
    }
}

/// An admitted step's watch on the user's input into its app.
pub(crate) enum InputWatch {
    /// No monitor runs, or the window's process is unknown.
    Unwatched,
    Watching {
        inputs: Arc<UserInputs>,
        pid: Pid,
        /// The app's input count when the step was admitted.
        baseline: u64,
    },
}

impl InputWatch {
    /// Before each press: refuses once the user pressed or clicked in the
    /// app since admission, so at most the press under way lands after
    /// theirs.
    pub(crate) fn check_press(&self, sent: Sent) -> Result<(), Error> {
        let Self::Watching {
            inputs,
            pid,
            baseline,
        } = self
        else {
            return Ok(());
        };
        let app = match inputs.state().apps.get(pid) {
            Some(app) if app.inputs != *baseline => app.name.clone(),
            Some(_) | None => return Ok(()),
        };
        Err(match sent {
            Sent::Nothing => Intervention::DuringInput { app }.into(),
            Sent::Some => {
                Error::Unverified(Unverified::Interrupted(Interruption::UserInput { app }))
            }
        })
    }

    /// The step sends its input to process `input`, such as the service
    /// drawing its window's Open panel: the user's input there counts.
    #[allow(dead_code, reason = "called by the platform backends")]
    pub(crate) fn input_goes_to(&self, input: Pid) {
        if let Self::Watching { inputs, pid, .. } = self {
            inputs.route(input, *pid);
        }
    }

    /// Before a takeover brings its target forward: waits until the user
    /// paused in every app, at most one quiet period, then rechecks that
    /// they pressed and hold nothing since.
    pub(crate) fn admit_takeover(
        &self,
        token: &Token,
        mut held: impl FnMut() -> Held,
    ) -> Result<(), Error> {
        let Self::Watching { inputs, .. } = self else {
            return Ok(());
        };
        let presses = inputs.pause_before_takeover(
            Instant::now() + QUIET,
            Instant::now,
            &mut held,
            |duration| token.wait(duration),
        )?;
        if inputs.presses() != presses || held() == Held::Holding {
            return Err(Intervention::TakeoverStart.into());
        }
        Ok(())
    }
}

enum Tap {
    Off,
    Running(
        #[allow(dead_code, reason = "dropping it stops the monitor")] platform::UserInputMonitor,
    ),
}

/// The session's record of the user's input and the monitor feeding it. The
/// monitor starts when the session first reads or acts on an app.
pub(crate) struct Listener {
    inputs: Arc<UserInputs>,
    tap: Tap,
}

impl Default for Listener {
    fn default() -> Self {
        Self {
            inputs: Arc::new(UserInputs::new(platform::process_started)),
            tap: Tap::Off,
        }
    }
}

impl Listener {
    /// Starts the monitor if it is off. Without event-listening access it
    /// stays off and input goes unwatched, as with no monitor at all.
    fn start(&mut self) {
        if let Tap::Off = self.tap {
            if let Ok(monitor) = platform::UserInputMonitor::start(Arc::clone(&self.inputs)) {
                self.tap = Tap::Running(monitor);
            }
        }
    }

    /// Records the user's input into `pid` (named `app`) from now on.
    pub(crate) fn touch(&mut self, pid: Pid, app: &str) {
        self.start();
        self.inputs.touch(pid, app);
    }

    /// A read of `pid`'s window that began at `began` reached the caller.
    pub(crate) fn read(&self, pid: Pid, began: Instant) {
        self.inputs.read(pid, began);
    }

    /// Admits input to `pid`, waiting while the user is still using it;
    /// a cancel ends the wait.
    pub(crate) fn admit(&self, pid: Pid, token: &Token) -> Result<InputWatch, Error> {
        match self.tap {
            Tap::Off => Ok(InputWatch::Unwatched),
            Tap::Running(_) => self
                .inputs
                .admit(pid, Instant::now, |duration| token.wait(duration)),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use super::*;

    fn unknown(_: Pid) -> Option<StartTime> {
        None
    }

    /// A clock that the waits advance.
    struct Clock {
        start: Instant,
        offset: Cell<Duration>,
    }

    impl Clock {
        fn new() -> Self {
            Self {
                start: Instant::now(),
                offset: Cell::new(Duration::ZERO),
            }
        }

        fn now(&self) -> Instant {
            self.start + self.offset.get()
        }

        /// A wait that advances this clock instead of sleeping.
        fn wait(&self) -> impl FnMut(Duration) -> Result<(), Error> + '_ {
            |by| {
                self.offset.set(self.offset.get() + by);
                Ok(())
            }
        }
    }

    #[test]
    fn input_into_an_app_the_user_just_used_waits_then_refuses() {
        let inputs = Arc::new(UserInputs::new(unknown));
        let clock = Clock::new();
        inputs.touch(Pid(9), "Notes");
        inputs.record(Pid(9), clock.now());
        let refused = inputs
            .admit(Pid(9), || clock.now(), clock.wait())
            .map(|_| ());
        assert_eq!(
            refused,
            Err(Error::from(Intervention::Used {
                app: "Notes".to_owned(),
                idle: QUIET
            }))
        );
        inputs.read(Pid(9), clock.now());
        assert!(inputs.admit(Pid(9), || clock.now(), clock.wait()).is_ok());
    }

    #[test]
    fn a_press_during_input_stops_it() {
        let inputs = Arc::new(UserInputs::new(unknown));
        let clock = Clock::new();
        inputs.touch(Pid(3), "Mail");
        let watch = inputs
            .admit(Pid(3), || clock.now(), clock.wait())
            .unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(watch.check_press(Sent::Nothing), Ok(()));
        inputs.record(Pid(3), clock.now());
        assert_eq!(
            watch.check_press(Sent::Some),
            Err(Error::Unverified(Unverified::Interrupted(
                Interruption::UserInput {
                    app: "Mail".to_owned()
                }
            )))
        );
    }

    #[test]
    fn a_takeover_waits_for_the_user_to_pause_everywhere() {
        let inputs = UserInputs::new(unknown);
        let clock = Clock::new();
        inputs.pressed(clock.now());
        let presses = inputs.pause_before_takeover(
            clock.now() + QUIET * 2,
            || clock.now(),
            || Held::Released,
            clock.wait(),
        );
        assert_eq!(presses, Ok(1));
        assert_eq!(clock.offset.get(), QUIET);
        inputs.pressed(clock.now());
        assert_eq!(
            inputs.pause_before_takeover(
                clock.now(),
                || clock.now(),
                || Held::Released,
                clock.wait(),
            ),
            Err(Error::from(Intervention::StillActive {
                idle: Duration::ZERO
            }))
        );
    }
}
