//! Listen-only watches on the user's own input: their key presses and
//! clicks per app, and the physical Escape that stops takeover input (port
//! of omp `crates/natives/src/desktop/control/macos.rs`).

use std::sync::Arc;
use std::time::Instant;

use super::ffi::quartz;
use super::ffi::tap::{Tap, TapError, TapEvent};
use super::input::SYNTHETIC_TAG;
use crate::control::intervention::UserInputs;
use crate::control::EmergencyStop;
use crate::error::{Error, Feature, Permission, Refusal};
use crate::types::Pid;

const LEFT_MOUSE_DOWN: u32 = 1;
const RIGHT_MOUSE_DOWN: u32 = 3;
const OTHER_MOUSE_DOWN: u32 = 25;
const KEY_DOWN: u32 = 10;
const ESCAPE: i64 = 53;

/// The user's own input: from their devices (no source process), never one
/// of this backend's tagged events.
const fn physical(event: &TapEvent) -> bool {
    event.source_pid == 0 && event.user_data != SYNTHETIC_TAG
}

const fn physical_escape(event: &TapEvent) -> bool {
    physical(event) && event.kind == KEY_DOWN && event.keycode == ESCAPE
}

/// The app a physical event went to, as the annotated tap names it.
fn target(event: &TapEvent) -> Option<Pid> {
    u32::try_from(event.target_pid)
        .ok()
        .filter(|pid| *pid > 0)
        .map(Pid)
}

fn tap_error(error: TapError, feature: Feature) -> Error {
    match error {
        TapError::Refused => Error::Refused(Refusal::NotPermitted {
            permission: Permission::InputMonitoring,
        }),
        TapError::Thread(error) => Error::Refused(Refusal::Platform {
            detail: format!("the {feature} thread did not start: {error}").into(),
        }),
    }
}

/// Feeds the user's key presses and clicks into the session until dropped.
pub(crate) struct UserInputMonitor {
    _tap: Tap,
}

impl UserInputMonitor {
    pub(crate) fn start(inputs: Arc<UserInputs>) -> Result<Self, Error> {
        if !quartz::listen_event_access() {
            return Err(Error::Refused(Refusal::NotPermitted {
                permission: Permission::InputMonitoring,
            }));
        }
        // The user's input before the tap sees any: idle time stands in for
        // their latest press.
        inputs.monitor_started(Instant::now(), Some(quartz::press_idle()));
        let tap = Tap::listen(
            "eukhe-desktop-user-input",
            &[
                LEFT_MOUSE_DOWN,
                RIGHT_MOUSE_DOWN,
                OTHER_MOUSE_DOWN,
                KEY_DOWN,
            ],
            move |event| {
                if !physical(event) {
                    return;
                }
                let now = Instant::now();
                inputs.pressed(now);
                if let Some(pid) = target(event) {
                    inputs.record(pid, now);
                }
            },
        )
        .map_err(|error| tap_error(error, Feature::UserInputWatch))?;
        Ok(Self { _tap: tap })
    }
}

/// Stops takeover input on the user's physical Escape until dropped.
pub(crate) struct EscapeMonitor {
    _tap: Tap,
}

impl EscapeMonitor {
    /// `Unsupported` without event-listening access or under Secure Event
    /// Input, which hides every key from taps: takeover then runs without it.
    pub(crate) fn start(stop: EmergencyStop) -> Result<Self, Error> {
        if !quartz::listen_event_access() || quartz::session().secure_input.is_some() {
            return Err(Error::unsupported(Feature::EscapeStop));
        }
        let tap = Tap::listen("eukhe-desktop-escape", &[KEY_DOWN], move |event| {
            if physical_escape(event) {
                stop.escape();
            }
        })
        .map_err(|error| tap_error(error, Feature::EscapeStop))?;
        Ok(Self { _tap: tap })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn event(kind: u32, keycode: i64, source_pid: i64, user_data: i64) -> TapEvent {
        TapEvent {
            kind,
            keycode,
            flags: 0,
            source_pid,
            user_data,
            target_pid: 42,
        }
    }

    #[test]
    fn only_the_users_own_escape_stops_a_takeover() {
        assert!(physical_escape(&event(KEY_DOWN, ESCAPE, 0, 0)));
        // Posted by a process, or tagged as this backend's own.
        assert!(!physical_escape(&event(KEY_DOWN, ESCAPE, 77, 0)));
        assert!(!physical_escape(&event(KEY_DOWN, ESCAPE, 0, SYNTHETIC_TAG)));
        assert!(!physical_escape(&event(KEY_DOWN, 0, 0, 0)));
    }

    #[test]
    fn a_physical_press_counts_for_the_app_it_went_to() {
        assert_eq!(target(&event(LEFT_MOUSE_DOWN, 0, 0, 0)), Some(Pid(42)));
        let mut unrouted = event(KEY_DOWN, 0, 0, 0);
        unrouted.target_pid = 0;
        assert_eq!(target(&unrouted), None);
    }
}
