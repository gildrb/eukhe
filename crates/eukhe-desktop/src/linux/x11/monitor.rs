//! The user's own key presses and clicks, read from XI2 raw events on a
//! thread of their own (port of omp `crates/natives/src/desktop/linux/x11/activity.rs`,
//! `x11/listener.rs` and `control/linux.rs`).
//!
//! XTEST devices carry this session's input (the pair's and takeover's) and
//! are never the user's; tools that type through XTEST (xdotool, x11vnc)
//! are not seen either.

use std::collections::HashSet;
use std::sync::mpsc::{self, RecvTimeoutError};
use std::sync::Arc;
use std::time::{Duration, Instant};

use x11rb::connection::Connection;
use x11rb::protocol::screensaver::ConnectionExt as _;
use x11rb::protocol::xinput::{self, ConnectionExt as _, XIEventMask};
use x11rb::protocol::xproto::ConnectionExt as _;
use x11rb::protocol::Event;

use super::keymap::Keysym;
use super::{XError, XWindow, X11};
use crate::control::intervention::UserInputs;
use crate::control::EmergencyStop;
use crate::error::{Error, Feature, Refusal};
use crate::types::{Pid, Support};

/// How often a watch checks whether its owner let go.
const POLL: Duration = Duration::from_millis(15);
const ESCAPE: Keysym = Keysym(0xff1b);

/// One press of the user's.
enum Press {
    Key { code: u32 },
    Button,
}

/// Feeds the user's key presses and clicks into the session until dropped.
pub(crate) struct UserInputMonitor {
    _stop: mpsc::Sender<()>,
}

impl UserInputMonitor {
    pub(crate) fn start(inputs: Arc<UserInputs>) -> Result<Self, Error> {
        let stop = watch("eukhe-desktop-input", Feature::UserInputWatch, move |x| {
            let idle = x
                .conn
                .screensaver_query_info(x.root)
                .ok()
                .and_then(|cookie| cookie.reply().ok())
                .map(|info| Duration::from_millis(u64::from(info.ms_since_user_input)));
            inputs.monitor_started(Instant::now(), idle);
            move |x: &X11, press: Press| {
                let now = Instant::now();
                inputs.pressed(now);
                if let Some(pid) = pressed_in(x, &press) {
                    inputs.record(pid, now);
                }
            }
        })?;
        Ok(Self { _stop: stop })
    }
}

/// Stops takeover input on the user's physical Escape until dropped.
pub(crate) struct EscapeMonitor {
    _stop: mpsc::Sender<()>,
}

impl EscapeMonitor {
    pub(crate) fn start(stop: EmergencyStop) -> Result<Self, Error> {
        let sender = watch("eukhe-desktop-escape", Feature::EscapeStop, move |_| {
            move |x: &X11, press: Press| {
                // Read on each press: the layout may change under the watch.
                let escape = x
                    .keymap()
                    .ok()
                    .and_then(|keymap| keymap.find(ESCAPE))
                    .map(|(code, _)| u32::from(code.0));
                if let Press::Key { code } = press {
                    if Some(code) == escape {
                        stop.escape();
                    }
                }
            }
        })?;
        Ok(Self { _stop: sender })
    }
}

/// The process of the window a press went to: the focused window for a
/// key, the one under the pointer for a click.
fn pressed_in(x: &X11, press: &Press) -> Option<Pid> {
    let top = match press {
        Press::Key { .. } => x.frame_of(XWindow(x.focused()?)),
        Press::Button => {
            let child = x.conn.query_pointer(x.root).ok()?.reply().ok()?.child;
            (child != x11rb::NONE).then_some(XWindow(child))?
        }
    };
    x.pid(x.client_of(top))
}

/// The ids of the XTEST devices, which the server marks with a property.
fn xtest_devices(x: &X11) -> Result<HashSet<xinput::DeviceId>, XError> {
    let devices = x
        .conn
        .xinput_xi_query_device(xinput::Device::ALL)?
        .reply()?;
    Ok(devices
        .infos
        .iter()
        .map(|info| info.deviceid)
        .filter(|device| {
            x.conn
                .xinput_xi_get_property(*device, false, x.atoms.XTEST_DEVICE, 0u32, 0, 1)
                .ok()
                .and_then(|cookie| cookie.reply().ok())
                .is_some_and(|reply| reply.type_ != x11rb::NONE)
        })
        .collect())
}

/// Starts a thread with its own X connection reading raw presses; `setup`
/// runs on it once and returns the press handler. The thread ends once the
/// returned sender is dropped.
fn watch<S, H>(name: &str, feature: Feature, setup: S) -> Result<mpsc::Sender<()>, Error>
where
    S: FnOnce(&X11) -> H + Send + 'static,
    H: FnMut(&X11, Press),
{
    let (stop, stopped) = mpsc::channel::<()>();
    let (ready, started) = mpsc::sync_channel::<Result<(), Error>>(1);
    std::thread::Builder::new()
        .name(name.to_owned())
        .spawn(move || {
            let x = match listen(feature) {
                Ok(x) => x,
                Err(error) => {
                    ready.send(Err(error)).ok();
                    return;
                }
            };
            let handle = setup(&x);
            ready.send(Ok(())).ok();
            run(&x, &stopped, handle);
        })
        .map_err(|error| {
            Error::Refused(Refusal::Platform {
                detail: format!("cannot start the input watch: {error}").into(),
            })
        })?;
    started.recv().map_err(|_| {
        Error::Refused(Refusal::Platform {
            detail: "the input watch ended while starting".into(),
        })
    })??;
    Ok(stop)
}

/// A connection selecting raw key and button presses on the root.
fn listen(feature: Feature) -> Result<X11, Error> {
    let x = X11::open()?;
    match x.extensions.xinput {
        Support::Supported => {}
        Support::Unsupported => return Err(Error::unsupported(feature)),
    }
    // The server takes hierarchy events only for all devices.
    let presses = XIEventMask::RAW_KEY_PRESS | XIEventMask::RAW_BUTTON_PRESS;
    x.conn
        .xinput_xi_select_events(
            x.root,
            &[
                xinput::EventMask {
                    deviceid: xinput::Device::ALL_MASTER.into(),
                    mask: vec![presses],
                },
                xinput::EventMask {
                    deviceid: xinput::Device::ALL.into(),
                    mask: vec![XIEventMask::HIERARCHY],
                },
            ],
        )
        .map_err(XError::from)?
        .check()
        .map_err(XError::from)?;
    Ok(x)
}

fn run(x: &X11, stopped: &mpsc::Receiver<()>, mut handle: impl FnMut(&X11, Press)) {
    let Ok(mut xtest) = xtest_devices(x) else {
        return;
    };
    loop {
        loop {
            let event = match x.conn.poll_for_event() {
                Ok(Some(event)) => event,
                Ok(None) => break,
                // The server went away: nothing more to watch.
                Err(_) => return,
            };
            match event {
                Event::XinputRawKeyPress(raw) if !xtest.contains(&raw.sourceid) => {
                    handle(x, Press::Key { code: raw.detail });
                }
                Event::XinputRawButtonPress(raw) if !xtest.contains(&raw.sourceid) => {
                    handle(x, Press::Button);
                }
                // Device ids are reused once a device goes.
                Event::XinputHierarchy(_) => match xtest_devices(x) {
                    Ok(devices) => xtest = devices,
                    Err(_) => return,
                },
                _ => {}
            }
        }
        match stopped.recv_timeout(POLL) {
            Err(RecvTimeoutError::Timeout) => {}
            Ok(()) | Err(RecvTimeoutError::Disconnected) => return,
        }
    }
}
