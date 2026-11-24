//! The Linux backend: X11 (input, capture, window list) and AT-SPI
//! (accessibility). Seam stubs until the backend lands; see
//! `crate::backend` for the contract.
#![allow(
    dead_code,
    clippy::unused_self,
    clippy::unnecessary_wraps,
    reason = "seam stubs: the backend constructs these types, reads self and fails"
)]

use std::path::Path;
use std::sync::Arc;

use crate::applications::{Activation, AppKind, Application, Document, Opened};
use crate::ax::{ActionNames, AxProps, AxRead, Liveness, Settable, WalkBounds};
use crate::backend::{Delivery, PointerEvent, SelectionReadback, Typing, ValueReadback};
use crate::control::intervention::{Held, StartTime, UserInputs};
use crate::control::{EmergencyStop, Token};
use crate::error::{Error, Feature};
use crate::frame::Capture;
use crate::menus::MenuItem;
use crate::roster::RosterWindow;
use crate::text_range::Utf16Range;
use crate::types::{
    Access, BackendKind, Capabilities, DisplayPower, Lock, Pid, ScreenState, SecureInput, Support,
    Window,
};

pub(crate) const BACKEND: BackendKind = BackendKind::X11;
/// AT-SPI action names are provider-defined: lines list none.
pub(crate) const ACTION_NAMES: ActionNames = ActionNames::Hidden;
pub(crate) const OPENS_DOCUMENTS: Support = Support::Unsupported;

/// An AT-SPI element: bus name and object path.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct AxHandle;

/// The X11 connection and AT-SPI bus of one session.
pub(crate) struct Backend;

impl Backend {
    pub(crate) fn open() -> Result<Self, Error> {
        Ok(Self)
    }

    pub(crate) fn capabilities(&mut self) -> Capabilities {
        Capabilities {
            backend: BACKEND,
            capture: Access::Unknown,
            input: Access::Unknown,
            accessibility: Access::Unknown,
            background_input: Support::Unsupported,
            takeover: Support::Unsupported,
            menus: Support::Unsupported,
            applications: Support::Unsupported,
            escape_stop: Support::Unsupported,
            secure_input: SecureInput::Off,
            screen: ScreenState {
                lock: Lock::Unlocked,
                display: DisplayPower::Awake,
            },
        }
    }

    pub(crate) fn windows(&mut self) -> Result<Vec<Window>, Error> {
        Err(Error::unsupported(Feature::Windows))
    }

    pub(crate) fn capture(&mut self, _: &Window) -> Result<Capture, Error> {
        Err(Error::unsupported(Feature::Capture))
    }

    pub(crate) fn input_held(&mut self) -> Held {
        Held::Unknown
    }

    pub(crate) fn admit_takeover(&mut self, _: &Token) -> Result<(), Error> {
        Err(Error::unsupported(Feature::Takeover))
    }

    pub(crate) fn press(&mut self, _: &AxHandle, _: &Delivery<'_>) -> Result<(), Error> {
        Err(Error::unsupported(Feature::Input))
    }

    pub(crate) fn set_value(
        &mut self,
        _: &AxHandle,
        _: &str,
        _: &Delivery<'_>,
    ) -> Result<ValueReadback, Error> {
        Err(Error::unsupported(Feature::Input))
    }

    pub(crate) fn element_input(
        &mut self,
        _: &AxHandle,
        _: Typing<'_>,
        _: &Delivery<'_>,
    ) -> Result<(), Error> {
        Err(Error::unsupported(Feature::Input))
    }

    pub(crate) fn text_value(&mut self, _: &AxHandle) -> Result<String, Error> {
        Err(Error::unsupported(Feature::Accessibility))
    }

    pub(crate) fn select_range(
        &mut self,
        _: &AxHandle,
        _: Utf16Range,
        _: &Delivery<'_>,
    ) -> Result<SelectionReadback, Error> {
        Err(Error::unsupported(Feature::TextSelection))
    }

    pub(crate) fn window_input(
        &mut self,
        _: &Window,
        _: Typing<'_>,
        _: &Delivery<'_>,
    ) -> Result<(), Error> {
        Err(Error::unsupported(Feature::Input))
    }

    pub(crate) fn pointer(
        &mut self,
        _: &Window,
        _: &PointerEvent,
        _: &Delivery<'_>,
    ) -> Result<(), Error> {
        Err(Error::unsupported(Feature::Input))
    }

    pub(crate) fn menu_items(&mut self, _: &Window, _: &[String]) -> Result<Vec<MenuItem>, Error> {
        Err(Error::unsupported(Feature::Menus))
    }

    pub(crate) fn menu_press(
        &mut self,
        _: &Window,
        _: &[String],
        _: &Delivery<'_>,
    ) -> Result<(), Error> {
        Err(Error::unsupported(Feature::Menus))
    }
}

impl AxRead for Backend {
    type Handle = AxHandle;

    fn window_root(&mut self, _: &Window) -> Result<AxHandle, Error> {
        Err(Error::unsupported(Feature::Accessibility))
    }

    fn walk_node(
        &mut self,
        _: &AxHandle,
        _: WalkBounds,
        _: u32,
    ) -> Result<(AxProps, Vec<AxHandle>), Error> {
        Err(Error::unsupported(Feature::Accessibility))
    }

    fn props(&mut self, _: &AxHandle) -> Result<AxProps, Error> {
        Err(Error::unsupported(Feature::Accessibility))
    }

    fn liveness(&mut self, _: &AxHandle) -> Liveness {
        Liveness::Gone
    }

    fn focused_within(&mut self, _: &AxHandle) -> Option<AxHandle> {
        None
    }

    fn value_settable(&mut self, _: &AxHandle) -> Settable {
        Settable::Unknown
    }
}

pub(crate) fn list_applications() -> Result<Vec<Application>, Error> {
    Err(Error::unsupported(Feature::Applications))
}

pub(crate) fn application_at(_: &Path) -> Result<Application, Error> {
    Err(Error::unsupported(Feature::Applications))
}

/// Desktop entries list no helpers apart from their applications.
pub(crate) fn app_kind(_: &Application) -> AppKind {
    AppKind::Regular
}

pub(crate) fn open_application(_: &Application, _: Activation) -> Result<Opened, Error> {
    Err(Error::unsupported(Feature::Applications))
}

pub(crate) fn open_document(_: &str, _: &Document<'_>, _: Activation) -> Result<Opened, Error> {
    Err(Error::unsupported(Feature::Documents))
}

pub(crate) fn window_roster() -> Result<Vec<RosterWindow>, Error> {
    Err(Error::unsupported(Feature::Roster))
}

pub(crate) fn process_started(_: Pid) -> Option<StartTime> {
    None
}

/// Feeds the user's key presses and clicks into the session until dropped.
pub(crate) struct UserInputMonitor;

impl UserInputMonitor {
    pub(crate) fn start(_: Arc<UserInputs>) -> Result<Self, Error> {
        Err(Error::unsupported(Feature::UserInputWatch))
    }
}

/// Stops takeover input on the user's physical Escape until dropped.
pub(crate) struct EscapeMonitor;

impl EscapeMonitor {
    pub(crate) fn start(_: EmergencyStop) -> Result<Self, Error> {
        Err(Error::unsupported(Feature::EscapeStop))
    }
}
