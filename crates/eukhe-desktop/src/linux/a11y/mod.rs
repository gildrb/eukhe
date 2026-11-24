//! AT-SPI accessibility over the accessibility bus: element reads, actions,
//! text and value writes (port of omp `crates/natives/src/desktop/linux/ax.rs`).

mod menus;
mod text;

use std::hash::{DefaultHasher, Hash, Hasher};
use std::time::Duration;

use atspi::proxy::accessible::AccessibleProxyBlocking;
use atspi::proxy::action::ActionProxyBlocking;
use atspi::proxy::application::ApplicationProxyBlocking;
use atspi::proxy::bus::BusProxyBlocking;
use atspi::proxy::component::ComponentProxyBlocking;
use atspi::proxy::editable_text::EditableTextProxyBlocking;
use atspi::proxy::text::TextProxyBlocking;
use atspi::proxy::value::ValueProxyBlocking;
use atspi::{CoordType, Interface, InterfaceSet, ObjectRefOwned, State, StateSet};
use zbus::blocking::Connection;
use zbus::names::{BusName, UniqueName};
use zbus::proxy::CacheProperties;
use zbus::zvariant::ObjectPath;

use crate::ax::{
    Availability, AxProps, Completeness, Identity, Liveness, Role, Selection, Settable, TextLines,
    Unread, WalkBounds,
};
use crate::backend::{Delivery, SelectionReadback, ValueReadback};
use crate::control::Sent;
use crate::error::{Detail, Error, Refusal, Unverified};
use crate::geometry::ElementBounds;
use crate::types::{DeliveryMode, Focus, MenuPress, Pid, Window};

pub(super) use menus::{menu_items, menu_press};

/// How long an application gets to answer one request: libatspi gives 800
/// ms; a text edit in an office suite can take 2 s.
const REPLY_TIMEOUT: Duration = Duration::from_secs(5);
/// Most children one read of an element takes; the rest are counted.
const MAX_CHILDREN_READ: u32 = 4096;
/// Most actions read of one element: the count comes from the app.
const MAX_ACTIONS: i32 = 256;
/// Most characters of text a read returns.
const MAX_TEXT: i32 = 65_536;
/// Bounds on the searches below a window: focus, top-level owner.
const SEARCH_NODES: usize = 4096;
const SEARCH_DEPTH: usize = 64;
/// The path AT-SPI uses for "no object".
const NULL_PATH: &str = "/org/a11y/atspi/null";

/// An AT-SPI element: the unique bus name of its application and its object
/// path, equal for the same live element.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct AxHandle {
    bus: UniqueName<'static>,
    path: ObjectPath<'static>,
}

impl AxHandle {
    /// `None` for the null object and objects without a bus name.
    fn of(object: &ObjectRefOwned) -> Option<Self> {
        let bus = object.name()?;
        let path = object.path();
        (path.as_str() != NULL_PATH).then(|| Self {
            bus: bus.to_owned(),
            path: path.to_owned(),
        })
    }
}

/// Why a bus request failed, sorted at the edge.
enum BusFailure {
    /// The element or its application is gone.
    Gone,
    /// The application did not answer within [`REPLY_TIMEOUT`].
    Silent,
    Other(Detail),
}

impl From<zbus::Error> for BusFailure {
    fn from(error: zbus::Error) -> Self {
        const GONE: [&str; 4] = [
            "org.freedesktop.DBus.Error.UnknownObject",
            "org.freedesktop.DBus.Error.ServiceUnknown",
            "org.freedesktop.DBus.Error.NameHasNoOwner",
            "org.freedesktop.DBus.Error.UnknownMethod",
        ];
        match &error {
            zbus::Error::MethodError(name, ..) if GONE.contains(&name.as_str()) => Self::Gone,
            zbus::Error::FDO(fdo) => match **fdo {
                zbus::fdo::Error::UnknownObject(_)
                | zbus::fdo::Error::ServiceUnknown(_)
                | zbus::fdo::Error::NameHasNoOwner(_)
                | zbus::fdo::Error::UnknownMethod(_) => Self::Gone,
                _ => Self::Other(error.to_string().into()),
            },
            zbus::Error::InputOutput(io) if io.kind() == std::io::ErrorKind::TimedOut => {
                Self::Silent
            }
            _ => Self::Other(error.to_string().into()),
        }
    }
}

impl From<BusFailure> for Error {
    /// A failed read sent nothing.
    fn from(failure: BusFailure) -> Self {
        Self::Refused(match failure {
            BusFailure::Gone => Refusal::Vanished,
            BusFailure::Silent => Refusal::Ax {
                detail: "the application did not answer within 5 s".into(),
            },
            BusFailure::Other(detail) => Refusal::Ax { detail },
        })
    }
}

/// A failed action or write: a request the app never answered may have run.
fn after_request(failure: BusFailure) -> Error {
    match failure {
        BusFailure::Silent => Error::Unverified(Unverified::AxUnconfirmed {
            detail: "the application did not answer within 5 s; the request may still run".into(),
        }),
        BusFailure::Gone | BusFailure::Other(_) => failure.into(),
    }
}

fn read<T>(result: zbus::Result<T>) -> Result<T, Error> {
    result.map_err(|error| BusFailure::from(error).into())
}

fn refused(detail: impl Into<Detail>) -> Error {
    Error::Refused(Refusal::Ax {
        detail: detail.into(),
    })
}

/// The accessibility bus, or why it could not be reached.
pub(super) enum Bus {
    Connected(A11y),
    Missing(Detail),
}

impl Bus {
    /// Connects to the bus at `x_address` (the X root's `AT_SPI_BUS`) or
    /// the one the session bus names.
    pub(super) fn connect(x_address: Option<&str>) -> Self {
        match A11y::connect(x_address) {
            Ok(a11y) => Self::Connected(a11y),
            Err(failure) => Self::Missing(match failure {
                BusFailure::Gone | BusFailure::Silent => {
                    "the accessibility bus does not answer".into()
                }
                BusFailure::Other(detail) => detail,
            }),
        }
    }

    pub(super) fn a11y(&self) -> Result<&A11y, Error> {
        match self {
            Self::Connected(a11y) => Ok(a11y),
            Self::Missing(detail) => Err(refused(format!(
                "the AT-SPI accessibility bus is unavailable: {detail}"
            ))),
        }
    }
}

/// One element's top-level frame: its window title and process.
pub(super) struct Frame {
    pub(super) pid: Pid,
    pub(super) title: String,
}

/// Whether an element's toolkit reports which element holds its window's
/// keyboard, and whether this one does.
pub(super) enum KeyFocus {
    /// GTK 3 reports `Focused` only for its window's focus widget.
    Reported(Focus),
    /// Another toolkit, named or not.
    Unreported(String),
}

/// How text went into an element through its editable-text interface.
pub(super) enum TextRoute {
    Inserted,
    /// The element has no editable text.
    Absent,
    /// It has, but refused the insert.
    Declined,
}

pub(super) struct A11y {
    conn: Connection,
}

impl A11y {
    fn connect(x_address: Option<&str>) -> Result<Self, BusFailure> {
        let address = if let Some(address) = x_address {
            address.to_owned()
        } else {
            let session = Connection::session()?;
            BusProxyBlocking::new(&session)?.get_address()?
        };
        let conn = zbus::blocking::connection::Builder::address(address.as_str())?
            .method_timeout(REPLY_TIMEOUT)
            .build()?;
        Ok(Self { conn })
    }

    /// A proxy for `handle`'s element; it holds its own copy of the name and
    /// path (shared strings), so it outlives the borrow of `handle`.
    fn proxy<'a, P>(&'a self, handle: &AxHandle) -> zbus::Result<P>
    where
        P: zbus::proxy::Defaults + From<zbus::Proxy<'a>>,
    {
        zbus::blocking::proxy::Builder::<P>::new(&self.conn)
            .destination(BusName::from(handle.bus.clone()))?
            .path(handle.path.clone())?
            .cache_properties(CacheProperties::No)
            .build()
    }

    fn accessible(&self, handle: &AxHandle) -> Result<AccessibleProxyBlocking<'_>, Error> {
        read(self.proxy(handle))
    }

    /// The applications the AT-SPI registry lists. The registry is a
    /// service, not an element: its failures never read as a vanished one.
    fn applications(&self) -> Result<Vec<AxHandle>, Error> {
        let unanswered =
            |error: zbus::Error| refused(format!("the AT-SPI registry did not answer: {error}"));
        let registry =
            zbus::blocking::proxy::Builder::<AccessibleProxyBlocking<'_>>::new(&self.conn)
                .destination("org.a11y.atspi.Registry")
                .and_then(|builder| builder.path("/org/a11y/atspi/accessible/root"))
                .map(|builder| builder.cache_properties(CacheProperties::No))
                .and_then(zbus::blocking::proxy::Builder::build)
                .map_err(unanswered)?;
        Ok(registry
            .get_children()
            .map_err(unanswered)?
            .iter()
            .filter_map(AxHandle::of)
            .collect())
    }

    /// The process owning `bus`, which the bus daemon knows without asking
    /// the application.
    fn pid_of(&self, bus: &UniqueName<'_>) -> Result<Pid, Error> {
        let daemon = read(zbus::blocking::fdo::DBusProxy::new(&self.conn))?;
        daemon
            .get_connection_unix_process_id(BusName::from(bus.as_ref()))
            .map(Pid)
            .map_err(|error| BusFailure::from(zbus::Error::from(error)).into())
    }

    /// `app`'s top-level windows: frames, dialogs and windows, and file
    /// choosers and alerts hung straight off the application.
    fn frames(&self, app: &AxHandle) -> Result<Vec<AxHandle>, Error> {
        let children = read(self.accessible(app)?.get_children())?;
        Ok(children
            .iter()
            .filter_map(AxHandle::of)
            .filter(|child| {
                self.accessible(child)
                    .ok()
                    .and_then(|proxy| proxy.get_role().ok())
                    .is_some_and(|role| top_level(role, Parent::Application))
            })
            .collect())
    }

    /// The frame showing `window`: an application of the window's process
    /// with one frame of its title, or of its title and place.
    pub(super) fn window_root(&self, window: &Window) -> Result<AxHandle, Error> {
        let pid = window.pid.ok_or_else(|| {
            refused("the window names no process, so its accessibility tree is unknown")
        })?;
        let mut titled = Vec::new();
        for app in self.applications()? {
            if self.pid_of(&app.bus).ok() != Some(pid) {
                continue;
            }
            for frame in self.frames(&app)? {
                let name = self.accessible(&frame).and_then(|proxy| read(proxy.name()));
                if name.is_ok_and(|name| name == window.title) {
                    titled.push(frame);
                }
            }
        }
        if titled.len() > 1 {
            titled.retain(|frame| {
                self.extents(frame)
                    .is_ok_and(|bounds| same_place(bounds, window))
            });
        }
        let mut frames = titled.into_iter();
        match (frames.next(), frames.next()) {
            (Some(frame), None) => Ok(frame),
            (None, _) => Err(refused(format!(
                "the window's application exposes no accessibility frame titled {:?}; it may run without AT-SPI",
                window.title
            ))),
            (Some(_), Some(_)) => Err(refused(format!(
                "several accessibility frames match window {:?}; refusing an ambiguous tree",
                window.title
            ))),
        }
    }

    fn extents(&self, handle: &AxHandle) -> Result<ElementBounds, Error> {
        let component: ComponentProxyBlocking<'_> = read(self.proxy(handle))?;
        let (x, y, width, height) = read(component.get_extents(CoordType::Screen))?;
        Ok(ElementBounds {
            x: f64::from(x),
            y: f64::from(y),
            width: f64::from(width),
            height: f64::from(height),
        })
    }

    /// One element, and at most `children` of its children when asked.
    pub(super) fn read_node(
        &self,
        handle: &AxHandle,
        bounds: WalkBounds,
        children: Option<u32>,
    ) -> Result<(AxProps, Vec<AxHandle>), Error> {
        let proxy = self.accessible(handle)?;
        let native_role = proxy.get_role_name().map_err(BusFailure::from);
        if let Err(BusFailure::Gone) = native_role {
            return Err(Error::Refused(Refusal::Vanished));
        }
        let state = proxy.get_state().ok();
        if state.is_some_and(|states| states.contains(State::Defunct)) {
            return Err(Error::Refused(Refusal::Vanished));
        }
        let title = proxy.name().ok();
        let description = proxy.description().ok();
        let interfaces = proxy.get_interfaces().ok();
        let count = proxy
            .child_count()
            .ok()
            .map(|count| u32::try_from(count).unwrap_or(0));
        // An element whose interfaces cannot be read is asked on each.
        let has = |interface| interfaces.is_none_or(|set: InterfaceSet| set.contains(interface));
        let value = if has(Interface::Text) {
            self.text(handle).ok()
        } else {
            None
        };
        let value = match value {
            None if interfaces.is_some_and(|set| set.contains(Interface::Value)) => {
                self.number(handle).ok().map(|number| number.to_string())
            }
            text => text,
        };
        let bounds = match bounds {
            WalkBounds::Read if has(Interface::Component) => self
                .extents(handle)
                .ok()
                .filter(|bounds| bounds.width > 0.0 && bounds.height > 0.0),
            WalkBounds::Read | WalkBounds::Skip => None,
        };
        let actions = if has(Interface::Action) {
            self.action_names(handle).unwrap_or_default()
        } else {
            Vec::new()
        };
        let (child_handles, read_children) = match children {
            Some(limit) => match children_of(&proxy, count, limit) {
                Ok(read) => (read, Completeness::Whole),
                Err(_) => (Vec::new(), Completeness::Partial),
            },
            None => (Vec::new(), Completeness::Whole),
        };
        let unread_children = match count {
            Some(count) => Unread::Count(
                count.saturating_sub(u32::try_from(child_handles.len()).unwrap_or(u32::MAX)),
            ),
            None => Unread::Unknown,
        };
        let props = props(Read {
            native_role: native_role.ok(),
            title,
            description,
            value,
            state,
            bounds,
            actions,
            child_count: count,
            children: read_children,
            unread_children,
        });
        Ok((props, child_handles))
    }

    fn action_names(&self, handle: &AxHandle) -> Result<Vec<String>, Error> {
        let action: ActionProxyBlocking<'_> = read(self.proxy(handle))?;
        let count = read(action.n_actions())?.clamp(0, MAX_ACTIONS);
        (0..count)
            .map(|index| read(action.get_name(index)))
            .collect()
    }

    /// The element's text, at most [`MAX_TEXT`] characters.
    pub(super) fn text(&self, handle: &AxHandle) -> Result<String, Error> {
        let text: TextProxyBlocking<'_> = read(self.proxy(handle))?;
        let count = read(text.character_count())?.clamp(0, MAX_TEXT);
        read(text.get_text(0, count))
    }

    fn number(&self, handle: &AxHandle) -> Result<f64, Error> {
        let value: ValueProxyBlocking<'_> = read(self.proxy(handle))?;
        read(value.current_value())
    }

    pub(super) fn liveness(&self, handle: &AxHandle) -> Liveness {
        let state = self.accessible(handle).and_then(|proxy| {
            proxy
                .get_state()
                .map_err(|error| BusFailure::from(error).into())
        });
        match state {
            Ok(states) if states.contains(State::Defunct) => Liveness::Gone,
            Err(Error::Refused(Refusal::Vanished)) => Liveness::Gone,
            Ok(_) | Err(_) => Liveness::Alive,
        }
    }

    /// The element holding keyboard focus at or below `root`.
    pub(super) fn focused_within(&self, root: &AxHandle) -> Option<AxHandle> {
        let mut pending = vec![(root.clone(), 0usize)];
        let mut visited = 0usize;
        while let Some((handle, depth)) = pending.pop() {
            visited += 1;
            if visited > SEARCH_NODES {
                return None;
            }
            let proxy = self.accessible(&handle).ok()?;
            if proxy
                .get_state()
                .is_ok_and(|states| states.contains(State::Focused))
            {
                return Some(handle);
            }
            if depth < SEARCH_DEPTH {
                let children = proxy.get_children().unwrap_or_default();
                pending.extend(
                    children
                        .iter()
                        .rev()
                        .filter_map(AxHandle::of)
                        .map(|child| (child, depth + 1)),
                );
            }
        }
        None
    }

    pub(super) fn value_settable(&self, handle: &AxHandle) -> Settable {
        let Ok(proxy) = self.accessible(handle) else {
            return Settable::Unknown;
        };
        match (proxy.get_interfaces(), proxy.get_state()) {
            (Ok(interfaces), Ok(states)) => {
                if interfaces.contains(Interface::EditableText) && states.contains(State::Editable)
                    || interfaces.contains(Interface::Value)
                {
                    Settable::Yes
                } else {
                    Settable::No
                }
            }
            (Err(_), _) | (_, Err(_)) => Settable::Unknown,
        }
    }

    /// Runs the element's activation: a press refuses, in the background, a
    /// control whose press opens a menu.
    pub(super) fn press(&self, handle: &AxHandle, delivery: &Delivery<'_>) -> Result<(), Error> {
        let proxy = self.accessible(handle)?;
        let role = read(proxy.get_role())?;
        let states = read(proxy.get_state())?;
        if states.contains(State::Defunct) {
            return Err(Error::Refused(Refusal::Vanished));
        }
        if opens_menu(role, states)
            && delivery.mode == DeliveryMode::Background
            && delivery.menus == MenuPress::Refuse
        {
            return Err(Error::Refused(Refusal::BackgroundUnavailable {
                detail: "pressing it opens a menu, which takes the user's keyboard".into(),
            }));
        }
        let names = self.action_names(handle)?;
        let index = activation(&names, toggles(role))
            .ok_or_else(|| refused("the element offers no activation action"))?;
        self.do_action(handle, index, delivery)
    }

    fn do_action(
        &self,
        handle: &AxHandle,
        index: i32,
        delivery: &Delivery<'_>,
    ) -> Result<(), Error> {
        let action: ActionProxyBlocking<'_> = read(self.proxy(handle))?;
        delivery.before_press(Sent::Nothing)?;
        match action.do_action(index) {
            Ok(true) => Ok(()),
            Ok(false) => Err(refused("the application refused the action")),
            Err(error) => Err(after_request(error.into())),
        }
    }

    /// Writes `value` as the element's text, or as its number, and reads it
    /// back.
    pub(super) fn set_value(
        &self,
        handle: &AxHandle,
        value: &str,
        delivery: &Delivery<'_>,
    ) -> Result<ValueReadback, Error> {
        let proxy = self.accessible(handle)?;
        let interfaces = read(proxy.get_interfaces())?;
        if interfaces.contains(Interface::EditableText) {
            let field = match proxy.get_role() {
                Ok(atspi::Role::PasswordText) | Err(_) => crate::ax::FieldKind::Secure,
                Ok(_) => crate::ax::FieldKind::Plain,
            };
            let editable: EditableTextProxyBlocking<'_> = read(self.proxy(handle))?;
            delivery.before_press(Sent::Nothing)?;
            return match editable.set_text_contents(value) {
                Ok(true) => Ok(ValueReadback {
                    actual: self.text(handle).ok(),
                    field,
                }),
                Ok(false) => Err(refused("the application refused the text")),
                Err(error) => Err(after_request(error.into())),
            };
        }
        if interfaces.contains(Interface::Value) {
            let number: f64 = value
                .trim()
                .parse()
                .map_err(|_| refused("the element holds a number, and the value is not one"))?;
            let control: ValueProxyBlocking<'_> = read(self.proxy(handle))?;
            delivery.before_press(Sent::Nothing)?;
            control
                .set_current_value(number)
                .map_err(|error| after_request(error.into()))?;
            let actual = control.current_value().ok().map(|actual| {
                // A toolkit storing `float` reads 0.3 back as 0.30000001192092896.
                if (actual - number).abs() <= number.abs().max(1.0) * f64::from(f32::EPSILON) {
                    value.to_owned()
                } else {
                    actual.to_string()
                }
            });
            return Ok(ValueReadback {
                actual,
                field: crate::ax::FieldKind::Plain,
            });
        }
        Err(refused("the element has no editable text or value"))
    }

    /// Inserts `text` at the element's caret through its editable-text
    /// interface: no keys, no focus.
    pub(super) fn insert_text(
        &self,
        handle: &AxHandle,
        text: &str,
        delivery: &Delivery<'_>,
    ) -> Result<TextRoute, Error> {
        let interfaces = read(self.accessible(handle)?.get_interfaces())?;
        if !interfaces.contains(Interface::EditableText) {
            return Ok(TextRoute::Absent);
        }
        let caret: TextProxyBlocking<'_> = read(self.proxy(handle))?;
        let at = read(caret.caret_offset())?.max(0);
        let length = i32::try_from(text.chars().count())
            .map_err(|_| refused("the text is too long for one insert"))?;
        let editable: EditableTextProxyBlocking<'_> = read(self.proxy(handle))?;
        delivery.before_press(Sent::Nothing)?;
        match editable.insert_text(at, text, length) {
            Ok(true) => Ok(TextRoute::Inserted),
            Ok(false) => Ok(TextRoute::Declined),
            Err(error) => Err(after_request(error.into())),
        }
    }

    /// Moves keyboard focus to the element; may raise its window.
    pub(super) fn grab_focus(&self, handle: &AxHandle) -> Result<(), Error> {
        let component: ComponentProxyBlocking<'_> = read(self.proxy(handle))?;
        match component.grab_focus() {
            Ok(true) => Ok(()),
            Ok(false) => Err(refused("the element refused keyboard focus")),
            Err(error) => Err(after_request(error.into())),
        }
    }

    pub(super) fn key_focus(&self, handle: &AxHandle) -> Result<KeyFocus, Error> {
        let proxy = self.accessible(handle)?;
        let states = read(proxy.get_state())?;
        let app = read(proxy.get_application())?;
        let app = AxHandle::of(&app).ok_or_else(|| refused("the element names no application"))?;
        let application: ApplicationProxyBlocking<'_> = read(self.proxy(&app))?;
        let toolkit = application.toolkit_name().unwrap_or_default();
        let version = application.version().unwrap_or_default();
        if toolkit.eq_ignore_ascii_case("gtk") && version.starts_with("3.") {
            Ok(KeyFocus::Reported(if states.contains(State::Focused) {
                Focus::Focused
            } else {
                Focus::Unfocused
            }))
        } else {
            Ok(KeyFocus::Unreported(toolkit))
        }
    }

    /// The top-level frame holding `handle`, followed by parent links, and
    /// its process.
    pub(super) fn frame_of(&self, handle: &AxHandle) -> Result<Frame, Error> {
        let mut current = handle.clone();
        for _ in 0..SEARCH_DEPTH {
            let proxy = self.accessible(&current)?;
            let role = read(proxy.get_role())?;
            let parent = AxHandle::of(&read(proxy.parent())?);
            let parent_role = match &parent {
                Some(parent) => read(self.accessible(parent)?.get_role())?,
                None => atspi::Role::Invalid,
            };
            let at_top = top_level(role, Parent::Other)
                || top_level(role, Parent::Application) && parent_role == atspi::Role::Application;
            if at_top {
                return Ok(Frame {
                    pid: self.pid_of(&current.bus)?,
                    title: read(proxy.name())?,
                });
            }
            match parent {
                Some(parent) if parent != current => current = parent,
                Some(_) | None => break,
            }
        }
        Err(refused("the element has no top-level window"))
    }

    pub(super) fn select(
        &self,
        handle: &AxHandle,
        range: crate::text_range::Utf16Range,
        delivery: &Delivery<'_>,
    ) -> Result<SelectionReadback, Error> {
        let value = self.text(handle)?;
        let (start, end) = text::char_span(&value, range)
            .ok_or_else(|| refused("the range runs past the element's text"))?;
        let text: TextProxyBlocking<'_> = read(self.proxy(handle))?;
        let selections = read(text.get_n_selections())?;
        delivery.before_press(Sent::Nothing)?;
        let applied = if start == end {
            text.set_caret_offset(start)
        } else if selections > 0 {
            text.set_selection(0, start, end)
        } else {
            text.add_selection(start, end)
        };
        match applied {
            Ok(true) => {}
            Ok(false) => return Err(refused("the application refused the selection")),
            Err(error) => return Err(after_request(error.into())),
        }
        let unconfirmed = |detail: &'static str| {
            Error::Unverified(Unverified::AxUnconfirmed {
                detail: detail.into(),
            })
        };
        let value = self.text(handle).map_err(|_| {
            unconfirmed("the selection was set, but the text could not be read back")
        })?;
        let (start, end) = match text.get_n_selections() {
            Ok(count) if count > 0 => text
                .get_selection(0)
                .map_err(|_| unconfirmed("the selection was set, but could not be read back"))?,
            Ok(_) | Err(_) => {
                let caret = text
                    .caret_offset()
                    .map_err(|_| unconfirmed("the caret was set, but could not be read back"))?;
                (caret, caret)
            }
        };
        let range = text::utf16_span(&value, start, end)
            .ok_or_else(|| unconfirmed("the selection read back runs past the element's text"))?;
        let focus = match self
            .accessible(handle)
            .and_then(|proxy| read(proxy.get_state()))
        {
            Ok(states) if states.contains(State::Focused) => Focus::Focused,
            Ok(_) | Err(_) => Focus::Unfocused,
        };
        Ok(SelectionReadback {
            range,
            value,
            focus,
        })
    }
}

/// Whether a frame's bounds match the native window's.
fn same_place(bounds: ElementBounds, window: &Window) -> bool {
    let near = |a: f64, b: i32| (a - f64::from(b)).abs() < 1.0;
    near(bounds.x, window.bounds.x) && near(bounds.y, window.bounds.y)
}

/// What a top-level role check knows about the element's parent.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Parent {
    Application,
    Other,
}

/// Frames, dialogs and windows anywhere; file choosers and alerts only as a
/// child of the application.
fn top_level(role: atspi::Role, parent: Parent) -> bool {
    match role {
        atspi::Role::Frame | atspi::Role::Dialog | atspi::Role::Window => true,
        atspi::Role::FileChooser | atspi::Role::Alert => parent == Parent::Application,
        _ => false,
    }
}

/// A combo box, a GTK menu item holding a submenu, or a control that says
/// it has a popup.
fn opens_menu(role: atspi::Role, states: StateSet) -> bool {
    matches!(role, atspi::Role::ComboBox | atspi::Role::Menu) || states.contains(State::HasPopup)
}

/// Whether a press of the role may fall back on `check`/`uncheck`, the only
/// activation Chromium gives toggles.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Toggle {
    Yes,
    No,
}

fn toggles(role: atspi::Role) -> Toggle {
    match role {
        atspi::Role::CheckBox
        | atspi::Role::CheckMenuItem
        | atspi::Role::RadioButton
        | atspi::Role::RadioMenuItem
        | atspi::Role::ToggleButton => Toggle::Yes,
        _ => Toggle::No,
    }
}

/// Machine names that activate an element: GTK (`click`, `activate`), Qt
/// (`Toggle`), Chromium (`click`, `open`, `jump`, `doDefault`), ATK bridges.
const ACTIVATIONS: [&str; 9] = [
    "press",
    "click",
    "clickancestor",
    "activate",
    "invoke",
    "toggle",
    "open",
    "jump",
    "dodefault",
];

/// Whether `name` is `safe`, ignoring case and the spaces, hyphens and
/// underscores toolkits spell action names with.
fn folds_to(name: &str, safe: &str) -> bool {
    name.bytes()
        .filter(|byte| !matches!(byte, b' ' | b'-' | b'_'))
        .map(|byte| byte.to_ascii_lowercase())
        .eq(safe.bytes())
}

/// The action a press runs: an activation, else `select` (a GTK colour
/// swatch lists `select` before `activate`), else a toggle's check.
fn activation<S: AsRef<str>>(names: &[S], toggle: Toggle) -> Option<i32> {
    let position = |safe: &[&str]| {
        names
            .iter()
            .position(|name| safe.iter().any(|safe| folds_to(name.as_ref(), safe)))
    };
    let index = position(&ACTIVATIONS)
        .or_else(|| position(&["select"]))
        .or_else(|| match toggle {
            Toggle::Yes => position(&["check", "uncheck"]),
            Toggle::No => None,
        })?;
    i32::try_from(index).ok()
}

/// At most `limit` children: all at once when they fit, else one by one.
fn children_of(
    proxy: &AccessibleProxyBlocking<'_>,
    count: Option<u32>,
    limit: u32,
) -> Result<Vec<AxHandle>, Error> {
    let limit = limit.min(MAX_CHILDREN_READ);
    match count {
        Some(count) if count > limit => (0..limit)
            .filter_map(|index| i32::try_from(index).ok())
            .map(|index| read(proxy.get_child_at_index(index)))
            .filter_map(|child| child.map(|child| AxHandle::of(&child)).transpose())
            .collect(),
        Some(_) | None => Ok(read(proxy.get_children())?
            .iter()
            .filter_map(AxHandle::of)
            .collect()),
    }
}

/// What one read of an element answered; `None` where a request failed.
struct Read {
    native_role: Option<String>,
    title: Option<String>,
    description: Option<String>,
    value: Option<String>,
    state: Option<StateSet>,
    bounds: Option<ElementBounds>,
    actions: Vec<String>,
    child_count: Option<u32>,
    children: Completeness,
    unread_children: Unread,
}

fn props(read: Read) -> AxProps {
    let lines = match read.state {
        Some(states) if states.contains(State::MultiLine) => TextLines::Multi,
        Some(_) | None => TextLines::Single,
    };
    let label_read = match (&read.native_role, &read.title, &read.description) {
        (Some(_), Some(_), Some(_)) => Completeness::Whole,
        _ => Completeness::Partial,
    };
    let identity = match (
        &read.native_role,
        &read.title,
        &read.description,
        read.state,
    ) {
        (Some(role), Some(title), Some(description), Some(_)) => {
            let mut hasher = DefaultHasher::new();
            (role, title, description, &read.value).hash(&mut hasher);
            Some(Identity(hasher.finish()))
        }
        _ => None,
    };
    let fields = match (identity, read.children) {
        (Some(_), Completeness::Whole) => Completeness::Whole,
        _ => Completeness::Partial,
    };
    let native_role = read.native_role.unwrap_or_else(|| "unknown".to_owned());
    let has = |state| read.state.is_some_and(|states| states.contains(state));
    AxProps {
        role: Role::from_atspi(&native_role, lines),
        native_role,
        title: read.title.filter(|title| !title.is_empty()),
        value: read.value,
        description: read.description.filter(|text| !text.is_empty()),
        role_name: None,
        // GTK4 marks an enabled control only `Sensitive`; toolkits drop both
        // from a greyed-out one.
        availability: if has(State::Enabled) || has(State::Sensitive) {
            Availability::Enabled
        } else {
            Availability::Disabled
        },
        focus: if has(State::Focused) {
            Focus::Focused
        } else {
            Focus::Unfocused
        },
        selection: if has(State::Selected) {
            Selection::Selected
        } else {
            Selection::Unselected
        },
        bounds: read.bounds,
        actions: read.actions,
        child_count: read.child_count.unwrap_or(0),
        identity,
        fields,
        label_read,
        unread_children: read.unread_children,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_press_takes_an_activation_never_an_unrelated_action() {
        let names = ["buffer.delete-line", "Do Default"];
        assert_eq!(activation(&names, Toggle::No), Some(1));
        let swatch = ["select", "activate"];
        assert_eq!(activation(&swatch, Toggle::No), Some(1));
        assert_eq!(activation(&["select"], Toggle::No), Some(0));
        assert_eq!(activation(&["check"], Toggle::No), None);
        assert_eq!(activation(&["check"], Toggle::Yes), Some(0));
        assert_eq!(activation(&["click_ancestor"], Toggle::No), Some(0));
    }

    #[test]
    fn an_element_with_unread_labels_gets_no_identity() {
        let read = |title: Option<&str>| Read {
            native_role: Some("push button".to_owned()),
            title: title.map(str::to_owned),
            description: Some(String::new()),
            value: None,
            state: Some(StateSet::new(State::Enabled)),
            bounds: None,
            actions: Vec::new(),
            child_count: Some(0),
            children: Completeness::Whole,
            unread_children: Unread::Count(0),
        };
        let whole = props(read(Some("OK")));
        assert_eq!(whole.role, Role::Button);
        assert_eq!(whole.label(), Some("OK"));
        assert!(whole.identity.is_some());
        assert_eq!(whole.fields, Completeness::Whole);
        assert_eq!(whole.availability, Availability::Enabled);
        let partial = props(read(None));
        assert_eq!(partial.identity, None);
        assert_eq!(partial.label_read, Completeness::Partial);
        assert_eq!(partial.fields, Completeness::Partial);
    }
}
