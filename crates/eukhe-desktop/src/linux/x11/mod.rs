//! X11: the connection, the window list, window properties, focus and
//! activation (port of omp `crates/natives/src/desktop/linux/x11/mod.rs`,
//! `x11/capture.rs` window listing and `x11/wm.rs`).

mod capture;
mod input;
mod keymap;
mod monitor;
mod roster;

use std::path::Path;
use std::time::{Duration, Instant};

use x11rb::connection::Connection;
use x11rb::errors::{ConnectError, ConnectionError, ReplyError, ReplyOrIdError};
use x11rb::protocol::xproto::{
    self, AtomEnum, ClientMessageEvent, ConfigureWindowAux, ConnectionExt as _, EventMask,
    InputFocus, MapState, StackMode, WindowClass,
};
use x11rb::rust_connection::RustConnection;
use x11rb::CURRENT_TIME;

use crate::control::Token;
use crate::error::{Error, Refusal, Unverified, WindowError};
use crate::geometry::GlobalRect;
use crate::types::{Focus, Pid, Support, Window, WindowId};

use input::Pair;
pub(crate) use monitor::{EscapeMonitor, UserInputMonitor};
pub(crate) use roster::window_roster;

x11rb::atom_manager! {
    pub(super) Atoms: AtomsCookie {
        _NET_CLIENT_LIST_STACKING,
        _NET_ACTIVE_WINDOW,
        _NET_SUPPORTING_WM_CHECK,
        _NET_WM_NAME,
        _NET_WM_PID,
        _NET_WM_WINDOW_TYPE,
        _NET_WM_WINDOW_TYPE_DESKTOP,
        _NET_WM_WINDOW_TYPE_DOCK,
        _NET_WM_WINDOW_TYPE_TOOLBAR,
        _NET_WM_WINDOW_TYPE_MENU,
        _NET_WM_WINDOW_TYPE_UTILITY,
        _NET_WM_WINDOW_TYPE_SPLASH,
        _NET_WM_WINDOW_TYPE_DIALOG,
        _NET_WM_WINDOW_TYPE_DROPDOWN_MENU,
        _NET_WM_WINDOW_TYPE_POPUP_MENU,
        _NET_WM_WINDOW_TYPE_TOOLTIP,
        _NET_WM_WINDOW_TYPE_NOTIFICATION,
        _NET_WM_WINDOW_TYPE_COMBO,
        _NET_WM_WINDOW_TYPE_DND,
        _NET_WM_WINDOW_OPACITY,
        _GTK_FRAME_EXTENTS,
        WM_STATE,
        UTF8_STRING,
        AT_SPI_BUS,
        XTEST_DEVICE: b"XTEST Device",
    }
}

/// Bound on ancestor and descendant walks.
const TREE_WALK_LIMIT: usize = 32;
/// How long a takeover gives the window manager to focus its target.
const ACTIVATION_BUDGET: Duration = Duration::from_millis(1500);
const FOCUS_POLL: Duration = Duration::from_millis(25);

/// An X window id.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct XWindow(pub(super) xproto::Window);

impl XWindow {
    /// The X window a session window id names; ids are decimal.
    pub(super) fn of(id: &WindowId) -> Result<Self, WindowError> {
        id.as_str()
            .parse()
            .map(Self)
            .map_err(|_| WindowError::NotFound(id.clone()))
    }

    fn id(self) -> WindowId {
        WindowId::new(&self.0.to_string())
    }
}

/// Why an X request failed.
#[derive(Debug, thiserror::Error)]
pub(super) enum XError {
    #[error("cannot connect to the X server: {0}")]
    Connect(#[from] ConnectError),
    #[error("the X connection failed: {0}")]
    Connection(#[from] ConnectionError),
    #[error("an X request failed: {0}")]
    Reply(#[from] ReplyError),
    #[error("an X request failed: {0}")]
    ReplyOrId(#[from] ReplyOrIdError),
    #[error("the X server names no screen for this display")]
    NoScreen,
    #[error("the X server did not create the virtual input device pair")]
    NoPair,
}

impl From<XError> for Error {
    /// A failed query sent nothing.
    fn from(error: XError) -> Self {
        Self::Refused(Refusal::Platform {
            detail: error.to_string().into(),
        })
    }
}

/// A failure once input went out: some of it may have landed.
pub(super) fn landed(error: &XError) -> Error {
    Error::Unverified(Unverified::InputFailed {
        detail: error.to_string().into(),
    })
}

/// A failure before input went out.
pub(super) fn refused(error: &XError) -> Error {
    Error::Refused(Refusal::Platform {
        detail: error.to_string().into(),
    })
}

/// The extensions this server offers that the backend uses.
#[derive(Clone, Copy)]
pub(super) struct Extensions {
    pub(super) xtest: Support,
    pub(super) xinput: Support,
    pub(super) composite: Support,
}

/// What `_NET_WM_WINDOW_TYPE` says a window is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    Normal,
    Dialog,
    Utility,
    Toolbar,
    Splash,
    Menu,
    Tooltip,
    Notification,
    Dock,
    Desktop,
    DragIcon,
}

impl Kind {
    /// Windows a user works in: the window list keeps these.
    fn listed(self) -> bool {
        match self {
            Self::Normal | Self::Dialog | Self::Utility | Self::Toolbar | Self::Splash => true,
            Self::Menu
            | Self::Tooltip
            | Self::Notification
            | Self::Dock
            | Self::Desktop
            | Self::DragIcon => false,
        }
    }
}

/// A top-level window: the root's child and the client window inside it
/// (the same window without a reparenting window manager).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TopLevel {
    frame: XWindow,
    client: XWindow,
}

pub(super) struct X11 {
    conn: RustConnection,
    root: xproto::Window,
    atoms: Atoms,
    extensions: Extensions,
    pair: Pair,
}

impl X11 {
    pub(super) fn open() -> Result<Self, XError> {
        let (conn, screen) = RustConnection::connect(None)?;
        let root = conn
            .setup()
            .roots
            .get(screen)
            .map(|screen| screen.root)
            .ok_or(XError::NoScreen)?;
        let atoms = Atoms::new(&conn)?.reply()?;
        let extensions = Extensions {
            xtest: present(&conn, x11rb::protocol::xtest::X11_EXTENSION_NAME)?,
            xinput: match present(&conn, x11rb::protocol::xinput::X11_EXTENSION_NAME)? {
                Support::Supported => input::xi2(&conn)?,
                Support::Unsupported => Support::Unsupported,
            },
            composite: match present(&conn, x11rb::protocol::composite::X11_EXTENSION_NAME)? {
                Support::Supported => capture::composite(&conn)?,
                Support::Unsupported => Support::Unsupported,
            },
        };
        Ok(Self {
            conn,
            root,
            atoms,
            extensions,
            pair: Pair::Unprobed,
        })
    }

    pub(super) fn extensions(&self) -> Extensions {
        self.extensions
    }

    /// The accessibility bus address the X root publishes (`AT_SPI_BUS`).
    pub(super) fn atspi_address(&self) -> Option<String> {
        let reply = self
            .property(
                self.root,
                self.atoms.AT_SPI_BUS,
                AtomEnum::STRING.into(),
                1024,
            )
            .ok()??;
        String::from_utf8(reply.value)
            .ok()
            .filter(|address| !address.is_empty())
    }

    fn property(
        &self,
        window: xproto::Window,
        property: xproto::Atom,
        type_: xproto::Atom,
        longs: u32,
    ) -> Result<Option<xproto::GetPropertyReply>, XError> {
        let reply = self
            .conn
            .get_property(false, window, property, type_, 0, longs)?
            .reply()?;
        Ok((reply.type_ != x11rb::NONE).then_some(reply))
    }

    fn cardinals(
        &self,
        window: xproto::Window,
        property: xproto::Atom,
        count: u32,
    ) -> Option<Vec<u32>> {
        let reply = self
            .property(window, property, AtomEnum::CARDINAL.into(), count)
            .ok()??;
        let values = reply.value32()?.collect();
        Some(values)
    }

    fn cardinal(&self, window: xproto::Window, property: xproto::Atom) -> Option<u32> {
        self.cardinals(window, property, 1)?.first().copied()
    }

    fn window_property(
        &self,
        window: xproto::Window,
        property: xproto::Atom,
    ) -> Option<xproto::Window> {
        let reply = self
            .property(window, property, AtomEnum::WINDOW.into(), 1)
            .ok()??;
        let first = reply.value32()?.next();
        first.filter(|id| *id != x11rb::NONE)
    }

    fn has(&self, window: xproto::Window, property: xproto::Atom) -> bool {
        self.property(window, property, AtomEnum::ANY.into(), 0)
            .is_ok_and(|reply| reply.is_some())
    }

    /// Whether an EWMH window manager runs.
    fn managed(&self) -> bool {
        self.window_property(self.root, self.atoms._NET_SUPPORTING_WM_CHECK)
            .is_some()
    }

    fn pid(&self, window: XWindow) -> Option<Pid> {
        self.cardinal(window.0, self.atoms._NET_WM_PID).map(Pid)
    }

    fn title(&self, window: XWindow) -> String {
        let utf8 = self
            .property(
                window.0,
                self.atoms._NET_WM_NAME,
                self.atoms.UTF8_STRING,
                1024,
            )
            .ok()
            .flatten();
        if let Some(reply) = utf8 {
            return String::from_utf8_lossy(&reply.value).into_owned();
        }
        match self.property(
            window.0,
            AtomEnum::WM_NAME.into(),
            AtomEnum::ANY.into(),
            1024,
        ) {
            // `STRING` is Latin-1.
            Ok(Some(reply)) if reply.type_ == u32::from(AtomEnum::STRING) => {
                reply.value.iter().map(|byte| char::from(*byte)).collect()
            }
            Ok(Some(reply)) => String::from_utf8_lossy(&reply.value).into_owned(),
            Ok(None) | Err(_) => String::new(),
        }
    }

    /// The application name: the `WM_CLASS` class, else the process name.
    fn app(&self, window: XWindow, pid: Option<Pid>) -> String {
        let class = self
            .property(
                window.0,
                AtomEnum::WM_CLASS.into(),
                AtomEnum::STRING.into(),
                256,
            )
            .ok()
            .flatten()
            .and_then(|reply| wm_class(&reply.value).map(str::to_owned));
        class
            .or_else(|| {
                pid.and_then(|pid| std::fs::read_to_string(format!("/proc/{}/comm", pid.0)).ok())
            })
            .map(|name| name.trim().to_owned())
            .unwrap_or_default()
    }

    fn kind(&self, window: XWindow) -> Kind {
        let atoms = &self.atoms;
        let Some(types) = self
            .property(
                window.0,
                atoms._NET_WM_WINDOW_TYPE,
                AtomEnum::ATOM.into(),
                16,
            )
            .ok()
            .flatten()
        else {
            return Kind::Normal;
        };
        let table = [
            (atoms._NET_WM_WINDOW_TYPE_DESKTOP, Kind::Desktop),
            (atoms._NET_WM_WINDOW_TYPE_DOCK, Kind::Dock),
            (atoms._NET_WM_WINDOW_TYPE_TOOLBAR, Kind::Toolbar),
            (atoms._NET_WM_WINDOW_TYPE_MENU, Kind::Menu),
            (atoms._NET_WM_WINDOW_TYPE_UTILITY, Kind::Utility),
            (atoms._NET_WM_WINDOW_TYPE_SPLASH, Kind::Splash),
            (atoms._NET_WM_WINDOW_TYPE_DIALOG, Kind::Dialog),
            (atoms._NET_WM_WINDOW_TYPE_DROPDOWN_MENU, Kind::Menu),
            (atoms._NET_WM_WINDOW_TYPE_POPUP_MENU, Kind::Menu),
            (atoms._NET_WM_WINDOW_TYPE_TOOLTIP, Kind::Tooltip),
            (atoms._NET_WM_WINDOW_TYPE_NOTIFICATION, Kind::Notification),
            (atoms._NET_WM_WINDOW_TYPE_COMBO, Kind::Menu),
            (atoms._NET_WM_WINDOW_TYPE_DND, Kind::DragIcon),
        ];
        // The first type the window lists that this backend knows wins.
        let kind = types
            .value32()
            .into_iter()
            .flatten()
            .find_map(|atom| {
                table
                    .iter()
                    .find(|(known, _)| *known == atom)
                    .map(|(_, kind)| *kind)
            })
            .unwrap_or(Kind::Normal);
        kind
    }

    /// Where a client window's content sits on the root, shadow excluded.
    pub(super) fn placed(&self, window: XWindow) -> Result<GlobalRect, XError> {
        let geometry = self.conn.get_geometry(window.0)?.reply()?;
        let origin = self
            .conn
            .translate_coordinates(window.0, self.root, 0, 0)?
            .reply()?;
        let [left, right, top, bottom] = self
            .cardinals(window.0, self.atoms._GTK_FRAME_EXTENTS, 4)
            .and_then(|extents| <[u32; 4]>::try_from(extents).ok())
            .filter(|[left, right, top, bottom]| {
                left + right < u32::from(geometry.width)
                    && top + bottom < u32::from(geometry.height)
            })
            .unwrap_or([0; 4]);
        Ok(GlobalRect {
            x: i32::from(origin.dst_x) + i32::try_from(left).unwrap_or(0),
            y: i32::from(origin.dst_y) + i32::try_from(top).unwrap_or(0),
            width: u32::from(geometry.width) - left - right,
            height: u32::from(geometry.height) - top - bottom,
        })
    }

    /// The client inside a root child: the window itself when it has
    /// `WM_STATE` or no child does.
    fn client_of(&self, frame: XWindow) -> XWindow {
        if self.has(frame.0, self.atoms.WM_STATE) {
            return frame;
        }
        let mut pending = vec![(frame.0, 0usize)];
        while let Some((window, depth)) = pending.pop() {
            let Ok(tree) = self
                .conn
                .query_tree(window)
                .map_err(XError::from)
                .and_then(|cookie| Ok(cookie.reply()?))
            else {
                continue;
            };
            for child in tree.children {
                if self.has(child, self.atoms.WM_STATE) {
                    return XWindow(child);
                }
                if depth < 2 {
                    pending.push((child, depth + 1));
                }
            }
        }
        frame
    }

    /// The root child holding `window`.
    fn frame_of(&self, window: XWindow) -> XWindow {
        let mut current = window.0;
        for _ in 0..TREE_WALK_LIMIT {
            let Some(parent) = self.parent(current) else {
                break;
            };
            if parent == self.root {
                return XWindow(current);
            }
            current = parent;
        }
        window
    }

    fn parent(&self, window: xproto::Window) -> Option<xproto::Window> {
        let tree = self.conn.query_tree(window).ok()?.reply().ok()?;
        (tree.parent != x11rb::NONE).then_some(tree.parent)
    }

    /// Whether `inner` is `outer` or inside it.
    pub(super) fn is_within(&self, inner: xproto::Window, outer: XWindow) -> bool {
        let mut current = inner;
        for _ in 0..TREE_WALK_LIMIT {
            if current == outer.0 {
                return true;
            }
            match self.parent(current) {
                Some(parent) if parent != self.root => current = parent,
                Some(_) | None => return false,
            }
        }
        false
    }

    /// Top-level windows, front to back.
    fn toplevels(&self) -> Result<Vec<TopLevel>, XError> {
        let stacking = self
            .property(
                self.root,
                self.atoms._NET_CLIENT_LIST_STACKING,
                AtomEnum::WINDOW.into(),
                4096,
            )?
            .and_then(|reply| reply.value32().map(Iterator::collect::<Vec<_>>));
        if let Some(clients) = stacking.filter(|clients| !clients.is_empty()) {
            return Ok(clients
                .into_iter()
                .rev()
                .map(|client| TopLevel {
                    frame: self.frame_of(XWindow(client)),
                    client: XWindow(client),
                })
                .collect());
        }
        let tree = self.conn.query_tree(self.root)?.reply()?;
        Ok(tree
            .children
            .into_iter()
            .rev()
            .map(|frame| TopLevel {
                frame: XWindow(frame),
                client: self.client_of(XWindow(frame)),
            })
            .collect())
    }

    /// The window holding the user's focus: the window manager's active
    /// window, else the core focus.
    fn focused(&self) -> Option<xproto::Window> {
        if self.managed() {
            if let Some(active) = self.window_property(self.root, self.atoms._NET_ACTIVE_WINDOW) {
                return Some(active);
            }
        }
        let focus = self.conn.get_input_focus().ok()?.reply().ok()?.focus;
        (focus > 1).then_some(focus)
    }

    /// The windows a user works in, front to back, in global points.
    pub(super) fn windows(&self) -> Result<Vec<Window>, XError> {
        let focused = self.focused();
        Ok(self
            .toplevels()?
            .into_iter()
            .filter_map(|top| self.describe(top, focused))
            .collect())
    }

    /// `top` as the window list shows it; `None` for windows it skips or
    /// that vanished while read.
    fn describe(&self, top: TopLevel, focused: Option<xproto::Window>) -> Option<Window> {
        let attributes = self
            .conn
            .get_window_attributes(top.client.0)
            .ok()?
            .reply()
            .ok()?;
        if attributes.map_state != MapState::VIEWABLE
            || attributes.class == WindowClass::INPUT_ONLY
            || attributes.override_redirect
            || !self.kind(top.client).listed()
        {
            return None;
        }
        let placed = self.placed(top.client).ok()?;
        if placed.width < 2 || placed.height < 2 {
            return None;
        }
        let pid = self.pid(top.client);
        Some(Window {
            id: top.client.id(),
            title: self.title(top.client),
            app: self.app(top.client, pid),
            pid,
            bounds: placed,
            focus: match focused {
                Some(focus) if focus == top.client.0 || self.is_within(focus, top.client) => {
                    Focus::Focused
                }
                Some(_) | None => Focus::Unfocused,
            },
        })
    }

    /// The listed window of process `pid` titled `title`: where an
    /// accessibility frame's keys go.
    pub(super) fn window_of(&self, pid: Pid, title: &str) -> Result<Window, Error> {
        let mut matches = self
            .windows()?
            .into_iter()
            .filter(|window| window.pid == Some(pid) && window.title == title);
        match (matches.next(), matches.next()) {
            (Some(window), None) => Ok(window),
            (None, _) => Err(Error::Refused(Refusal::Ax {
                detail: "the element's frame has no matching X window".into(),
            })),
            (Some(_), Some(_)) => Err(Error::Refused(Refusal::Ax {
                detail: "the element's frame matches several X windows; refusing ambiguous input"
                    .into(),
            })),
        }
    }

    /// The top-level window shown at `(x, y)`, override-redirect popups
    /// included.
    fn shown_at(&self, x: i16, y: i16) -> Result<Option<XWindow>, XError> {
        let tree = self.conn.query_tree(self.root)?.reply()?;
        for child in tree.children.into_iter().rev() {
            let Ok(attributes) = self.conn.get_window_attributes(child)?.reply() else {
                continue;
            };
            if attributes.map_state != MapState::VIEWABLE
                || attributes.class == WindowClass::INPUT_ONLY
            {
                continue;
            }
            let Ok(geometry) = self.conn.get_geometry(child)?.reply() else {
                continue;
            };
            let border = i32::from(geometry.border_width) * 2;
            let inside = |at: i16, start: i16, size: u16| {
                let offset = i32::from(at) - i32::from(start);
                offset >= 0 && offset < i32::from(size) + border
            };
            if inside(x, geometry.x, geometry.width) && inside(y, geometry.y, geometry.height) {
                return Ok(Some(XWindow(child)));
            }
        }
        Ok(None)
    }

    /// Makes `window` the focused window, waiting until the window manager
    /// (or, without one, the server) confirms it. Nothing reaches the app.
    fn activate(&self, window: XWindow, token: &Token) -> Result<(), Error> {
        let focused = |this: &Self| {
            this.conn
                .get_input_focus()
                .ok()
                .and_then(|cookie| cookie.reply().ok())
                .is_some_and(|reply| this.is_within(reply.focus, window))
        };
        if focused(self) {
            return Ok(());
        }
        let request = if self.managed() {
            let active = self
                .window_property(self.root, self.atoms._NET_ACTIVE_WINDOW)
                .unwrap_or(x11rb::NONE);
            // Source 2: a pager, which window managers honour without focus
            // stealing prevention.
            let event = ClientMessageEvent::new(
                32,
                window.0,
                self.atoms._NET_ACTIVE_WINDOW,
                [2, CURRENT_TIME, active, 0, 0],
            );
            self.conn
                .send_event(
                    false,
                    self.root,
                    EventMask::SUBSTRUCTURE_REDIRECT | EventMask::SUBSTRUCTURE_NOTIFY,
                    event,
                )
                .map(|_| ())
        } else {
            self.conn
                .configure_window(
                    self.frame_of(window).0,
                    &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE),
                )
                .and_then(|_| {
                    self.conn
                        .set_input_focus(InputFocus::PARENT, window.0, CURRENT_TIME)
                })
                .map(|_| ())
        };
        request
            .and_then(|()| self.conn.flush())
            .map_err(|error| Error::from(XError::from(error)))?;
        let deadline = Instant::now() + ACTIVATION_BUDGET;
        while Instant::now() < deadline {
            if focused(self) {
                return Ok(());
            }
            token.wait(FOCUS_POLL)?;
        }
        Err(Error::Refused(Refusal::Platform {
            detail: format!(
                "window {} did not take the keyboard focus within {} ms (it may be minimized, on \
                 another workspace or behind a modal dialog)",
                window.0,
                ACTIVATION_BUDGET.as_millis()
            )
            .into(),
        }))
    }

    /// The focus and pointer a takeover hands back.
    fn user_state(&self) -> Result<UserState, XError> {
        let focus = self.conn.get_input_focus()?.reply()?;
        let pointer = self.conn.query_pointer(self.root)?.reply()?;
        Ok(UserState {
            active: self
                .managed()
                .then(|| self.window_property(self.root, self.atoms._NET_ACTIVE_WINDOW))
                .flatten(),
            focus: focus.focus,
            revert: focus.revert_to,
            pointer: (pointer.root_x, pointer.root_y),
        })
    }

    /// Gives focus back to the user's window while `target` still holds it,
    /// and the pointer back when the takeover left it where it moved it.
    fn hand_back(&self, user: &UserState, target: XWindow, moved_to: Option<(i16, i16)>) {
        let still_ours = self
            .conn
            .get_input_focus()
            .ok()
            .and_then(|cookie| cookie.reply().ok())
            .is_some_and(|reply| self.is_within(reply.focus, target));
        if still_ours {
            match user.active.filter(|active| *active != target.0) {
                Some(active) => {
                    let event = ClientMessageEvent::new(
                        32,
                        active,
                        self.atoms._NET_ACTIVE_WINDOW,
                        [2, CURRENT_TIME, target.0, 0, 0],
                    );
                    // Best effort: the input already landed, so a failed
                    // hand-back must not fail the step and invite a retry.
                    self.conn
                        .send_event(
                            false,
                            self.root,
                            EventMask::SUBSTRUCTURE_REDIRECT | EventMask::SUBSTRUCTURE_NOTIFY,
                            event,
                        )
                        .ok();
                }
                None if user.focus > 1 => {
                    self.conn
                        .set_input_focus(user.revert, user.focus, CURRENT_TIME)
                        .ok();
                }
                None => {}
            }
        }
        let pointer_now = self
            .conn
            .query_pointer(self.root)
            .ok()
            .and_then(|cookie| cookie.reply().ok())
            .map(|reply| (reply.root_x, reply.root_y));
        if let Some(moved_to) = moved_to.filter(|moved| pointer_now == Some(*moved)) {
            let (x, y) = user.pointer;
            if moved_to != user.pointer {
                self.conn
                    .warp_pointer(x11rb::NONE, self.root, 0, 0, 0, 0, x, y)
                    .ok();
            }
        }
        self.conn.flush().ok();
    }
}

/// What the user had before a takeover.
struct UserState {
    active: Option<xproto::Window>,
    focus: xproto::Window,
    revert: InputFocus,
    pointer: (i16, i16),
}

fn present(conn: &RustConnection, name: &'static str) -> Result<Support, XError> {
    Ok(
        match x11rb::connection::RequestConnection::extension_information(conn, name)? {
            Some(_) => Support::Supported,
            None => Support::Unsupported,
        },
    )
}

/// The class of a `WM_CLASS` value `instance\0class\0`.
fn wm_class(value: &[u8]) -> Option<&str> {
    let mut parts = value.split(|byte| *byte == 0);
    let instance = parts.next()?;
    let class = parts
        .next()
        .filter(|class| !class.is_empty())
        .unwrap_or(instance);
    std::str::from_utf8(class)
        .ok()
        .filter(|class| !class.is_empty())
}

/// How long an opened application gets to show a window.
const APP_WINDOW_WAIT: Duration = Duration::from_secs(5);

/// Brings forward the window of process `pid`, or of any process running
/// `executable`, waiting for one to appear.
pub(in crate::linux) fn activate_process(
    pid: Option<Pid>,
    executable: Option<&Path>,
) -> Result<Window, Error> {
    let x = X11::open()?;
    let token = crate::control::CancelSource::default().token();
    let deadline = Instant::now() + APP_WINDOW_WAIT;
    let runs = |window: &Window| {
        window.pid.is_some_and(|owner| {
            Some(owner) == pid
                || executable.is_some_and(|executable| {
                    std::fs::read_link(format!("/proc/{}/exe", owner.0))
                        .is_ok_and(|path| path == executable)
                })
        })
    };
    loop {
        if let Some(window) = x.windows()?.into_iter().find(runs) {
            x.activate(XWindow::of(&window.id)?, &token)?;
            return Ok(window);
        }
        if Instant::now() >= deadline {
            return Err(Error::Refused(Refusal::Platform {
                detail: "the application runs, but no window of its process appeared within 5 s; \
                         wrappers and sandboxes may hide it"
                    .into(),
            }));
        }
        token.wait(FOCUS_POLL)?;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_class_names_the_app_and_the_instance_stands_in() {
        assert_eq!(wm_class(b"gedit\0Gedit\0"), Some("Gedit"));
        assert_eq!(wm_class(b"xterm\0"), Some("xterm"));
        assert_eq!(wm_class(b""), None);
    }

    #[test]
    fn window_ids_parse_back_or_name_the_missing_window() {
        assert_eq!(
            XWindow::of(&WindowId::new("4194307")),
            Ok(XWindow(4_194_307))
        );
        let bad = WindowId::new("atspi:1");
        assert_eq!(XWindow::of(&bad), Err(WindowError::NotFound(bad)));
    }

    #[test]
    fn only_working_windows_are_listed() {
        assert!(Kind::Dialog.listed());
        assert!(!Kind::Menu.listed());
        assert!(!Kind::Dock.listed());
    }
}
