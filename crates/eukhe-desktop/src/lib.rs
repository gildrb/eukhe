//! Desktop computer use: windows, screenshots, accessibility trees with
//! stable `[ref=eN]` refs, and typed input steps on one window, delivered in
//! the background unless the caller's takeover policy allows otherwise.
//!
//! A [`Desktop`] session owns one worker thread and the platform backend
//! (`macos` or `linux`, chosen at compile time; see `backend`). Its
//! [`Reader`] inspects; its [`Executor`] sends input, each step reporting an
//! [`Effect`]: confirmed, unverifiable, or refused with nothing sent.

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
compile_error!("eukhe-desktop supports macOS and Linux");

mod applications;
mod ax;
mod backend;
mod control;
mod error;
mod frame;
mod geometry;
mod keys;
mod menus;
mod roster;
mod session;
mod text_range;
mod types;

#[cfg(target_os = "linux")]
mod linux;
#[cfg(target_os = "macos")]
mod macos;

#[cfg(target_os = "linux")]
use linux as platform;
#[cfg(target_os = "macos")]
use macos as platform;

pub use applications::{
    Activation, AppError, AppQuery, AppScope, AppState, Application, DocumentRoute, OpenRequest,
    Opened,
};
pub use ax::{
    Availability, ElementRef, FindQuery, FoundNode, RefSyntax, Role, Selection, TextLines, Tree,
    TreeOptions, TreeScope, Truncation,
};
pub use backend::{ClickCount, ClickCountRange, MouseButton};
pub use control::default_input_lock;
pub use error::{
    Detail, Done, Effect, ElementError, Error, Feature, FieldReads, Holder, Interruption,
    Intervention, Permission, Readback, Refusal, StaleCause, StaleRef, Unverified, WindowError,
};
pub use frame::{FrameError, Screenshot};
pub use geometry::{ElementBounds, FramePoint, GlobalPoint, GlobalRect, PixelSize, ScrollDelta};
pub use keys::{Chord, FunctionKey, Key, KeyError, Modifier, Modifiers};
pub use menus::{Check, MenuError, MenuItem, MenuPath, Offered, OfferedItem, Submenu, Tier};
pub use roster::{Listing, RosterWindow};
pub use session::{
    ActReport, Desktop, Executor, KeyTarget, Observation, ObserveOptions, PointTarget, Reader,
    SessionOptions, Step,
};
pub use text_range::{Context, SelectPart, TextRangeError, TextSelectRequest, TextSelection};
pub use types::{
    Access, BackendKind, Capabilities, DisplayPower, Focus, ImageCaps, Lock, Pid, ScreenState,
    SecureInput, Support, Takeover, Window, WindowFilter, WindowId, WindowSelector, WindowSummary,
};
