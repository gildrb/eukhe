//! Element reads for the tree walk and the element steps: one batched read
//! per element, labels, identity, and where focus is (port of omp
//! `crates/natives/src/desktop/macos/ax.rs`).

use std::hash::{DefaultHasher, Hash, Hasher};
use std::ops::Range;

use super::ffi::ax::{AxCode, AxHandle, Names, Read, Value, Width};
use super::ffi::sky::Spi;
use crate::ax::{
    Availability, AxProps, Completeness, Identity, Role, Selection, Unread, WalkBounds,
};
use crate::error::{Error, Permission, Refusal, Unverified};
use crate::geometry::ElementBounds;
use crate::types::{Focus, Window};

/// How long an app may take to answer one request.
pub(super) const AX_TIMEOUT_SECONDS: f32 = 2.0;

/// The attributes one element read asks for, in one round trip. Ordered so
/// each read is a contiguous range: a walk without bounds drops the last
/// two, `props` drops `AXChildren`, whose count it reads without the array.
const NODE_ATTRIBUTES: [&str; 18] = [
    "AXChildren",
    "AXRole",
    "AXTitle",
    "AXValue",
    "AXDescription",
    "AXEnabled",
    "AXFocused",
    "AXSelected",
    "AXSubrole",
    "AXRoleDescription",
    "AXValueDescription",
    "AXHelp",
    "AXIdentifier",
    "AXURL",
    "AXPlaceholderValue",
    "AXTitleUIElement",
    "AXPosition",
    "AXSize",
];
const CHILDREN: usize = 0;
const ROLE: usize = 1;
const TITLE: usize = 2;
const VALUE: usize = 3;
const DESCRIPTION: usize = 4;
const ENABLED: usize = 5;
const FOCUSED: usize = 6;
const SELECTED: usize = 7;
const SUBROLE: usize = 8;
const ROLE_DESCRIPTION: usize = 9;
const VALUE_DESCRIPTION: usize = 10;
const HELP: usize = 11;
const IDENTIFIER: usize = 12;
const URL: usize = 13;
const PLACEHOLDER: usize = 14;
const TITLE_ELEMENT: usize = 15;
const POSITION: usize = 16;
const SIZE: usize = 17;

/// The attributes that, with the role, tell an element apart in its window.
const IDENTIFYING: [usize; 11] = [
    SUBROLE,
    ROLE_DESCRIPTION,
    TITLE,
    DESCRIPTION,
    VALUE,
    VALUE_DESCRIPTION,
    HELP,
    IDENTIFIER,
    URL,
    PLACEHOLDER,
    TITLE_ELEMENT,
];

/// Which slice of [`NODE_ATTRIBUTES`] one read requests.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum NodeRead {
    Walk,
    WalkWithBounds,
    Props,
}

impl NodeRead {
    const fn attributes(self) -> Range<usize> {
        match self {
            Self::Walk => CHILDREN..POSITION,
            Self::WalkWithBounds => CHILDREN..NODE_ATTRIBUTES.len(),
            Self::Props => ROLE..NODE_ATTRIBUTES.len(),
        }
    }

    pub(super) const fn of(bounds: WalkBounds) -> Self {
        match bounds {
            WalkBounds::Read => Self::WalkWithBounds,
            WalkBounds::Skip => Self::Walk,
        }
    }
}

/// Each [`NodeRead`]'s names as the array it sends, built once per backend.
pub(super) struct Requests {
    walk: Names,
    walk_bounds: Names,
    props: Names,
}

impl Requests {
    pub(super) fn new() -> Self {
        let names = |read: NodeRead| Names::new(&NODE_ATTRIBUTES[read.attributes()]);
        Self {
            walk: names(NodeRead::Walk),
            walk_bounds: names(NodeRead::WalkWithBounds),
            props: names(NodeRead::Props),
        }
    }

    fn names(&self, read: NodeRead) -> &Names {
        match read {
            NodeRead::Walk => &self.walk,
            NodeRead::WalkWithBounds => &self.walk_bounds,
            NodeRead::Props => &self.props,
        }
    }
}

/// One element's values from a batched read.
pub(super) struct NodeValues {
    values: Vec<Read>,
    /// [`NODE_ATTRIBUTES`] index of the first value.
    first: usize,
}

impl NodeValues {
    pub(super) fn read(element: &AxHandle, requests: &Requests, read: NodeRead) -> Self {
        Self {
            values: element.read_many(requests.names(read)),
            first: read.attributes().start,
        }
    }

    fn get(&self, index: usize) -> &Read {
        const UNREAD: Read = Err(AxCode::Failure);
        index
            .checked_sub(self.first)
            .and_then(|offset| self.values.get(offset))
            .unwrap_or(&UNREAD)
    }

    fn text(&self, index: usize) -> Option<&str> {
        match self.get(index) {
            Ok(Some(Value::Text(text))) => Some(text),
            Ok(_) | Err(_) => None,
        }
    }

    fn flag(&self, index: usize) -> Option<bool> {
        match self.get(index) {
            Ok(Some(Value::Bool(flag))) => Some(*flag),
            Ok(Some(Value::Int(number))) => Some(*number != 0),
            Ok(_) | Err(_) => None,
        }
    }

    /// The children a walk read, and whether the app answered for them.
    pub(super) fn take_children(&mut self) -> (Vec<AxHandle>, Answer) {
        let Some(slot) = CHILDREN
            .checked_sub(self.first)
            .and_then(|offset| self.values.get_mut(offset))
        else {
            return (Vec::new(), Answer::Unanswered);
        };
        let answer = answered(slot);
        match std::mem::replace(slot, Ok(None)) {
            Ok(Some(Value::Elements(children))) => (children, answer),
            Ok(_) | Err(_) => (Vec::new(), answer),
        }
    }
}

/// Whether a read got the element's answer: a value, or its saying it has
/// none.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Answer {
    Answered,
    Unanswered,
}

fn answered(read: &Read) -> Answer {
    match read {
        Ok(_) | Err(AxCode::NoValue | AxCode::AttributeUnsupported) => Answer::Answered,
        Err(_) => Answer::Unanswered,
    }
}

/// An AX failure before anything was sent.
pub(super) fn refused(code: AxCode, what: &str) -> Error {
    match code {
        AxCode::InvalidElement => Error::Refused(Refusal::Vanished),
        AxCode::ApiDisabled => Error::Refused(Refusal::NotPermitted {
            permission: Permission::Accessibility,
        }),
        AxCode::CannotComplete => Error::Refused(Refusal::Ax {
            detail: format!("{what}: the app did not answer in time").into(),
        }),
        AxCode::Failure
        | AxCode::IllegalArgument
        | AxCode::AttributeUnsupported
        | AxCode::ActionUnsupported
        | AxCode::NotImplemented
        | AxCode::NoValue
        | AxCode::Other(_) => Error::Refused(Refusal::Ax {
            detail: format!("{what} ({code:?})").into(),
        }),
    }
}

/// An AX failure of a write or action: one the app did not answer in time
/// may still apply.
pub(super) fn after_send(code: AxCode, what: &str) -> Error {
    match code {
        AxCode::CannotComplete => Error::Unverified(Unverified::AxUnconfirmed {
            detail: format!(
                "{what}: the app did not answer in time, so it may already have taken effect"
            )
            .into(),
        }),
        AxCode::InvalidElement
        | AxCode::ApiDisabled
        | AxCode::Failure
        | AxCode::IllegalArgument
        | AxCode::AttributeUnsupported
        | AxCode::ActionUnsupported
        | AxCode::NotImplemented
        | AxCode::NoValue
        | AxCode::Other(_) => refused(code, what),
    }
}

/// Builds one element's props from its batched values; `linked` reads the
/// label of an `AXTitleUIElement`.
pub(super) fn props(
    values: &NodeValues,
    child_count: u32,
    bounds: WalkBounds,
    actions: Vec<String>,
    linked: impl FnOnce(&AxHandle) -> Result<Option<String>, AxCode>,
) -> Result<AxProps, Error> {
    let native_role = match values.get(ROLE) {
        Ok(Some(Value::Text(role))) => role.clone(),
        Ok(_) => {
            return Err(Error::Refused(Refusal::Ax {
                detail: "the element has no role".into(),
            }))
        }
        Err(code) => return Err(refused(*code, "reading the element's role")),
    };
    let own_title = nonempty(values.text(TITLE));
    let own_description = nonempty(values.text(DESCRIPTION));
    let has_own_label = own_title.is_some() || own_description.is_some();
    let placeholder = if has_own_label {
        None
    } else {
        nonempty(values.text(PLACEHOLDER))
    };
    let linked_label = if has_own_label {
        Ok(None)
    } else {
        match values.get(TITLE_ELEMENT) {
            Ok(Some(Value::Element(label))) => linked(label),
            Ok(_) | Err(AxCode::Failure | AxCode::NoValue | AxCode::AttributeUnsupported) => {
                Ok(None)
            }
            Err(code) => Err(*code),
        }
    };
    let value = values.get(VALUE).as_ref().ok().and_then(|value| {
        value
            .as_ref()
            .and_then(|value| nonempty_owned(stringify(value)))
    });
    let (title, description, linked_read) = match linked_label {
        Ok(Some(label)) => (Some(label), None, Answer::Answered),
        Ok(None) => (own_title, own_description.or(placeholder), Answer::Answered),
        Err(_) => (
            own_title,
            own_description.or(placeholder),
            Answer::Unanswered,
        ),
    };
    let label_read = label_complete(values, &native_role, title.is_some(), has_own_label);
    let role_name = window_control_name(
        &native_role,
        title.is_some() || description.is_some(),
        values.text(SUBROLE),
    );
    let identity = match linked_read {
        Answer::Answered => identity(values, &native_role, [&title, &value, &description]),
        Answer::Unanswered => None,
    };
    let fields = match identity {
        Some(_) => Completeness::Whole,
        None => Completeness::Partial,
    };
    Ok(AxProps {
        role: Role::from_macos(&native_role),
        availability: match values.flag(ENABLED) {
            Some(false) => Availability::Disabled,
            Some(true) | None => Availability::Enabled,
        },
        focus: match values.flag(FOCUSED) {
            Some(true) => Focus::Focused,
            Some(false) | None => Focus::Unfocused,
        },
        selection: selection(values, &native_role),
        bounds: match bounds {
            WalkBounds::Read => element_bounds(values.get(POSITION), values.get(SIZE)),
            WalkBounds::Skip => None,
        },
        native_role,
        title,
        value,
        description,
        role_name: role_name.map(str::to_owned),
        actions,
        child_count,
        identity: identity.map(Identity),
        fields,
        label_read,
        unread_children: Unread::Count(0),
    })
}

fn nonempty(text: Option<&str>) -> Option<String> {
    text.filter(|text| !text.is_empty()).map(str::to_owned)
}

fn nonempty_owned(text: Option<String>) -> Option<String> {
    text.filter(|text| !text.is_empty())
}

/// Whether the role and every field the label is chosen from answered.
fn label_complete(
    values: &NodeValues,
    native_role: &str,
    titled: bool,
    has_own_label: bool,
) -> Completeness {
    let answers = |index| label_answered(values.get(index));
    let complete = answers(TITLE)
        && (titled
            || (answers(DESCRIPTION)
                && (has_own_label || answers(PLACEHOLDER))
                && (native_role != "AXButton" || answers(SUBROLE))));
    if complete {
        Completeness::Whole
    } else {
        Completeness::Partial
    }
}

/// An absent string is an answer; an error or a value of another type is
/// not.
fn label_answered(read: &Read) -> bool {
    match read {
        Ok(None | Some(Value::Text(_))) | Err(AxCode::NoValue | AxCode::AttributeUnsupported) => {
            true
        }
        Ok(Some(_)) | Err(_) => false,
    }
}

/// The name a window's own unlabelled button takes from its subrole.
fn window_control_name(
    native_role: &str,
    labelled: bool,
    subrole: Option<&str>,
) -> Option<&'static str> {
    if labelled || native_role != "AXButton" {
        return None;
    }
    match subrole? {
        "AXCloseButton" => Some("close"),
        "AXMinimizeButton" => Some("minimize"),
        "AXZoomButton" => Some("zoom"),
        "AXFullScreenButton" => Some("full screen"),
        _ => None,
    }
}

/// Rows, cells, buttons and file icons report selection; Finder's icon
/// list reports a section, not its icons, as selected.
fn selection(values: &NodeValues, native_role: &str) -> Selection {
    let selectable = matches!(native_role, "AXRow" | "AXCell" | "AXButton" | "AXImage");
    if selectable && values.flag(SELECTED) == Some(true) {
        Selection::Selected
    } else {
        Selection::Unselected
    }
}

/// The element's identity, hashed from its role and identifying
/// attributes; `None` when the app did not answer one of them. A read that
/// fails outright counts as its own value: `AppKit` fails some on every read.
fn identity(
    values: &NodeValues,
    native_role: &str,
    [title, value, description]: [&Option<String>; 3],
) -> Option<u64> {
    let mut hasher = DefaultHasher::new();
    native_role.hash(&mut hasher);
    for index in IDENTIFYING {
        let read = values.get(index);
        if let Err(AxCode::Failure) = read {
            hasher.write_u8(0);
            continue;
        }
        if answered(read) == Answer::Unanswered {
            return None;
        }
        hasher.write_u8(1);
        match index {
            TITLE => title.hash(&mut hasher),
            VALUE => value.hash(&mut hasher),
            DESCRIPTION => description.hash(&mut hasher),
            URL => match read {
                Ok(Some(Value::Url(url))) => Some(url.as_str()),
                Ok(_) | Err(_) => None,
            }
            .hash(&mut hasher),
            _ => match read {
                Ok(Some(Value::Text(text))) if !text.is_empty() => Some(text.as_str()),
                Ok(_) | Err(_) => None,
            }
            .hash(&mut hasher),
        }
    }
    Some(hasher.finish())
}

/// A value as stable text: numbers as numbers, an element (a radio
/// group's selected button) as its title; `None` for structured values.
pub(super) fn stringify(value: &Value) -> Option<String> {
    match value {
        Value::Text(text) | Value::Url(text) => Some(text.clone()),
        Value::Bool(flag) => Some(flag.to_string()),
        Value::Int(number) => Some(number.to_string()),
        #[allow(
            clippy::cast_possible_truncation,
            reason = "a single-width float prints at the precision it was stored with"
        )]
        Value::Float(number, Width::Single) => Some((*number as f32).to_string()),
        Value::Float(number, Width::Double) => Some(number.to_string()),
        Value::Element(element) => [element.read("AXTitle"), element.read("AXDescription")]
            .into_iter()
            .find_map(|read| match read {
                Ok(Some(Value::Text(text))) if !text.is_empty() => Some(text),
                Ok(_) | Err(_) => None,
            }),
        Value::Elements(_)
        | Value::Point { .. }
        | Value::Size { .. }
        | Value::Range { .. }
        | Value::Other => None,
    }
}

fn element_bounds(position: &Read, size: &Read) -> Option<ElementBounds> {
    match (position, size) {
        (Ok(Some(Value::Point { x, y })), Ok(Some(Value::Size { width, height }))) => {
            Some(ElementBounds {
                x: *x,
                y: *y,
                width: *width,
                height: *height,
            })
        }
        (Ok(_) | Err(_), Ok(_) | Err(_)) => None,
    }
}

/// The label of a linked title element: its value, as static text holds
/// it, else its title.
pub(super) fn linked_label(label: &AxHandle) -> Result<Option<String>, AxCode> {
    for attribute in ["AXValue", "AXTitle"] {
        match label.read(attribute) {
            Ok(Some(Value::Text(text))) if !text.is_empty() => return Ok(Some(text)),
            Ok(_) | Err(AxCode::NoValue | AxCode::AttributeUnsupported | AxCode::Failure) => {}
            Err(code) => return Err(code),
        }
    }
    Ok(None)
}

/// The application element of `pid`, with the session's request timeout.
pub(super) fn application(pid: i32) -> AxHandle {
    let app = AxHandle::application(pid);
    app.set_timeout(AX_TIMEOUT_SECONDS);
    app
}

pub(super) fn element(read: Read) -> Option<AxHandle> {
    match read {
        Ok(Some(Value::Element(element))) => Some(element),
        Ok(_) | Err(_) => None,
    }
}

/// The window element of `window` in its app: the one with its window
/// server id, else the one with its frame and title.
pub(super) fn window_element(spi: &Spi, pid: i32, window: &Window) -> Result<AxHandle, Error> {
    let app = application(pid);
    let windows = match app.read("AXWindows") {
        Ok(Some(Value::Elements(windows))) => windows,
        Ok(_) => Vec::new(),
        Err(code) => return Err(refused(code, "listing the app's windows")),
    };
    let id = super::windows::server_id(window);
    if let (Some(get), Some(id)) = (spi.window_id_fn(), id) {
        if let Some(found) = windows
            .iter()
            .find(|element| element.window_id(get) == Some(id))
        {
            return Ok(found.clone());
        }
    }
    windows
        .into_iter()
        .find(|element| frames_match(element, window))
        .ok_or_else(|| {
            Error::Refused(Refusal::Ax {
                detail: format!(
                    "window {} is not among {}'s accessibility windows",
                    window.id, window.app
                )
                .into(),
            })
        })
}

fn frames_match(element: &AxHandle, window: &Window) -> bool {
    let close = |a: f64, b: f64| (a - b).abs() <= 2.0;
    let bounds = element_bounds(&element.read("AXPosition"), &element.read("AXSize"));
    let title = match element.read("AXTitle") {
        Ok(Some(Value::Text(title))) => title,
        Ok(_) | Err(_) => String::new(),
    };
    bounds.is_some_and(|bounds| {
        close(bounds.x, f64::from(window.bounds.x))
            && close(bounds.y, f64::from(window.bounds.y))
            && close(bounds.width, f64::from(window.bounds.width))
            && close(bounds.height, f64::from(window.bounds.height))
    }) && (window.title.is_empty() || title == window.title)
}

/// The window server id of the window `pid` reports focused.
pub(super) fn focused_window_id(spi: &Spi, pid: i32) -> Option<u32> {
    let get = spi.window_id_fn()?;
    element(application(pid).read("AXFocusedWindow"))?.window_id(get)
}

/// The element holding keyboard focus in `pid`.
pub(super) fn focused_element(pid: i32) -> Option<AxHandle> {
    element(application(pid).read("AXFocusedUIElement"))
}

/// The window server id of the window `element` sits in.
pub(super) fn element_window_id(spi: &Spi, element: &AxHandle) -> Option<u32> {
    let get = spi.window_id_fn()?;
    self::element(element.read("AXWindow"))?.window_id(get)
}

/// The element's role as its app names it.
pub(super) fn native_role(element: &AxHandle) -> Result<String, Error> {
    match element.read("AXRole") {
        Ok(Some(Value::Text(role))) => Ok(role),
        Ok(_) => Err(Error::Refused(Refusal::Ax {
            detail: "the element has no role".into(),
        })),
        Err(code) => Err(refused(code, "reading the element's role")),
    }
}

/// Whether the app reports itself active.
pub(super) fn reports_active(pid: i32) -> Option<bool> {
    match application(pid).read("AXFrontmost") {
        Ok(Some(Value::Bool(active))) => Some(active),
        Ok(_) | Err(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn values(entries: &[(usize, Read)], read: NodeRead) -> NodeValues {
        let range = read.attributes();
        let mut values: Vec<Read> = vec![Err(AxCode::NoValue); range.len()];
        for (index, value) in entries {
            values[index - range.start] = value.clone();
        }
        NodeValues {
            values,
            first: range.start,
        }
    }

    #[allow(clippy::unnecessary_wraps, reason = "a read as the batch gives it")]
    fn text(text: &str) -> Read {
        Ok(Some(Value::Text(text.to_owned())))
    }

    fn read(entries: &[(usize, Read)]) -> Result<AxProps, Error> {
        props(
            &values(entries, NodeRead::Props),
            0,
            WalkBounds::Read,
            Vec::new(),
            |_| Ok(None),
        )
    }

    #[test]
    fn a_button_reads_its_title_value_state_and_bounds() {
        let props = read(&[
            (ROLE, text("AXButton")),
            (TITLE, text("Press me")),
            (ENABLED, Ok(Some(Value::Bool(false)))),
            (POSITION, Ok(Some(Value::Point { x: 10.0, y: 20.0 }))),
            (
                SIZE,
                Ok(Some(Value::Size {
                    width: 80.0,
                    height: 24.0,
                })),
            ),
        ])
        .unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(props.role, Role::Button);
        assert_eq!(props.title.as_deref(), Some("Press me"));
        assert_eq!(props.availability, Availability::Disabled);
        assert_eq!(props.bounds.map(|bounds| bounds.center().x), Some(50.0));
        assert_eq!(props.label_read, Completeness::Whole);
        assert_eq!(props.fields, Completeness::Whole);
    }

    #[test]
    fn an_unlabelled_window_button_takes_its_subrole_name() {
        let props = read(&[(ROLE, text("AXButton")), (SUBROLE, text("AXCloseButton"))])
            .unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(props.label(), Some("close"));
    }

    #[test]
    fn a_field_without_a_label_uses_its_placeholder() {
        let props = read(&[(ROLE, text("AXTextField")), (PLACEHOLDER, text("Name"))])
            .unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(props.label(), Some("Name"));
    }

    #[test]
    fn an_unanswered_identifying_field_leaves_no_identity() {
        let props = read(&[
            (ROLE, text("AXButton")),
            (HELP, Err(AxCode::CannotComplete)),
        ])
        .unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(props.identity, None);
        assert_eq!(props.fields, Completeness::Partial);
        // AppKit fails some attributes on every read: that is an answer.
        let props = read(&[(ROLE, text("AXButton")), (HELP, Err(AxCode::Failure))])
            .unwrap_or_else(|error| panic!("{error}"));
        assert!(props.identity.is_some());
    }

    #[test]
    fn a_gone_element_is_vanished_and_an_untrusted_process_is_refused() {
        assert_eq!(
            read(&[(ROLE, Err(AxCode::InvalidElement))]).err(),
            Some(Error::Refused(Refusal::Vanished))
        );
        assert_eq!(
            read(&[(ROLE, Err(AxCode::ApiDisabled))]).err(),
            Some(Error::Refused(Refusal::NotPermitted {
                permission: Permission::Accessibility
            }))
        );
    }

    #[test]
    fn numbers_print_at_their_stored_precision() {
        assert_eq!(
            stringify(&Value::Float(f64::from(0.185f32), Width::Single)).as_deref(),
            Some("0.185")
        );
        assert_eq!(stringify(&Value::Int(1)).as_deref(), Some("1"));
        assert_eq!(
            stringify(&Value::Range {
                location: 0,
                length: 1
            }),
            None
        );
    }

    #[test]
    fn a_write_the_app_did_not_answer_may_have_landed() {
        assert!(matches!(
            after_send(AxCode::CannotComplete, "pressing"),
            Error::Unverified(Unverified::AxUnconfirmed { .. })
        ));
        assert!(matches!(
            after_send(AxCode::ActionUnsupported, "pressing"),
            Error::Refused(Refusal::Ax { .. })
        ));
    }
}
