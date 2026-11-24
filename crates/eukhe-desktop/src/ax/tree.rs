//! Walking a window's accessibility tree and printing it as lines with
//! `[ref=eN]` (port of the walk, filter and format passes of omp
//! `crates/natives/src/desktop/ax.rs`).

use std::collections::{HashMap, HashSet};
use std::fmt::{self, Write as _};

use serde::{Deserialize, Serialize};

use super::registry::{Generation, ReadKind, RowProof, Uniqueness, WholeWalk};
use super::{
    ActionNames, Availability, AxProps, AxRead, Completeness, ElementRef, Identity, Registry, Role,
    Selection, Settable, Unread, WalkBounds,
};
use crate::control::Token;
use crate::error::{Error, Refusal};
use crate::geometry::ElementBounds;
use crate::types::{Focus, Window};

/// How far a walk reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SnapshotLimits {
    pub(crate) max_nodes: u32,
    pub(crate) max_depth: u32,
}

impl SnapshotLimits {
    /// What `find` reads: deep enough for the levels Electron nests in.
    pub(crate) const FIND: Self = Self {
        max_nodes: 5_000,
        max_depth: 64,
    };

    /// At least as far as `find` reads.
    pub(crate) fn at_least_find(self) -> Self {
        Self {
            max_nodes: self.max_nodes.max(Self::FIND.max_nodes),
            max_depth: self.max_depth.max(Self::FIND.max_depth),
        }
    }
}

/// Which elements a tree prints.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TreeScope {
    /// Named or actionable elements and the containers that group them.
    #[default]
    Interesting,
    /// Every element read.
    All,
}

/// How an observation reads its window's tree.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TreeOptions {
    /// Levels below the window; 24 when absent.
    #[serde(default)]
    pub max_depth: Option<u32>,
    /// Elements read; 800 when absent.
    #[serde(default)]
    pub max_nodes: Option<u32>,
    #[serde(default)]
    pub scope: TreeScope,
}

impl TreeOptions {
    fn limits(&self) -> SnapshotLimits {
        SnapshotLimits {
            max_nodes: self.max_nodes.unwrap_or(800).max(1),
            max_depth: self.max_depth.unwrap_or(24),
        }
    }
}

/// Whether a walk read every element within its limits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Truncation {
    Complete,
    Truncated,
}

/// A window's tree as text: one element per line, `[ref=eN]` on each.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Tree {
    pub text: String,
    /// Lines printed.
    pub nodes: u32,
    pub truncation: Truncation,
}

/// What `find` looks for: every field a case-insensitive substring; absent
/// fields match anything.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FindQuery {
    #[serde(default)]
    pub role: Option<String>,
    #[serde(default)]
    pub title: Option<String>,
    #[serde(default)]
    pub value: Option<String>,
    /// Most results; 100 when absent, at most 5,000.
    #[serde(default)]
    pub limit: Option<u32>,
}

/// One element `find` returns.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct FoundNode {
    pub reference: ElementRef,
    pub role: Role,
    pub native_role: String,
    pub title: Option<String>,
    pub value: Option<String>,
    pub description: Option<String>,
    pub availability: Availability,
    pub focus: Focus,
    pub selection: Selection,
    pub bounds: Option<ElementBounds>,
    pub actions: Vec<String>,
    pub child_count: u32,
}

impl FoundNode {
    fn new(reference: ElementRef, props: AxProps) -> Self {
        Self {
            reference,
            role: props.role,
            native_role: props.native_role,
            title: props.title,
            value: props.value,
            description: props.description,
            availability: props.availability,
            focus: props.focus,
            selection: props.selection,
            bounds: props.bounds,
            actions: props.actions,
            child_count: props.child_count,
        }
    }
}

/// What a line says about writing an element's value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Writable {
    Unmarked,
    /// A date the backend can write.
    Settable,
    /// A web page's text field the page declares read-only.
    ReadOnly,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Web {
    Outside,
    Inside,
}

/// Whether a walk reads the states only `ax` lines print.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Marks {
    Read,
    Skip,
}

#[derive(Clone)]
pub(super) struct WalkNode<H> {
    pub(super) handle: H,
    pub(super) props: AxProps,
    writable: Writable,
    pub(super) children: Vec<Self>,
}

/// A walk's limits and what it has met so far, threaded through the walk.
pub(super) struct Walk<'t> {
    token: &'t Token,
    limits: SnapshotLimits,
    bounds: WalkBounds,
    marks: Marks,
    visited: u32,
    skipped: u32,
    /// Skipped elements the app destroyed before the walk read them.
    vanished: u32,
    fields: Completeness,
    truncation: Truncation,
    unread: Unread,
}

impl<'t> Walk<'t> {
    pub(super) fn new(
        token: &'t Token,
        limits: SnapshotLimits,
        bounds: WalkBounds,
        marks: Marks,
    ) -> Self {
        Self {
            token,
            limits,
            bounds,
            marks,
            visited: 0,
            skipped: 0,
            vanished: 0,
            fields: Completeness::Whole,
            truncation: Truncation::Complete,
            unread: Unread::Count(0),
        }
    }

    /// The walk of `root`, when it read every element of the window still
    /// there, so it can vouch that an identity is unique there.
    pub(super) fn whole<H: Clone>(&self, root: &H) -> Option<WholeWalk<H>> {
        (self.truncation == Truncation::Complete
            && self.skipped == self.vanished
            && self.fields == Completeness::Whole)
            .then(|| WholeWalk {
                root: root.clone(),
                limits: self.limits,
            })
    }
}

/// A walk's tree, when its root was read, and the walk's state after it.
type Walked<'t, H> = (Option<WalkNode<H>>, Walk<'t>);

/// How a failed read of a child element ends the walk.
enum Failure {
    Vanished,
    Unreadable,
    /// Every read after it fails the same way: a cancel, a timeout.
    Fatal,
}

fn failure(error: &Error) -> Failure {
    match error {
        Error::Refused(refusal) => match refusal {
            Refusal::Vanished => Failure::Vanished,
            Refusal::Cancelled | Refusal::Timeout | Refusal::Closed => Failure::Fatal,
            Refusal::NotPermitted { .. }
            | Refusal::BackgroundUnavailable { .. }
            | Refusal::StaleRef(_)
            | Refusal::UserIntervened(_)
            | Refusal::InputBusy { .. }
            | Refusal::Window(_)
            | Refusal::Frame(_)
            | Refusal::Key(_)
            | Refusal::Menu(_)
            | Refusal::Text(_)
            | Refusal::Application(_)
            | Refusal::Element(_)
            | Refusal::Ax { .. }
            | Refusal::ReadsAs { .. }
            | Refusal::Capture { .. }
            | Refusal::Unsupported { .. }
            | Refusal::ScreenLocked
            | Refusal::DisplayAsleep
            | Refusal::Platform { .. } => Failure::Unreadable,
        },
        Error::Unverified(_) => Failure::Unreadable,
    }
}

/// Reads the tree under `root` within the walk's limits.
pub(super) fn walk<'t, A: AxRead>(
    ax: &mut A,
    root: A::Handle,
    state: Walk<'t>,
) -> Result<Walked<'t, A::Handle>, Error> {
    walk_at(ax, root, 0, Web::Outside, state)
}

fn walk_at<'t, A: AxRead>(
    ax: &mut A,
    handle: A::Handle,
    depth: u32,
    web: Web,
    mut state: Walk<'t>,
) -> Result<Walked<'t, A::Handle>, Error> {
    if depth > state.limits.max_depth || state.visited >= state.limits.max_nodes {
        state.truncation = Truncation::Truncated;
        return Ok((None, state));
    }
    state.token.check()?;
    state.visited += 1;
    // Children past the depth limit are never visited, so none is read.
    let max_children = if depth < state.limits.max_depth {
        state.limits.max_nodes - state.visited
    } else {
        0
    };
    let (props, handles) = match ax.walk_node(&handle, state.bounds, max_children) {
        Ok(node) => node,
        Err(error) => match (depth, failure(&error)) {
            (0, _) | (_, Failure::Fatal) => return Err(error),
            (_, Failure::Vanished) => {
                state.skipped = state.skipped.saturating_add(1);
                state.vanished = state.vanished.saturating_add(1);
                return Ok((None, state));
            }
            (_, Failure::Unreadable) => {
                state.skipped = state.skipped.saturating_add(1);
                return Ok((None, state));
            }
        },
    };
    if props.fields == Completeness::Partial {
        state.fields = Completeness::Partial;
    }
    if props.unread_children.any() {
        state.truncation = Truncation::Truncated;
        state.unread = state.unread.add(props.unread_children);
    }
    let web = match (web, &props.role) {
        (Web::Inside, _) | (Web::Outside, Role::WebArea) => Web::Inside,
        (Web::Outside, _) => Web::Outside,
    };
    let writable = match state.marks {
        Marks::Read => writable(ax, &handle, &props, web),
        Marks::Skip => Writable::Unmarked,
    };
    let mut children = Vec::with_capacity(handles.len());
    for child in handles {
        let (node, next) = walk_at(ax, child, depth + 1, web, state)?;
        state = next;
        children.extend(node);
        if state.truncation == Truncation::Truncated && state.visited >= state.limits.max_nodes {
            break;
        }
    }
    Ok((
        Some(WalkNode {
            handle,
            props,
            writable,
            children,
        }),
        state,
    ))
}

/// `(settable)` marks a date outside web content; `(readonly)` an enabled
/// web text field the page declares read-only. Elsewhere the answer proves
/// nothing (a terminal's text area takes keys yet reports itself unsettable).
fn writable<A: AxRead>(ax: &mut A, handle: &A::Handle, props: &AxProps, web: Web) -> Writable {
    let date = web == Web::Outside
        && matches!(
            props.role,
            Role::DateTimeArea | Role::DateField | Role::TimeField
        );
    let page_text = web == Web::Inside
        && props.availability == Availability::Enabled
        && matches!(props.role, Role::TextField | Role::TextArea);
    if !date && !page_text {
        return Writable::Unmarked;
    }
    match ax.value_settable(handle) {
        Settable::Yes if date => Writable::Settable,
        Settable::No if page_text => Writable::ReadOnly,
        Settable::Yes | Settable::No | Settable::Unknown => Writable::Unmarked,
    }
}

/// Drops unnamed, inactionable elements that carry nothing, keeping every
/// survivor below them: a container with no survivors disappears, one around
/// a single survivor (outside [`Role::structural`]) gives way to it.
fn filter_node<H>(mut node: WalkNode<H>, scope: TreeScope) -> Option<WalkNode<H>> {
    node.children = node
        .children
        .into_iter()
        .filter_map(|child| filter_node(child, scope))
        .collect();
    let kept = match scope {
        TreeScope::All => true,
        TreeScope::Interesting => {
            !node.props.actions.is_empty() || node.props.role.interactable() || node.props.named()
        }
    };
    if kept {
        return Some(node);
    }
    match node.children.len() {
        0 => None,
        1 if !node.props.role.structural() => node.children.pop(),
        _ => Some(node),
    }
}

/// What one walk says about whether each identity is unique in its window.
pub(super) struct ReadIdentities<H> {
    shared: HashSet<Identity>,
    whole: Option<WholeWalk<H>>,
    rows: HashMap<H, RowProof<H>>,
}

impl<H: Clone + Eq + std::hash::Hash> ReadIdentities<H> {
    pub(super) fn new(root: &H, tree: Option<&WalkNode<H>>, state: &Walk<'_>) -> Self {
        let mut seen = HashSet::new();
        let mut shared = HashSet::new();
        let mut stack: Vec<_> = tree.into_iter().collect();
        while let Some(node) = stack.pop() {
            stack.extend(&node.children);
            if let Some(identity) = node.props.identity {
                if !seen.insert(identity) {
                    shared.insert(identity);
                }
            }
        }
        let whole = state.whole(root);
        let rows = match (tree, &whole) {
            (Some(tree), Some(walk)) => super::stale::row_places(tree, walk),
            (None, _) | (_, None) => HashMap::new(),
        };
        Self {
            shared,
            whole,
            rows,
        }
    }

    /// A twin anywhere in the walk rules naming out; only a whole walk rules
    /// it in.
    fn of(&self, props: &AxProps) -> Uniqueness<'_, H> {
        match (props.identity, &self.whole) {
            (Some(identity), _) if self.shared.contains(&identity) => Uniqueness::Shared,
            (Some(_), Some(walk)) => Uniqueness::Proven(walk),
            (Some(_), None) | (None, _) => Uniqueness::Unknown,
        }
    }

    /// Registers the element, then records its row when the walk read the
    /// whole window; a partial walk leaves an earlier decision standing.
    pub(super) fn register<A: AxRead<Handle = H>>(
        &self,
        ax: &mut A,
        registry: &mut Registry<H>,
        window: &Window,
        generation: Generation,
        handle: H,
        props: &AxProps,
    ) -> ElementRef {
        let row = self.rows.get(&handle).cloned();
        let reference = registry.register(
            |handle| ax.liveness(handle),
            &window.id,
            generation,
            handle,
            props,
            self.of(props),
        );
        if self.whole.is_some() {
            registry.set_row(reference, row);
        }
        reference
    }
}

/// The application's focused element for one request, read once, and only
/// once an element reports itself focused.
enum AppFocus<H> {
    Unread,
    Read(Option<H>),
}

impl<H: Clone + Eq> AppFocus<H> {
    /// Whether the element holds focus: it reports itself focused and, where
    /// the backend reads the application's focused element, it is that one.
    /// A focused table reports every cell focused.
    fn holds<A: AxRead<Handle = H>>(&mut self, ax: &mut A, handle: &H, props: &AxProps) -> Focus {
        if props.focus == Focus::Unfocused {
            return Focus::Unfocused;
        }
        if let Self::Unread = self {
            *self = Self::Read(ax.focused_within(handle));
        }
        match self {
            Self::Read(Some(focused)) if focused != handle => Focus::Unfocused,
            Self::Read(_) | Self::Unread => Focus::Focused,
        }
    }
}

/// Characters of a label or value a line shows before cutting it.
const SHOWN_CHARS: usize = 200;

/// Writes `text` quoted and escaped, at most `shown` characters, so an app
/// cannot add lines to the output.
fn write_quoted_chars(out: &mut impl fmt::Write, text: &str, shown: usize) -> fmt::Result {
    out.write_char('"')?;
    for character in text.chars().take(shown) {
        match character {
            '"' => out.write_str("\\\"")?,
            '\\' => out.write_str("\\\\")?,
            '\n' => out.write_str("\\n")?,
            '\r' => out.write_str("\\r")?,
            '\t' => out.write_str("\\t")?,
            control if control.is_control() => write!(out, "\\u{:04x}", u32::from(control))?,
            plain => out.write_char(plain)?,
        }
    }
    out.write_char('"')
}

/// An app-controlled label, quoted and cut at [`SHOWN_CHARS`].
pub(crate) fn write_quoted_label(out: &mut impl fmt::Write, text: &str) -> fmt::Result {
    write_quoted_chars(out, text, SHOWN_CHARS)?;
    if text.chars().nth(SHOWN_CHARS).is_some() {
        out.write_char('…')?;
    }
    Ok(())
}

/// A label or value on a line, with how much was cut.
fn write_quoted(out: &mut impl fmt::Write, text: &str) -> fmt::Result {
    write_quoted_chars(out, text, SHOWN_CHARS)?;
    match text.chars().count().checked_sub(SHOWN_CHARS) {
        Some(hidden) if hidden > 0 => write!(out, "… (+{} chars)", Grouped(hidden)),
        Some(_) | None => Ok(()),
    }
}

/// `14230` as `14,230`.
struct Grouped(usize);

impl fmt::Display for Grouped {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let digits = self.0.to_string();
        for (index, digit) in digits.chars().enumerate() {
            if index > 0 && (digits.len() - index).is_multiple_of(3) {
                f.write_char(',')?;
            }
            f.write_char(digit)?;
        }
        Ok(())
    }
}

/// Longest action name a line lists, past its `AX` prefix.
const MAX_SHOWN_ACTION: usize = 32;
/// Most actions a line lists.
const MAX_SHOWN_ACTIONS: usize = 16;

/// When a role already implies an action, so a line leaves it out.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Implied {
    Never,
    /// A control's own press.
    ByPress,
    /// A text input's confirm and cancel.
    ByTextInput,
    /// Actions nearly every element has: scroll into view, context menu,
    /// raise, page scrolls, hover variants.
    Always,
}

const IMPLIED: &[(&str, Implied)] = &[
    ("press", Implied::ByPress),
    ("confirm", Implied::ByTextInput),
    ("cancel", Implied::ByTextInput),
    ("scrolltovisible", Implied::Always),
    ("showmenu", Implied::Always),
    ("raise", Implied::Always),
    ("showalternateui", Implied::Always),
    ("showdefaultui", Implied::Always),
    ("zoomwindow", Implied::Always),
    ("scrollupbypage", Implied::Always),
    ("scrolldownbypage", Implied::Always),
    ("scrollleftbypage", Implied::Always),
    ("scrollrightbypage", Implied::Always),
];

/// A macOS action by the name it is performed by: lowercased past its `AX`
/// prefix.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ActionName {
    name: String,
    implied: Implied,
}

impl ActionName {
    /// `None` for custom actions and for anything but one short ASCII word,
    /// which an app could otherwise use to write its own lines.
    fn parse(action: &str) -> Option<Self> {
        let name = action
            .get(..2)?
            .eq_ignore_ascii_case("AX")
            .then(|| &action[2..])?;
        if name.is_empty()
            || name.len() > MAX_SHOWN_ACTION
            || !name.bytes().all(|byte| byte.is_ascii_alphanumeric())
        {
            return None;
        }
        let implied = IMPLIED
            .iter()
            .find(|(known, _)| known.eq_ignore_ascii_case(name))
            .map_or(Implied::Never, |(_, implied)| *implied);
        Some(Self {
            name: name.to_ascii_lowercase(),
            implied,
        })
    }

    fn implied_by(&self, role: &Role) -> bool {
        match self.implied {
            Implied::Never => false,
            Implied::ByPress => role.pressable(),
            Implied::ByTextInput => role.text_input(),
            Implied::Always => true,
        }
    }
}

/// The actions an element offers beyond what its role implies, each once.
/// A control without its own press lists them all.
fn shown_actions(props: &AxProps, names: ActionNames) -> Vec<ActionName> {
    match names {
        ActionNames::Hidden => return Vec::new(),
        ActionNames::Ax => {}
    }
    let mut shown: Vec<ActionName> = Vec::new();
    for action in props
        .actions
        .iter()
        .filter_map(|action| ActionName::parse(action))
    {
        if !shown.contains(&action) {
            shown.push(action);
        }
    }
    let role = &props.role;
    if !role.pressable()
        || shown
            .iter()
            .any(|action| action.implied == Implied::ByPress)
    {
        shown.retain(|action| !action.implied_by(role));
    }
    shown
}

/// One element's line, without its indent.
struct Line<'a> {
    props: &'a AxProps,
    reference: ElementRef,
    /// The window's app, on the root line only.
    app: Option<&'a str>,
    focus: Focus,
    writable: Writable,
    actions: &'a [ActionName],
}

impl fmt::Display for Line<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "- {}", self.props.role)?;
        if let Some(label) = self.props.label() {
            f.write_char(' ')?;
            write_quoted(f, label)?;
        }
        write!(f, " [ref={}]", self.reference)?;
        if let Some(app) = self.app {
            write!(f, " app={app}")?;
        }
        if let Some(value) = self
            .props
            .value
            .as_deref()
            .filter(|value| !value.is_empty())
        {
            f.write_str(": ")?;
            write_quoted(f, value)?;
        }
        match self.props.availability {
            Availability::Enabled => {}
            Availability::Disabled => f.write_str(" (disabled)")?,
        }
        match self.writable {
            Writable::Unmarked => {}
            Writable::Settable => f.write_str(" (settable)")?,
            Writable::ReadOnly => f.write_str(" (readonly)")?,
        }
        match self.props.selection {
            Selection::Unselected => {}
            Selection::Selected => f.write_str(" (selected)")?,
        }
        match self.focus {
            Focus::Unfocused => {}
            Focus::Focused => f.write_str(" (focused)")?,
        }
        let hidden = self.actions.len().saturating_sub(MAX_SHOWN_ACTIONS);
        for (index, action) in self.actions.iter().take(MAX_SHOWN_ACTIONS).enumerate() {
            f.write_str(if index == 0 { " actions=" } else { "," })?;
            f.write_str(&action.name)?;
        }
        if hidden > 0 {
            write!(f, "… (+{hidden} more)")?;
        }
        Ok(())
    }
}

/// What every line of one printed tree shares.
struct Printer<'a, H> {
    window: &'a Window,
    generation: Generation,
    names: ActionNames,
    identities: &'a ReadIdentities<H>,
}

/// Prints `node` and its children at `depth`, registering each; returns
/// how many lines it printed.
fn print_node<A: AxRead>(
    node: WalkNode<A::Handle>,
    depth: usize,
    printer: &Printer<'_, A::Handle>,
    ax: &mut A,
    registry: &mut Registry<A::Handle>,
    focus: &mut AppFocus<A::Handle>,
    text: &mut String,
) -> Result<u32, fmt::Error> {
    let WalkNode {
        handle,
        props,
        writable,
        children,
    } = node;
    // The root's own focus flag reflects only app-local focus; the window
    // list's flag says whether the window holds the user's focus.
    let (app, focused) = if depth == 0 {
        (Some(printer.window.app.as_str()), printer.window.focus)
    } else {
        (None, focus.holds(ax, &handle, &props))
    };
    let reference = printer.identities.register(
        ax,
        registry,
        printer.window,
        printer.generation,
        handle,
        &props,
    );
    if !text.is_empty() {
        text.push('\n');
    }
    for _ in 0..depth {
        text.push_str("  ");
    }
    let actions = shown_actions(&props, printer.names);
    write!(
        text,
        "{}",
        Line {
            props: &props,
            reference,
            app,
            focus: focused,
            writable,
            actions: &actions,
        }
    )?;
    let mut lines = 1;
    for child in children {
        lines += print_node(child, depth + 1, printer, ax, registry, focus, text)?;
    }
    Ok(lines)
}

/// Unreachable for `String`; kept as a typed failure, not a panic.
fn format_failed(_: fmt::Error) -> Error {
    Error::Refused(Refusal::Platform {
        detail: "the tree text could not be formatted".into(),
    })
}

/// Reads `window`'s tree and prints it, registering a ref for each line.
pub(crate) fn snapshot<A: AxRead>(
    ax: &mut A,
    registry: &mut Registry<A::Handle>,
    window: &Window,
    options: &TreeOptions,
    names: ActionNames,
    token: &Token,
) -> Result<Tree, Error> {
    let root = ax.window_root(window)?;
    let generation = registry.begin_read(&window.id, ReadKind::Snapshot);
    let (tree, state) = walk(
        ax,
        root.clone(),
        Walk::new(token, options.limits(), WalkBounds::Skip, Marks::Read),
    )?;
    let identities = ReadIdentities::new(&root, tree.as_ref(), &state);
    let printer = Printer {
        window,
        generation,
        names,
        identities: &identities,
    };
    let mut text = String::new();
    let nodes = match tree.and_then(|node| filter_node(node, options.scope)) {
        Some(node) => print_node(
            node,
            0,
            &printer,
            ax,
            registry,
            &mut AppFocus::Unread,
            &mut text,
        )
        .map_err(format_failed)?,
        None => 0,
    };
    registry.end_snapshot(&window.id, generation);
    write_notes(&mut text, &state).map_err(format_failed)?;
    Ok(Tree {
        text,
        nodes,
        truncation: state.truncation,
    })
}

fn write_notes(text: &mut String, state: &Walk<'_>) -> fmt::Result {
    if state.truncation == Truncation::Truncated {
        if !text.is_empty() {
            text.push('\n');
        }
        write!(text, "… truncated ({} nodes)", state.visited)?;
        match state.unread {
            Unread::Unknown => text.push_str("; some children not read"),
            Unread::Count(0) => {}
            Unread::Count(count) => write!(text, "; {count} children not read")?,
        }
    }
    if state.skipped > 0 {
        if !text.is_empty() {
            text.push('\n');
        }
        write!(text, "… skipped {} unreadable nodes", state.skipped)?;
    }
    Ok(())
}

/// Query aliases extend the vocabulary without changing printed roles.
const ROLE_ALIASES: &[(&str, Role)] = &[("radiobutton", Role::Radio)];

/// Accepts printed substrings, compact printed substrings, exact compact
/// native roles and aliases.
fn matches_role(props: &AxProps, query: &str, compact: &str) -> bool {
    let printed = props.role.name();
    printed.contains(query)
        || (!compact.is_empty()
            && ((compact.len() != query.len() && printed.contains(compact))
                || props
                    .native_role
                    .chars()
                    .filter(|c| !matches!(c, ' ' | '_' | '-'))
                    .flat_map(char::to_lowercase)
                    .eq(compact.chars())
                || ROLE_ALIASES
                    .iter()
                    .any(|(alias, role)| compact == *alias && props.role == *role)))
}

fn contains_folded(actual: Option<&str>, needle: Option<&str>) -> bool {
    needle.is_none_or(|needle| actual.is_some_and(|text| text.to_lowercase().contains(needle)))
}

/// Every element of `window` matching `query`, each registered.
pub(crate) fn query<A: AxRead>(
    ax: &mut A,
    registry: &mut Registry<A::Handle>,
    window: &Window,
    query: &FindQuery,
    token: &Token,
) -> Result<Vec<FoundNode>, Error> {
    let root = ax.window_root(window)?;
    let generation = registry.begin_read(&window.id, ReadKind::Query);
    let (Some(tree), state) = walk(
        ax,
        root.clone(),
        Walk::new(token, SnapshotLimits::FIND, WalkBounds::Read, Marks::Skip),
    )?
    else {
        return Ok(Vec::new());
    };
    let identities = ReadIdentities::new(&root, Some(&tree), &state);
    let role = query.role.as_deref().map(str::to_lowercase);
    let compact = role
        .as_deref()
        .map(|role| role.replace([' ', '_', '-'], ""));
    let title = query.title.as_deref().map(str::to_lowercase);
    let value = query.value.as_deref().map(str::to_lowercase);
    let limit = usize::try_from(query.limit.unwrap_or(100).min(5_000)).unwrap_or(5_000);
    let mut found = Vec::new();
    let mut focus = AppFocus::Unread;
    let mut stack = vec![tree];
    while let Some(node) = stack.pop() {
        let WalkNode {
            handle,
            mut props,
            children,
            ..
        } = node;
        stack.extend(children.into_iter().rev());
        let role_matches = role
            .as_deref()
            .is_none_or(|role| matches_role(&props, role, compact.as_deref().unwrap_or(role)));
        if role_matches
            && contains_folded(props.label(), title.as_deref())
            && contains_folded(props.value.as_deref(), value.as_deref())
        {
            props.focus = focus.holds(ax, &handle, &props);
            let reference = identities.register(ax, registry, window, generation, handle, &props);
            found.push(FoundNode::new(reference, props));
            if found.len() >= limit {
                break;
            }
        }
    }
    Ok(found)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ax::fake::{props, FakeTree};
    use crate::control::CancelSource;
    use crate::geometry::GlobalRect;
    use crate::types::{Pid, WindowId};

    fn window() -> Window {
        Window {
            id: WindowId::new("7"),
            title: "Notes".to_owned(),
            app: "TextEdit".to_owned(),
            pid: Some(Pid(1)),
            bounds: GlobalRect {
                x: 0,
                y: 0,
                width: 800,
                height: 600,
            },
            focus: Focus::Focused,
        }
    }

    /// window > group > [button "Save", text area with a value, unnamed
    /// group > image] and a disabled checkbox.
    fn tree() -> FakeTree {
        let mut tree = FakeTree {
            root: 1,
            ..FakeTree::default()
        };
        tree.add(1, props(Role::Window, "Notes"), &[2, 6]);
        tree.add(2, props(Role::Group, ""), &[3, 4, 5]);
        let mut save = props(Role::Button, "Save");
        save.actions = vec!["AXPress".to_owned(), "AXShowMenu".to_owned()];
        tree.add(3, save, &[]);
        let mut text = props(Role::TextArea, "");
        text.value = Some("line one\nline \"two\"".to_owned());
        text.focus = Focus::Focused;
        tree.add(4, text, &[]);
        tree.add(5, props(Role::Group, ""), &[8]);
        tree.add(8, props(Role::Image, ""), &[]);
        let mut check = props(Role::CheckBox, "Wrap");
        check.availability = Availability::Disabled;
        check.selection = Selection::Selected;
        tree.add(6, check, &[]);
        tree
    }

    fn print(tree: &mut FakeTree, registry: &mut Registry<u64>, names: ActionNames) -> Tree {
        let source = CancelSource::default();
        snapshot(
            tree,
            registry,
            &window(),
            &TreeOptions::default(),
            names,
            &source.token(),
        )
        .unwrap_or_else(|error| panic!("{error}"))
    }

    #[test]
    fn the_tree_prints_one_line_per_kept_element() {
        let mut registry = Registry::default();
        assert_eq!(
            print(&mut tree(), &mut registry, ActionNames::Ax),
            Tree {
                text: [
                    "- window \"Notes\" [ref=e1] app=TextEdit (focused)",
                    "  - group [ref=e2]",
                    "    - button \"Save\" [ref=e3]",
                    "    - textarea [ref=e4]: \"line one\\nline \\\"two\\\"\" (focused)",
                    "  - checkbox \"Wrap\" [ref=e5] (disabled) (selected)",
                ]
                .join("\n"),
                nodes: 5,
                truncation: Truncation::Complete,
            }
        );
    }

    #[test]
    fn a_second_observation_keeps_the_refs() {
        let mut registry = Registry::default();
        let mut fake = tree();
        let first = print(&mut fake, &mut registry, ActionNames::Hidden);
        let second = print(&mut fake, &mut registry, ActionNames::Hidden);
        assert_eq!(first, second);
    }

    #[test]
    fn limits_truncate_the_tree() {
        let mut registry = Registry::default();
        let source = CancelSource::default();
        let options = TreeOptions {
            max_nodes: Some(3),
            ..TreeOptions::default()
        };
        let printed = snapshot(
            &mut tree(),
            &mut registry,
            &window(),
            &options,
            ActionNames::Hidden,
            &source.token(),
        )
        .unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(
            printed,
            Tree {
                text: [
                    "- window \"Notes\" [ref=e1] app=TextEdit (focused)",
                    "  - button \"Save\" [ref=e2]",
                    "… truncated (3 nodes)",
                ]
                .join("\n"),
                nodes: 2,
                truncation: Truncation::Truncated,
            }
        );
    }

    #[test]
    fn a_child_the_app_destroyed_mid_walk_is_skipped_and_counted() {
        let mut registry = Registry::default();
        let mut fake = tree();
        fake.gone.insert(2);
        assert_eq!(
            print(&mut fake, &mut registry, ActionNames::Hidden).text,
            [
                "- window \"Notes\" [ref=e1] app=TextEdit (focused)",
                "  - checkbox \"Wrap\" [ref=e2] (disabled) (selected)",
                "… skipped 1 unreadable nodes",
            ]
            .join("\n")
        );
    }

    #[test]
    fn lines_list_only_the_actions_a_role_does_not_imply() {
        let mut slider = props(Role::Slider, "Volume");
        slider.actions = [
            "AXIncrement",
            "AXDecrement",
            "AXIncrement",
            "AXScrollToVisible",
            "AXCustom\nline",
            "Name:Custom",
        ]
        .map(str::to_owned)
        .to_vec();
        let names: Vec<String> = shown_actions(&slider, ActionNames::Ax)
            .into_iter()
            .map(|action| action.name)
            .collect();
        assert_eq!(names, ["increment", "decrement"]);
        assert!(shown_actions(&slider, ActionNames::Hidden).is_empty());
    }

    #[test]
    fn long_values_are_cut_with_the_count_of_hidden_characters() {
        let mut line = String::new();
        write_quoted(&mut line, &"x".repeat(SHOWN_CHARS + 14_230))
            .unwrap_or_else(|error| panic!("{error}"));
        assert!(line.ends_with("\"… (+14,230 chars)"), "{line}");
        let mut label = String::new();
        write_quoted_label(&mut label, "a\u{1b}b").unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(label, "\"a\\u001bb\"");
    }

    #[test]
    fn find_matches_role_title_and_value() {
        let mut registry = Registry::default();
        let source = CancelSource::default();
        let found = query(
            &mut tree(),
            &mut registry,
            &window(),
            &FindQuery {
                role: Some("Check Box".to_owned()),
                ..FindQuery::default()
            },
            &source.token(),
        )
        .unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(
            found
                .iter()
                .map(|node| node.title.as_deref())
                .collect::<Vec<_>>(),
            [Some("Wrap")]
        );
    }
}
