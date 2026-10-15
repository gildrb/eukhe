//! The `/memory` tree (`OptChat`): the chat memory as a navigable tree of
//! dated, labelled, expandable nodes, docked over the editor like the
//! read-only info panel. The view's lines are the top level, oldest
//! first; opening a line `id+n` shows its two halves one level down, and
//! opening a one-message line `id+1` shows the message whole. Each level
//! is fetched from the daemon (`get_memory_tree`) the first time it opens
//! and cached for the panel's life. Display only: nothing here reaches the
//! chat or a model.

use std::collections::{HashMap, HashSet};

use eukhe_types::daemon::{
    MemoryKindCount, MemoryStatusSnapshot, MemoryTree, MemoryTreeLevel, MemoryTreeMessage,
    MemoryTreeNode, MemoryZoom,
};

use crate::keybindings::KeybindingsManager;
use crate::memory_block::{memory_status_header, one_line, wrapped};
use crate::menu_panel::{fill_row, hint_row, key_hint, menu_list_layout, rule_row, scroll_row};
use crate::theme::{Theme, ThemeColor};
use crate::width::{spans_width, truncate_line};
use crate::{Line, Span};

/// The frame's rows outside the header and the content window: the rule,
/// the blank under the header, the key hint, and the trailing blank.
const FIXED_FRAME_ROWS: usize = 4;

/// The scroll indicator's row (shown when the window is partial).
const SCROLL_INDICATOR_ROWS: usize = 1;

/// The columns before a row's tree indent: the selection pointer and a
/// space.
const POINTER_COLUMNS: usize = 2;

/// One line of the tree, `id+n`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct NodeKey {
    id: u64,
    count: u64,
}

impl NodeKey {
    fn of(node: &MemoryTreeNode) -> Self {
        Self {
            id: node.id,
            count: node.count,
        }
    }
}

impl From<MemoryZoom> for NodeKey {
    fn from(zoom: MemoryZoom) -> Self {
        Self {
            id: zoom.id,
            count: zoom.count,
        }
    }
}

impl From<NodeKey> for MemoryZoom {
    fn from(key: NodeKey) -> Self {
        Self {
            id: key.id,
            count: key.count,
        }
    }
}

/// What one level of the tree holds on the client.
#[derive(Debug, Clone, PartialEq)]
enum Level {
    /// Asked, not answered yet.
    Loading,
    /// Summary lines, oldest first.
    Lines(Vec<MemoryTreeNode>),
    /// The one message under an `id+1` line.
    Message(MemoryTreeMessage),
    /// The daemon names no line there.
    NoLine,
    /// The session keeps no chat memory.
    NoMemory,
    /// The fetch failed; opening the line again asks again.
    Failed(String),
}

/// A selectable row group: a node's line (with its full summary while
/// selected) or a message under its `id+1` node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Item {
    Node(NodeKey),
    Message(NodeKey),
}

/// Where an item's rows sit in the last laid-out content.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ItemSpan {
    item: Item,
    first: usize,
    last: usize,
}

/// One flattened row group, in display order.
struct FlatRow<'a> {
    kind: RowKind<'a>,
    depth: usize,
    /// The node this row opens under; `None` at the top level.
    parent: Option<NodeKey>,
}

enum RowKind<'a> {
    Node(&'a MemoryTreeNode),
    Message(&'a MemoryTreeMessage),
    Loading,
    NoLine,
    NoMemory,
    Failed(&'a str),
}

impl FlatRow<'_> {
    fn item(&self) -> Option<Item> {
        match self.kind {
            RowKind::Node(node) => Some(Item::Node(NodeKey::of(node))),
            RowKind::Message(_) => self.parent.map(Item::Message),
            RowKind::Loading | RowKind::NoLine | RowKind::NoMemory | RowKind::Failed(_) => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Direction {
    Back,
    Forward,
}

/// How an open key treats a node that is already open.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OpenKey {
    /// Right: step into the first child.
    Descend,
    /// Enter: close it again.
    Toggle,
}

/// One fetched level: the line asked (`None` for the view) and the
/// daemon's answer (`Ok(None)`: the session keeps no chat memory).
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct MemoryTreeFetch {
    pub node: Option<MemoryZoom>,
    pub reply: Result<Option<MemoryTree>, String>,
}

/// The outcome of one key press on the tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryTreeAction {
    /// Consumed (navigation, or an inert key).
    None,
    /// Close the panel.
    Close,
    /// A line opened whose children are not cached: fetch them.
    Fetch(MemoryZoom),
}

/// The `/memory` tree panel's state.
#[derive(Debug, Clone, PartialEq)]
pub struct MemoryTreeView {
    /// The newest status a reply carried; `None` until the first lands.
    status: Option<MemoryStatusSnapshot>,
    /// Every fetched level, keyed by the line it opens (`None`: the view).
    levels: HashMap<Option<NodeKey>, Level>,
    /// The open lines.
    expanded: HashSet<NodeKey>,
    selected: Option<Item>,
    /// The content window's first row.
    scroll: usize,
    /// The content window's height from the last paint (a render always
    /// precedes a key press).
    visible_rows: usize,
    /// The item spans from the last paint.
    spans: Vec<ItemSpan>,
}

impl Default for MemoryTreeView {
    fn default() -> Self {
        Self::new()
    }
}

impl MemoryTreeView {
    /// A tree whose top level is being fetched.
    #[must_use]
    pub fn new() -> Self {
        Self {
            status: None,
            levels: HashMap::from([(None, Level::Loading)]),
            expanded: HashSet::new(),
            selected: None,
            scroll: 0,
            visible_rows: 0,
            spans: Vec::new(),
        }
    }

    /// Fold one fetched level in. The first top level selects the newest
    /// line (the bottom of the view).
    pub(crate) fn apply(&mut self, fetch: MemoryTreeFetch) {
        let level = match fetch.reply {
            Ok(None) => Level::NoMemory,
            Ok(Some(tree)) => {
                self.status = Some(tree.status);
                match tree.level {
                    MemoryTreeLevel::Lines { nodes } => Level::Lines(nodes),
                    MemoryTreeLevel::Message { message } => Level::Message(message),
                    MemoryTreeLevel::NoLine => Level::NoLine,
                }
            }
            Err(error) => Level::Failed(error),
        };
        self.levels.insert(fetch.node.map(NodeKey::from), level);
        if self.selected.is_none() {
            self.selected = self.flatten().iter().rev().find_map(FlatRow::item);
        }
    }

    /// Every row group in display order: each level's rows, an open
    /// line's level right under it.
    fn flatten(&self) -> Vec<FlatRow<'_>> {
        let mut out = Vec::new();
        self.walk(None, 0, &mut out);
        out
    }

    fn walk<'a>(&'a self, key: Option<NodeKey>, depth: usize, out: &mut Vec<FlatRow<'a>>) {
        let Some(level) = self.levels.get(&key) else {
            return;
        };
        let row = |kind| FlatRow {
            kind,
            depth,
            parent: key,
        };
        match level {
            Level::Loading => out.push(row(RowKind::Loading)),
            Level::Lines(nodes) => {
                for node in nodes {
                    out.push(row(RowKind::Node(node)));
                    let child = NodeKey::of(node);
                    if self.expanded.contains(&child) {
                        self.walk(Some(child), depth + 1, out);
                    }
                }
            }
            Level::Message(message) => out.push(row(RowKind::Message(message))),
            Level::NoLine => out.push(row(RowKind::NoLine)),
            Level::NoMemory => out.push(row(RowKind::NoMemory)),
            Level::Failed(error) => out.push(row(RowKind::Failed(error))),
        }
    }

    /// The selectable items in display order, each with the line it
    /// opens under.
    fn items(&self) -> Vec<(Item, Option<NodeKey>)> {
        self.flatten()
            .iter()
            .filter_map(|row| row.item().map(|item| (item, row.parent)))
            .collect()
    }

    fn selected_span(&self) -> Option<ItemSpan> {
        let selected = self.selected?;
        self.spans
            .iter()
            .copied()
            .find(|span| span.item == selected)
    }

    fn select(&mut self, item: Item) {
        self.selected = Some(item);
        self.reveal();
    }

    /// Keep the selected item in the window: a short one whole, a tall
    /// one (a long message or summary) filling the window.
    fn reveal(&mut self) {
        let Some(span) = self.selected_span() else {
            return;
        };
        let visible = self.visible_rows.max(1);
        if span.last + 1 - span.first <= visible {
            if span.first < self.scroll {
                self.scroll = span.first;
            } else if span.last >= self.scroll + visible {
                self.scroll = span.last + 1 - visible;
            }
        } else {
            self.scroll = self.scroll.clamp(span.first, span.last + 1 - visible);
        }
    }

    /// One step: a tall selected item scrolls through its own rows
    /// first; otherwise the selection moves to the neighbouring item.
    fn step(&mut self, direction: Direction) {
        let visible = self.visible_rows.max(1);
        if let Some(span) = self.selected_span() {
            if span.last + 1 - span.first > visible {
                match direction {
                    Direction::Forward if self.scroll + visible <= span.last => {
                        self.scroll += 1;
                        return;
                    }
                    Direction::Back if self.scroll > span.first => {
                        self.scroll -= 1;
                        return;
                    }
                    Direction::Forward | Direction::Back => {}
                }
            }
        }
        let items = self.items();
        let Some(index) = items
            .iter()
            .position(|(item, _)| Some(*item) == self.selected)
        else {
            if let Some((first, _)) = items.first() {
                self.select(*first);
            }
            return;
        };
        let next = match direction {
            Direction::Back => index.checked_sub(1),
            Direction::Forward => (index + 1 < items.len()).then_some(index + 1),
        };
        if let Some(next) = next {
            self.select(items[next].0);
        }
    }

    /// Right/Enter on a line: open it (fetching its level unless cached
    /// or already in flight). On an open line, Right steps into its first
    /// child and Enter closes it. A message opens nothing.
    fn open(&mut self, key: OpenKey) -> MemoryTreeAction {
        let Some(Item::Node(node)) = self.selected else {
            return MemoryTreeAction::None;
        };
        if self.expanded.contains(&node) {
            match key {
                OpenKey::Toggle => {
                    self.expanded.remove(&node);
                }
                OpenKey::Descend => {
                    let child = self
                        .items()
                        .into_iter()
                        .find(|(_, parent)| *parent == Some(node));
                    if let Some((child, _)) = child {
                        self.select(child);
                    }
                }
            }
            return MemoryTreeAction::None;
        }
        self.expanded.insert(node);
        match self.levels.get(&Some(node)) {
            Some(
                Level::Loading
                | Level::Lines(_)
                | Level::Message(_)
                | Level::NoLine
                | Level::NoMemory,
            ) => MemoryTreeAction::None,
            Some(Level::Failed(_)) | None => {
                self.levels.insert(Some(node), Level::Loading);
                MemoryTreeAction::Fetch(node.into())
            }
        }
    }

    /// Left: close the selected open line, else select its parent line.
    fn back(&mut self) {
        let Some(item) = self.selected else {
            return;
        };
        if let Item::Node(node) = item {
            if self.expanded.remove(&node) {
                return;
            }
        }
        let parent = self
            .items()
            .into_iter()
            .find(|(candidate, _)| *candidate == item)
            .and_then(|(_, parent)| parent);
        if let Some(parent) = parent {
            self.select(Item::Node(parent));
        }
    }

    /// One key press: the arrows and page keys move, Right/Enter open,
    /// Left closes or climbs, Esc/q/Ctrl+C close the panel; every other
    /// key is consumed.
    pub fn handle_key(&mut self, key: &str, kb: &KeybindingsManager) -> MemoryTreeAction {
        if key == "ctrl+c" || key == "q" || kb.matches(key, "tui.select.cancel") {
            return MemoryTreeAction::Close;
        }
        if kb.matches(key, "tui.select.up") {
            self.step(Direction::Back);
        } else if kb.matches(key, "tui.select.down") {
            self.step(Direction::Forward);
        } else if kb.matches(key, "tui.select.pageUp") || kb.matches(key, "tui.select.pageDown") {
            let direction = if kb.matches(key, "tui.select.pageDown") {
                Direction::Forward
            } else {
                Direction::Back
            };
            for _ in 0..self.visible_rows.max(1) {
                self.step(direction);
            }
        } else if kb.matches(key, "tui.select.top") {
            if let Some((first, _)) = self.items().first() {
                self.select(*first);
            }
            self.scroll = 0;
        } else if kb.matches(key, "tui.select.bottom") {
            if let Some((last, _)) = self.items().last() {
                self.select(*last);
            }
        } else if kb.matches(key, "app.memory.expand") {
            return self.open(OpenKey::Descend);
        } else if kb.matches(key, "tui.select.confirm") {
            return self.open(OpenKey::Toggle);
        } else if kb.matches(key, "app.modal.back") {
            self.back();
        }
        MemoryTreeAction::None
    }

    /// A node's line: the pointer, the tree indent and open marker,
    /// `id+n`, the date span, the kind tags and the summary's first line,
    /// cut to `width`; and whether the cut hid anything.
    fn node_row(
        &self,
        theme: &Theme,
        node: &MemoryTreeNode,
        depth: usize,
        width: usize,
    ) -> (Line, bool) {
        let key = NodeKey::of(node);
        let selected = self.selected == Some(Item::Node(key));
        let marker = if self.expanded.contains(&key) {
            crate::glyphs::EXPANDED
        } else {
            crate::glyphs::COLLAPSED
        };
        let mut row: Line = vec![
            Span::raw(self.pointer(Some(Item::Node(key)))),
            Span::raw("  ".repeat(depth)),
            theme.fg_span(ThemeColor::Muted, format!("{marker} ")),
            theme.fg_span(ThemeColor::Accent, format!("{}+{}", node.id, node.count)),
            Span::raw("  "),
            theme.fg_span(
                ThemeColor::Muted,
                date_span(&node.first_date, &node.last_date),
            ),
        ];
        let tags = kind_tags(&node.kinds);
        if !tags.is_empty() {
            row.push(Span::raw("  "));
            row.push(theme.fg_span(ThemeColor::Dim, tags));
        }
        row.push(Span::raw("  "));
        row.push(match &node.summary {
            Some(summary) => theme.fg_span(ThemeColor::Text, summary_line(summary)),
            None => theme.fg_span(ThemeColor::Dim, "(not summarized yet)"),
        });
        let clipped = spans_width(&row) > width;
        let row = truncate_line(&row, width, crate::glyphs::ELLIPSIS);
        (
            fill_row(&row, selected, width, theme.selection_row_style()),
            clipped,
        )
    }

    /// The content rows at `width` and where each item sits in them.
    fn layout(&self, theme: &Theme, width: usize) -> (Vec<Line>, Vec<ItemSpan>) {
        let mut lines: Vec<Line> = Vec::new();
        let mut spans = Vec::new();
        let text = theme.fg_style(ThemeColor::Text);
        let muted = theme.fg_style(ThemeColor::Muted);
        for row in self.flatten() {
            let first = lines.len();
            let indent = POINTER_COLUMNS + 2 * row.depth;
            match row.kind {
                RowKind::Node(node) => {
                    let (line, clipped) = self.node_row(theme, node, row.depth, width);
                    lines.push(line);
                    let item = Item::Node(NodeKey::of(node));
                    if self.selected == Some(item) {
                        if let Some(summary) = &node.summary {
                            if clipped || summary.lines().count() > 1 {
                                for line in summary.lines() {
                                    lines.extend(wrapped(&one_line(line), indent + 4, text, width));
                                }
                            }
                        }
                    }
                    spans.push(ItemSpan {
                        item,
                        first,
                        last: lines.len() - 1,
                    });
                }
                RowKind::Message(message) => {
                    let item = row.parent.map(Item::Message);
                    let selected = item.is_some() && self.selected == item;
                    let header: Line = vec![
                        Span::raw(self.pointer(item)),
                        Span::raw("  ".repeat(row.depth)),
                        theme.fg_span(ThemeColor::Accent, one_line(&message.kind)),
                        Span::raw("  "),
                        theme.fg_span(ThemeColor::Muted, message_date(&message.date)),
                    ];
                    let header = truncate_line(&header, width, crate::glyphs::ELLIPSIS);
                    lines.push(fill_row(
                        &header,
                        selected,
                        width,
                        theme.selection_row_style(),
                    ));
                    for line in message.text.lines() {
                        lines.extend(wrapped(&one_line(line), indent, text, width));
                    }
                    if let Some(item) = item {
                        spans.push(ItemSpan {
                            item,
                            first,
                            last: lines.len() - 1,
                        });
                    }
                }
                RowKind::Loading => {
                    lines.extend(wrapped(
                        &format!("loading{}", crate::glyphs::ELLIPSIS),
                        indent,
                        muted,
                        width,
                    ));
                }
                RowKind::NoLine => lines.extend(wrapped("(no line here)", indent, muted, width)),
                RowKind::NoMemory => lines.extend(wrapped(
                    "This session keeps no chat memory.",
                    indent,
                    muted,
                    width,
                )),
                RowKind::Failed(error) => lines.extend(wrapped(
                    &format!("{} {}", crate::glyphs::WARN, one_line(error)),
                    indent,
                    theme.fg_style(ThemeColor::Error),
                    width,
                )),
            }
        }
        (lines, spans)
    }

    /// Render the panel at the current row budget: the rule, the status
    /// header (and the compactor's unresolved failure), a blank, the
    /// content window, the scroll indicator when the window is partial,
    /// the key hint and one blank under it. Never taller than the budget.
    pub fn render(
        &mut self,
        theme: &Theme,
        width: usize,
        kb: &KeybindingsManager,
        viewport_rows: usize,
    ) -> Vec<Line> {
        let width = width.max(1);
        let (content, spans) = self.layout(theme, width);
        self.spans = spans;
        let muted = theme.fg_style(ThemeColor::Muted);
        let mut header = match &self.status {
            Some(status) => wrapped(&memory_status_header(status), 1, muted, width),
            None => wrapped(
                &format!("memory: loading{}", crate::glyphs::ELLIPSIS),
                1,
                muted,
                width,
            ),
        };
        if let Some(error) = self
            .status
            .as_ref()
            .and_then(|status| status.last_error.as_ref())
        {
            header.extend(wrapped(
                &format!(
                    "{} compactor error: {}",
                    crate::glyphs::WARN,
                    one_line(error)
                ),
                1,
                theme.fg_style(ThemeColor::Error),
                width,
            ));
        }
        let total = content.len();
        let visible = menu_list_layout(
            Some(viewport_rows),
            viewport_rows,
            total,
            FIXED_FRAME_ROWS + header.len(),
            SCROLL_INDICATOR_ROWS,
        );
        self.visible_rows = visible;
        self.reveal();
        self.scroll = self.scroll.min(total.saturating_sub(visible));
        let end = (self.scroll + visible).min(total);
        let mut lines: Vec<Line> =
            Vec::with_capacity(FIXED_FRAME_ROWS + header.len() + visible + 1);
        lines.push(rule_row(theme, width));
        lines.extend(header);
        lines.push(Vec::new());
        lines.extend(content[self.scroll..end].iter().cloned());
        if end < total || self.scroll > 0 {
            let position = self
                .selected
                .and_then(|selected| self.spans.iter().position(|span| span.item == selected))
                .map_or(0, |index| index + 1);
            lines.push(scroll_row(theme, width, position, self.spans.len()));
        }
        lines.push(hint_row(theme, width, &hint_text(kb)));
        lines.push(Vec::new());
        lines.truncate(viewport_rows.max(1));
        lines
    }

    /// The selection pointer cell in front of `item`'s first row.
    fn pointer(&self, item: Option<Item>) -> String {
        if item.is_some() && self.selected == item {
            format!("{} ", crate::glyphs::POINTER)
        } else {
            "  ".to_string()
        }
    }
}

/// `YYYY-MM-DD` and `HH:MM` of an RFC 3339 date in its own (local)
/// offset; `None` for anything else.
fn stamp(date: &str) -> Option<(&str, &str)> {
    let (day, rest) = date.split_once('T')?;
    let time = rest.get(..5)?;
    let well_formed = day.len() == 10
        && day.as_bytes()[4] == b'-'
        && day.as_bytes()[7] == b'-'
        && time.as_bytes()[2] == b':';
    well_formed.then_some((day, time))
}

/// A node's dates, compact: `2026-10-01 09:00` alone when both ends fall
/// in one minute, else ` -> ` and the end without what it shares with the
/// start: `09:30` the same day, `10-02 10:00` the same year, the full
/// date otherwise. Dates that do not parse show as sent.
pub(crate) fn date_span(first: &str, last: &str) -> String {
    let arrow = crate::glyphs::ARROW;
    let (Some((first_day, first_time)), Some((last_day, last_time))) = (stamp(first), stamp(last))
    else {
        return if first == last {
            one_line(first)
        } else {
            one_line(&format!("{first} {arrow} {last}"))
        };
    };
    let start = format!("{first_day} {first_time}");
    if (first_day, first_time) == (last_day, last_time) {
        start
    } else if first_day == last_day {
        format!("{start} {arrow} {last_time}")
    } else if first_day[..4] == last_day[..4] {
        format!("{start} {arrow} {} {last_time}", &last_day[5..])
    } else {
        format!("{start} {arrow} {last_day} {last_time}")
    }
}

/// A message's date, compact: `2026-10-03 08:00`.
fn message_date(date: &str) -> String {
    stamp(date).map_or_else(|| one_line(date), |(day, time)| format!("{day} {time}"))
}

/// The kinds under a node: `user 3, talk 2, tool 4`, in the daemon's
/// order (most frequent first).
pub(crate) fn kind_tags(kinds: &[MemoryKindCount]) -> String {
    kinds
        .iter()
        .map(|kind| format!("{} {}", one_line(&kind.kind), kind.count))
        .collect::<Vec<_>>()
        .join(", ")
}

/// A summary's first line, sanitized to one display line.
pub(crate) fn summary_line(summary: &str) -> String {
    one_line(summary.lines().next().unwrap_or_default())
}

/// The key hint: move, open, back, close -- each only while bound; the
/// close names Ctrl+C when the cancel binding is gone (always handled).
fn hint_text(kb: &KeybindingsManager) -> String {
    let close = kb.first_key("tui.select.cancel").map_or_else(
        || "Ctrl+C".to_string(),
        |key| crate::keybindings::format_key_text(&key),
    );
    [
        key_hint(kb, &["tui.select.up", "tui.select.down"], "move"),
        key_hint(kb, &["app.memory.expand", "tui.select.confirm"], "open"),
        key_hint(kb, &["app.modal.back"], "back"),
        Some(format!("{close} close")),
    ]
    .into_iter()
    .flatten()
    .collect::<Vec<_>>()
    .join(crate::glyphs::SEP)
}

#[cfg(test)]
mod tests;
