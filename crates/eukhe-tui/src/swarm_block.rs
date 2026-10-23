//! The agent family in the inline transcript: the `you -> worker-1:` echo
//! of an `@name message` the user sent to another agent, the dim
//! `worker-1 -> worker-2:` rows of relayed peer messages, and the
//! `/agents` roster. All of it is client-side display only: never sent to
//! a model, never logged into the chat.
//!
//! The family is the current session's roster subtree (the same
//! descendants the activity dock counts). An agent is addressed the way
//! the daemon's agent messaging resolves it: its session name when that
//! is unique in the family, else one of its ids (active session id,
//! session id, rlm child id, roster agent id), else the
//! `parent/child` session-name path that tells duplicates apart.

use serde_json::Value;

use eukhe_types::daemon::agent_roster::{summary_admission, AgentRosterStatus, ModelAdmission};
use eukhe_types::daemon::AgentRelayEvent;

use crate::autocomplete::CompletionItem;
use crate::chat::Detail;
use crate::glyphs::{ARROW, ELLIPSIS, TREE_LAST, TREE_MID, TREE_PIPE, TREE_SPACE};
use crate::style::Style;
use crate::subagents::{
    descendant_entries_with_depth, entry_status, summary_identity_keys, summary_parent_keys,
    SessionIdentity,
};
use crate::theme::{Theme, ThemeColor};
use crate::width::{str_width, truncate_line, wrap_line};
use crate::{Line, Span};

/// One family transcript row.
#[derive(Debug, Clone, PartialEq)]
pub enum SwarmRow {
    /// The user's `@name message`, delivered to `to` instead of the main
    /// model.
    Sent { to: String, text: String },
    /// A message one non-root agent of the family sent another.
    Relay(AgentRelayEvent),
    /// The `/agents` answer: the family, in tree order.
    Roster(Vec<RosterLine>),
}

/// One `/agents` row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RosterLine {
    /// The tree connectors before the name (`|- `, `` `- ``, ...).
    pub tree: String,
    pub name: String,
    /// `running`, `idle`, `inactive`, `queued`, `done`, `failed`, or the
    /// supervisor's exceptional label.
    pub status: String,
    /// The model request's admission while one is out.
    pub admission: Option<ModelAdmission>,
    /// Depth below the session (1 = a direct child).
    pub depth: usize,
    pub model: String,
    /// What the agent has worked on (one line).
    pub note: Option<String>,
}

/// One family member: its roster entry, its depth below the session, and
/// its parent among the members (`None` for a direct child).
#[derive(Debug, Clone, Copy)]
pub(crate) struct FamilyMember<'a> {
    pub(crate) entry: &'a Value,
    pub(crate) depth: usize,
    pub(crate) parent: Option<usize>,
}

/// What an `@token` names in the family.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum AgentLookup<'a> {
    /// The one agent the token names.
    Found(&'a Value),
    /// Several agents share the name: the `parent/child` paths that tell
    /// them apart.
    Ambiguous(Vec<String>),
    /// No agent of the family.
    Unknown,
}

fn field<'a>(value: &'a Value, name: &str) -> Option<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .filter(|text| !text.is_empty())
}

/// The entry's session name (an agent's addressable name).
fn session_name(entry: &Value) -> Option<&str> {
    field(&entry["summary"], "sessionName")
}

/// The display name the relay rows use (the session name, else the
/// active session id, else the roster agent id).
#[must_use]
pub(crate) fn agent_name(entry: &Value) -> String {
    session_name(entry)
        .or_else(|| field(&entry["summary"], "activeSessionId"))
        .or_else(|| field(entry, "agentId"))
        .unwrap_or("agent")
        .to_string()
}

/// The family of `root`: every roster entry below it, each with its
/// parent among the members, in tree order (a parent before its
/// children, siblings in roster order).
#[must_use]
pub(crate) fn family_members<'a>(
    roster: &'a [Value],
    root: &SessionIdentity,
) -> Vec<FamilyMember<'a>> {
    let found = descendant_entries_with_depth(roster, root);
    let identities: Vec<Vec<String>> = found
        .iter()
        .map(|(entry, _)| summary_identity_keys(&entry["summary"]))
        .collect();
    let mut parents: Vec<Option<usize>> = found
        .iter()
        .enumerate()
        .map(|(index, (entry, depth))| {
            if *depth <= 1 {
                return None;
            }
            let keys = summary_parent_keys(&entry["summary"]);
            identities.iter().enumerate().position(|(other, identity)| {
                other != index && identity.iter().any(|key| keys.contains(key))
            })
        })
        .collect();
    // Depth-first from the direct children; a member whose parent is not
    // in the family (or that sits on a parent cycle) hangs off the
    // session.
    let mut ordered = Vec::with_capacity(found.len());
    let mut visited = vec![false; found.len()];
    for start in 0..found.len() {
        if visited[start] || parents[start].is_some_and(|_| has_root(&parents, start)) {
            continue;
        }
        parents[start] = None;
        let mut stack = vec![start];
        while let Some(index) = stack.pop() {
            if std::mem::replace(&mut visited[index], true) {
                continue;
            }
            ordered.push(index);
            stack.extend(
                (0..found.len())
                    .rev()
                    .filter(|child| parents[*child] == Some(index) && !visited[*child]),
            );
        }
    }
    let mut position = vec![0; found.len()];
    for (at, index) in ordered.iter().enumerate() {
        position[*index] = at;
    }
    ordered
        .iter()
        .map(|index| FamilyMember {
            entry: found[*index].0,
            depth: found[*index].1,
            parent: parents[*index].map(|parent| position[parent]),
        })
        .collect()
}

/// Whether following `index`'s parents ends at a member without one (no
/// cycle on the way).
fn has_root(parents: &[Option<usize>], index: usize) -> bool {
    let mut current = index;
    for _ in 0..parents.len() {
        match parents[current] {
            Some(parent) => current = parent,
            None => return true,
        }
    }
    false
}

/// The members `keep` selects, in the same tree order, each hung under
/// its nearest kept ancestor (the session when none is kept): a running
/// grandchild of an idle child still nests under the session's tree.
pub(crate) fn kept_members<'a>(
    members: &[FamilyMember<'a>],
    keep: impl Fn(&FamilyMember<'a>) -> bool,
) -> Vec<FamilyMember<'a>> {
    let kept: Vec<bool> = members.iter().map(&keep).collect();
    let mut moved_to: Vec<Option<usize>> = vec![None; members.len()];
    let mut out = Vec::new();
    for (index, member) in members.iter().enumerate() {
        if !kept[index] {
            continue;
        }
        let mut ancestor = member.parent;
        while let Some(at) = ancestor {
            if kept[at] {
                break;
            }
            ancestor = members[at].parent;
        }
        moved_to[index] = Some(out.len());
        out.push(FamilyMember {
            entry: member.entry,
            depth: member.depth,
            // Tree order puts every parent before its children.
            parent: ancestor.and_then(|at| moved_to[at]),
        });
    }
    out
}

/// The `parent/child` path of a member: its parent's display name (the
/// session's own name for a direct child) and its own.
fn member_path(members: &[FamilyMember<'_>], member: &FamilyMember<'_>, root_name: &str) -> String {
    let parent = member.parent.map_or_else(
        || root_name.to_string(),
        |parent| agent_name(members[parent].entry),
    );
    format!("{parent}/{}", agent_name(member.entry))
}

/// Resolve `token` (the text after `@`) to one family agent.
#[must_use]
pub(crate) fn resolve_agent<'a>(
    members: &[FamilyMember<'a>],
    root_name: &str,
    token: &str,
) -> AgentLookup<'a> {
    let named: Vec<&FamilyMember<'a>> = members
        .iter()
        .filter(|member| session_name(member.entry) == Some(token))
        .collect();
    if let [only] = named.as_slice() {
        return AgentLookup::Found(only.entry);
    }
    let by_id = members.iter().find(|member| {
        let summary = &member.entry["summary"];
        ["activeSessionId", "sessionId", "rlmChildId"]
            .iter()
            .any(|name| field(summary, name) == Some(token))
            || field(member.entry, "agentId") == Some(token)
    });
    if let Some(member) = by_id {
        return AgentLookup::Found(member.entry);
    }
    let by_path: Vec<&FamilyMember<'a>> = members
        .iter()
        .filter(|member| member_path(members, member, root_name) == token)
        .collect();
    if let [only] = by_path.as_slice() {
        return AgentLookup::Found(only.entry);
    }
    if named.is_empty() {
        AgentLookup::Unknown
    } else {
        AgentLookup::Ambiguous(
            named
                .iter()
                .map(|member| member_path(members, member, root_name))
                .collect(),
        )
    }
}

/// The status column: the supervisor's exceptional label, a queued child,
/// a finished task (`done`/`failed`), else the roster classification.
#[must_use]
pub(crate) fn status_label(entry: &Value) -> String {
    if let Some(label) = field(entry, "statusLabel") {
        return label.to_string();
    }
    if entry.get("queuedChild").and_then(Value::as_bool) == Some(true) {
        return "queued".to_string();
    }
    match (entry_status(entry), field(&entry["summary"], "taskState")) {
        (AgentRosterStatus::Running, _) => "running",
        (AgentRosterStatus::Idle | AgentRosterStatus::Inactive, Some("error")) => "failed",
        (AgentRosterStatus::Idle | AgentRosterStatus::Inactive, Some("completed")) => "done",
        (AgentRosterStatus::Idle, _) => "idle",
        (AgentRosterStatus::Inactive, _) => "inactive",
    }
    .to_string()
}

fn admission_word(admission: ModelAdmission) -> &'static str {
    match admission {
        ModelAdmission::Queued => "queued",
        ModelAdmission::Generating => "generating",
    }
}

/// The agent's one-line note (what it has worked on), if it has one.
fn note(entry: &Value) -> Option<String> {
    let text = field(&entry["summary"], "note")?;
    let line = text.split_whitespace().collect::<Vec<_>>().join(" ");
    (!line.is_empty()).then_some(line)
}

/// The `/agents` rows: the family in tree order with tree connectors.
#[must_use]
pub(crate) fn roster_lines(members: &[FamilyMember<'_>]) -> Vec<RosterLine> {
    members
        .iter()
        .enumerate()
        .map(|(index, member)| {
            // The connectors: one cell per ancestor (a pipe while that
            // ancestor has a later sibling), then this member's own.
            let is_last = |at: usize| {
                let parent = members[at].parent;
                !members[at + 1..].iter().any(|later| later.parent == parent)
            };
            let mut cells = vec![if is_last(index) { TREE_LAST } else { TREE_MID }];
            let mut ancestor = member.parent;
            while let Some(at) = ancestor {
                cells.push(if is_last(at) { TREE_SPACE } else { TREE_PIPE });
                ancestor = members[at].parent;
            }
            cells.reverse();
            RosterLine {
                tree: cells.concat(),
                name: agent_name(member.entry),
                status: status_label(member.entry),
                admission: summary_admission(&member.entry["summary"]),
                depth: member.depth,
                model: crate::agents_view_forest::session_model(&member.entry["summary"]),
                note: note(member.entry),
            }
        })
        .collect()
}

/// The `@` completions at prompt start: one per family agent, its handle
/// the name the resolver accepts (the `parent/child` path for a shared
/// name), its status as the description.
#[must_use]
pub(crate) fn mention_items(members: &[FamilyMember<'_>], root_name: &str) -> Vec<CompletionItem> {
    members
        .iter()
        .map(|member| {
            let name = agent_name(member.entry);
            let shared = members
                .iter()
                .filter(|other| agent_name(other.entry) == name)
                .count()
                > 1;
            let handle = if shared {
                member_path(members, member, root_name)
            } else {
                name
            };
            let status = status_label(member.entry);
            let description = match summary_admission(&member.entry["summary"]) {
                Some(admission) => format!("agent, {status}, {}", admission_word(admission)),
                None => format!("agent, {status}"),
            };
            CompletionItem {
                value: format!("@{handle}"),
                label: handle,
                description: Some(description),
                argument_hint: None,
                source_tag: None,
                path_row: None,
            }
        })
        .collect()
}

/// `spans` wrapped to `width` under a one-column indent, continuation
/// rows three columns deep.
fn wrapped(spans: &Line, width: usize) -> Vec<Line> {
    let content = width.saturating_sub(1).max(1);
    wrap_line(spans, content)
        .into_iter()
        .enumerate()
        .map(|(index, row)| {
            let mut out: Line = vec![Span::raw(if index == 0 { " " } else { "   " })];
            out.extend(row);
            out
        })
        .collect()
}

fn sent_rows(to: &str, text: &str, theme: &Theme, width: usize) -> Vec<Line> {
    let label = theme.fg_style(ThemeColor::Accent);
    let body = theme.fg_style(ThemeColor::UserMessageText);
    let mut out = Vec::new();
    for (index, paragraph) in text.split('\n').enumerate() {
        let mut line: Line = Vec::new();
        if index == 0 {
            line.push(Span::styled(format!("you {ARROW} {to}:"), label));
            line.push(Span::raw(" "));
        } else {
            line.push(Span::raw("  "));
        }
        line.push(Span::styled(paragraph.to_string(), body));
        out.extend(wrapped(&line, width));
    }
    out
}

fn relay_rows(relay: &AgentRelayEvent, detail: Detail, theme: &Theme, width: usize) -> Vec<Line> {
    let dim = theme.fg_style(ThemeColor::Dim);
    let head = format!("{} {ARROW} {}:", relay.from, relay.to);
    match detail {
        Detail::All => relay
            .text
            .split('\n')
            .enumerate()
            .flat_map(|(index, paragraph)| {
                let text = if index == 0 {
                    format!("{head} {paragraph}")
                } else {
                    format!("  {paragraph}")
                };
                wrapped(&vec![Span::styled(text, dim)], width)
            })
            .collect(),
        Detail::Overview | Detail::Details => {
            let mut lines = relay.text.lines().filter(|line| !line.trim().is_empty());
            let first = lines.next().unwrap_or_default().trim();
            let more = if lines.next().is_some() { ELLIPSIS } else { "" };
            let row: Line = vec![
                Span::raw(" "),
                Span::styled(format!("{head} {first}{more}"), dim),
            ];
            vec![truncate_line(&row, width, ELLIPSIS)]
        }
    }
}

fn status_style(theme: &Theme, status: &str) -> Style {
    theme.fg_style(match status {
        "running" => ThemeColor::Success,
        "failed" => ThemeColor::Error,
        "queued" | "recovering" => ThemeColor::Warning,
        _ => ThemeColor::Muted,
    })
}

fn roster_rows(lines: &[RosterLine], theme: &Theme, width: usize) -> Vec<Line> {
    let muted = theme.fg_style(ThemeColor::Muted);
    let dim = theme.fg_style(ThemeColor::Dim);
    let running = lines.iter().filter(|line| line.status == "running").count();
    let mut out = vec![vec![
        Span::raw(" "),
        Span::styled(
            format!("agents: {} ({running} running)", lines.len()),
            muted,
        ),
    ]];
    let status_text = |line: &RosterLine| match line.admission {
        Some(admission) => format!("{} ({})", line.status, admission_word(admission)),
        None => line.status.clone(),
    };
    let name_width = lines
        .iter()
        .map(|line| str_width(&line.tree) + str_width(&line.name))
        .max()
        .unwrap_or(0);
    let status_width = lines
        .iter()
        .map(|line| str_width(&status_text(line)))
        .max()
        .unwrap_or(0);
    let model_width = lines
        .iter()
        .map(|line| str_width(&line.model))
        .max()
        .unwrap_or(0);
    for line in lines {
        let status = status_text(line);
        let name_pad = name_width - str_width(&line.tree) - str_width(&line.name);
        let mut row: Line = vec![
            Span::raw(" "),
            Span::styled(line.tree.clone(), dim),
            Span::styled(line.name.clone(), theme.fg_style(ThemeColor::Accent)),
            Span::raw(" ".repeat(name_pad + 2)),
            Span::styled(
                format!("{status:<status_width$}"),
                status_style(theme, &line.status),
            ),
            Span::styled(
                format!("  depth {}  {:<model_width$}", line.depth, line.model),
                muted,
            ),
        ];
        if let Some(note) = &line.note {
            row.push(Span::styled(format!("  {note}"), dim));
        }
        out.push(truncate_line(&row, width, ELLIPSIS));
    }
    out
}

/// One family row: an optional leading blank, then the row's lines.
pub(crate) fn render_swarm_row(
    row: &SwarmRow,
    detail: Detail,
    theme: &Theme,
    width: usize,
    leading: bool,
) -> Vec<Line> {
    let mut out = Vec::new();
    if leading {
        out.push(Vec::new());
    }
    out.extend(match row {
        SwarmRow::Sent { to, text } => sent_rows(to, text, theme, width),
        SwarmRow::Relay(relay) => relay_rows(relay, detail, theme, width),
        SwarmRow::Roster(lines) => roster_rows(lines, theme, width),
    });
    out
}

#[cfg(test)]
mod tests;
