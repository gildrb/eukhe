//! Program status reports on the TUI's terminal: OSC 7501 (the Program
//! Status Protocol: <https://www.superlogical.com/rex/docs/build/program-status.md>)
//! for the session (the root record) and one child record per running
//! subagent, and OSC 9;4 progress for terminals that know only that.
//!
//! [`report`] encodes one report; [`Reporter`] remembers what the terminal
//! holds and returns the reports that move it to a new state, so a frame
//! that changes nothing writes nothing.

use std::borrow::Cow;
use std::collections::BTreeSet;

use base64::Engine;
use eukhe_types::daemon::agent_tree::TreeStatus;

use crate::activity::AgentActivity;
use crate::agents_panel::AgentRow;
use crate::chat::{ChatEntry, MessageBlock, StatusKind};
use crate::view::AgentView;

/// The `app` key of every record.
const APP: &str = "eukhe";
/// Bytes of a `msg`: one short line (the protocol allows 2048).
pub(crate) const MSG_MAX: usize = 160;
/// Bytes of a `title` (the protocol's decoded cap).
const TITLE_MAX: usize = 192;
/// Bytes of one id segment.
const SEGMENT_MAX: usize = 32;
/// Bytes of a whole id.
const ID_MAX: usize = 128;
/// Segments of an id.
const ID_DEPTH_MAX: usize = 8;
/// Child records at most: with the root, the 64 records every terminal
/// holds. A terminal past its own cap drops its least recent record, which
/// could be the root.
const CHILDREN_MAX: usize = 63;
const ELLIPSIS: char = '\u{2026}';

/// OSC 9;4 indeterminate progress.
const PROGRESS_BUSY: &str = "\x1b]9;4;3;0\x07";
/// OSC 9;4 progress removed.
const PROGRESS_CLEAR: &str = "\x1b]9;4;0;0\x07";

/// One line of text for a `msg` or `title`: no control characters, within
/// its byte cap, never empty.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Text<'a>(Cow<'a, str>);

impl<'a> Text<'a> {
    /// `raw` as one line of at most `max` bytes: control characters
    /// (newlines and tabs included) become spaces, whitespace runs one
    /// space, and a longer line ends in an ellipsis at a character
    /// boundary. `None` when nothing printable remains.
    pub(crate) fn line(raw: &'a str, max: usize) -> Option<Self> {
        let trimmed = raw.trim();
        if trimmed.is_empty() {
            return None;
        }
        if trimmed.len() <= max && !trimmed.chars().any(char::is_control) {
            return Some(Text(Cow::Borrowed(trimmed)));
        }
        let mut line = String::with_capacity(trimmed.len().min(max));
        for word in trimmed
            .split(|c: char| c.is_control() || c.is_whitespace())
            .filter(|word| !word.is_empty())
        {
            if !line.is_empty() {
                line.push(' ');
            }
            line.push_str(word);
            if line.len() > max {
                break;
            }
        }
        if line.is_empty() {
            return None;
        }
        if line.len() > max {
            let mut end = max - ELLIPSIS.len_utf8();
            while !line.is_char_boundary(end) {
                end -= 1;
            }
            line.truncate(end);
            line.truncate(line.trim_end().len());
            line.push(ELLIPSIS);
        }
        Some(Text(Cow::Owned(line)))
    }

    /// A fixed text (a literal that already is one clean line).
    const fn fixed(text: &'static str) -> Text<'static> {
        Text(Cow::Borrowed(text))
    }

    pub(crate) fn into_owned(self) -> Text<'static> {
        Text(Cow::Owned(self.0.into_owned()))
    }

    fn borrowed(&self) -> Text<'_> {
        Text(Cow::Borrowed(&self.0))
    }

    fn as_str(&self) -> &str {
        &self.0
    }
}

/// What a blocked record waits for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Kind {
    /// Approval to do something (a yes/no confirm).
    Permission,
    /// An answer the user types or picks.
    Question,
    /// A login or credential.
    Auth,
}

impl Kind {
    fn wire(self) -> &'static str {
        match self {
            Kind::Permission => "permission",
            Kind::Question => "question",
            Kind::Auth => "auth",
        }
    }
}

/// One record's state, each with its own fields.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum State<'a> {
    /// At the prompt, nothing to look at.
    Idle,
    /// A turn runs; `msg` names what it works on.
    Working { msg: Option<Text<'a>> },
    /// Waiting on the user.
    Blocked { kind: Kind, msg: Text<'a> },
    /// A turn finished and its answer is unread.
    Done { msg: Text<'a> },
    /// A turn failed and stopped.
    Error { msg: Text<'a> },
}

impl State<'_> {
    pub(crate) fn into_owned(self) -> State<'static> {
        match self {
            State::Idle => State::Idle,
            State::Working { msg } => State::Working {
                msg: msg.map(Text::into_owned),
            },
            State::Blocked { kind, msg } => State::Blocked {
                kind,
                msg: msg.into_owned(),
            },
            State::Done { msg } => State::Done {
                msg: msg.into_owned(),
            },
            State::Error { msg } => State::Error {
                msg: msg.into_owned(),
            },
        }
    }

    fn wire(&self) -> &'static str {
        match self {
            State::Idle => "idle",
            State::Working { .. } => "working",
            State::Blocked { .. } => "blocked",
            State::Done { .. } => "done",
            State::Error { .. } => "error",
        }
    }

    fn msg(&self) -> Option<&Text<'_>> {
        match self {
            State::Idle => None,
            State::Working { msg } => msg.as_ref(),
            State::Blocked { msg, .. } | State::Done { msg } | State::Error { msg } => Some(msg),
        }
    }

    fn kind(&self) -> Option<Kind> {
        match self {
            State::Blocked { kind, .. } => Some(*kind),
            State::Idle | State::Working { .. } | State::Done { .. } | State::Error { .. } => None,
        }
    }

    /// Whether the terminal drops the record when the process exits.
    fn lasts_past_exit(&self) -> bool {
        match self {
            State::Idle | State::Done { .. } | State::Error { .. } => true,
            State::Working { .. } | State::Blocked { .. } => false,
        }
    }
}

/// A record id: `/`-joined segments of `[A-Za-z0-9_.+-]{1,32}`, at most 8
/// deep and 128 bytes.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct RecordId(String);

impl RecordId {
    /// The id of `segments` (each already a [`segment`]); `None` past the
    /// depth or length cap.
    fn of_segments(segments: &[String]) -> Option<Self> {
        if segments.is_empty() || segments.len() > ID_DEPTH_MAX {
            return None;
        }
        let id = segments.join("/");
        (id.len() <= ID_MAX).then_some(RecordId(id))
    }

    /// This id or one beneath it: a clear of `parent` removes it.
    fn is_within(&self, parent: &RecordId) -> bool {
        self.0
            .strip_prefix(parent.0.as_str())
            .is_some_and(|rest| rest.is_empty() || rest.starts_with('/'))
    }
}

/// `name` as an id segment: characters outside the segment set become
/// `-`, cut at 32 bytes.
fn segment(name: &str) -> String {
    let segment: String = name
        .chars()
        .map(|c| match c {
            'A'..='Z' | 'a'..='z' | '0'..='9' | '_' | '.' | '+' | '-' => c,
            _ => '-',
        })
        .take(SEGMENT_MAX)
        .collect();
    if segment.is_empty() {
        "agent".to_owned()
    } else {
        segment
    }
}

/// One running subagent's record: always `working`, labelled by its name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ChildRecord {
    id: RecordId,
    title: Text<'static>,
}

/// One report.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Status<'r> {
    /// The session's own record.
    Root(&'r State<'r>),
    /// A running subagent's record.
    Child(&'r ChildRecord),
    /// Remove a record and every record beneath it.
    Clear(&'r RecordId),
    /// Remove every record.
    ClearAll,
}

/// The OSC 7501 sequence of `status`.
pub(crate) fn report(status: &Status<'_>) -> String {
    let mut out = String::from("\x1b]7501;state=");
    match status {
        Status::Root(state) => push_record(&mut out, state, None, None),
        Status::Child(child) => push_record(
            &mut out,
            &State::Working { msg: None },
            Some(&child.id),
            Some(&child.title),
        ),
        Status::Clear(id) => {
            out.push_str("clear:id=");
            out.push_str(&id.0);
        }
        Status::ClearAll => out.push_str("clear"),
    }
    out.push_str("\x1b\\");
    out
}

fn push_record(
    out: &mut String,
    state: &State<'_>,
    id: Option<&RecordId>,
    title: Option<&Text<'_>>,
) {
    out.push_str(state.wire());
    if let Some(kind) = state.kind() {
        out.push_str(":kind=");
        out.push_str(kind.wire());
    }
    if let Some(id) = id {
        out.push_str(":id=");
        out.push_str(&id.0);
    }
    out.push_str(":app=");
    out.push_str(APP);
    if let Some(title) = title {
        out.push_str(":title=");
        base64::engine::general_purpose::STANDARD.encode_string(title.as_str(), out);
    }
    if let Some(msg) = state.msg() {
        out.push_str(":msg=");
        base64::engine::general_purpose::STANDARD.encode_string(msg.as_str(), out);
    }
}

/// The `terminal.showTerminalProgress` setting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TerminalProgress {
    Shown,
    Off,
}

impl TerminalProgress {
    pub(crate) fn of_setting(shown: bool) -> Self {
        if shown {
            TerminalProgress::Shown
        } else {
            TerminalProgress::Off
        }
    }
}

/// What OSC 9;4 shows now.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum Progress {
    #[default]
    Cleared,
    Busy,
}

impl Progress {
    fn of(state: &State<'_>, setting: TerminalProgress) -> Self {
        match setting {
            TerminalProgress::Off => Progress::Cleared,
            TerminalProgress::Shown => match state {
                State::Working { .. } => Progress::Busy,
                State::Idle | State::Blocked { .. } | State::Done { .. } | State::Error { .. } => {
                    Progress::Cleared
                }
            },
        }
    }

    fn sequence(self) -> &'static str {
        match self {
            Progress::Cleared => PROGRESS_CLEAR,
            Progress::Busy => PROGRESS_BUSY,
        }
    }
}

/// The running subagents, when they changed since the last step.
#[derive(Debug)]
pub(crate) enum Family {
    Unchanged,
    Now(Vec<ChildRecord>),
}

/// How the surface leaves the terminal.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Leave<'a> {
    /// The process exits; `last_run` is how the latest run this process
    /// saw ended, if one did.
    Process { last_run: Option<&'a RunEnd> },
    /// Another surface takes the terminal and the process stays.
    Handoff,
}

/// What the terminal holds from this surface.
#[derive(Debug, Default)]
pub(crate) struct Reporter {
    root: Option<State<'static>>,
    children: Vec<ChildRecord>,
    progress: Progress,
}

impl Reporter {
    /// The reporter after the terminal moved to `root` and `family`, and
    /// the reports that move it there (empty when nothing changed).
    pub(crate) fn step(
        self,
        root: State<'_>,
        family: Family,
        setting: TerminalProgress,
    ) -> (Self, String) {
        let mut out = String::new();
        let children = match family {
            Family::Unchanged => self.children,
            Family::Now(children) => {
                let cleared: Vec<&RecordId> = self
                    .children
                    .iter()
                    .filter(|old| !children.iter().any(|new| new.id == old.id))
                    .map(|old| &old.id)
                    .collect();
                for id in &cleared {
                    out.push_str(&report(&Status::Clear(id)));
                }
                for child in &children {
                    // A clear above a record removed it too.
                    let stale = cleared.iter().any(|id| child.id.is_within(id))
                        || !self.children.contains(child);
                    if stale {
                        out.push_str(&report(&Status::Child(child)));
                    }
                }
                children
            }
        };
        let progress = Progress::of(&root, setting);
        let root = if self.root.as_ref() == Some(&root) {
            self.root
        } else {
            out.push_str(&report(&Status::Root(&root)));
            Some(root.into_owned())
        };
        if progress != self.progress {
            out.push_str(progress.sequence());
        }
        (
            Reporter {
                root,
                children,
                progress,
            },
            out,
        )
    }

    /// The reports that leave the terminal as `leave` needs: a process
    /// exit after work leaves how its latest run ended (the terminal drops
    /// `working` and `blocked` itself); a handoff removes every record.
    pub(crate) fn leave(self, leave: Leave<'_>) -> String {
        let mut out = String::new();
        match leave {
            Leave::Process { last_run } => {
                let settled = self.root.as_ref().is_none_or(State::lasts_past_exit);
                if let Some(last) = last_run.map(RunEnd::state) {
                    if settled && self.root.as_ref() != Some(&last) {
                        out.push_str(&report(&Status::Root(&last)));
                    }
                }
            }
            Leave::Handoff => out.push_str(&report(&Status::ClearAll)),
        }
        if self.progress == Progress::Busy {
            out.push_str(PROGRESS_CLEAR);
        }
        out
    }
}

/// How a run ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RunEnd {
    /// It answered; the answer's last line.
    Answered(Text<'static>),
    /// It failed and stopped; the failure.
    Failed(Text<'static>),
    /// The user stopped it.
    Interrupted,
}

impl RunEnd {
    /// The root state this end leaves while it is unread.
    pub(crate) fn state(&self) -> State<'_> {
        match self {
            RunEnd::Answered(msg) => State::Done {
                msg: msg.borrowed(),
            },
            RunEnd::Failed(msg) => State::Error {
                msg: msg.borrowed(),
            },
            RunEnd::Interrupted => State::Idle,
        }
    }
}

const TURN_FINISHED: Text<'static> = Text::fixed("Turn finished");
const TURN_FAILED: Text<'static> = Text::fixed("Turn failed");

/// How the run whose rows end `chat` ended: the newest row after the last
/// user message that tells it (an aborted reply, a failure, the answer's
/// last line).
pub(crate) fn run_end(chat: &[ChatEntry]) -> RunEnd {
    for entry in chat.iter().rev() {
        match entry {
            ChatEntry::User { .. } => break,
            ChatEntry::Assistant(message) if message.aborted => return RunEnd::Interrupted,
            ChatEntry::Assistant(message) => {
                if let Some(error) = &message.error {
                    return RunEnd::Failed(owned_line(error).unwrap_or(TURN_FAILED));
                }
                if let Some(line) = message.blocks.iter().rev().find_map(|block| match block {
                    MessageBlock::Text(text) => last_line(text),
                    MessageBlock::Thinking(_) => None,
                }) {
                    return RunEnd::Answered(line);
                }
            }
            ChatEntry::Status {
                text,
                kind: StatusKind::Error,
            } => return RunEnd::Failed(owned_line(text).unwrap_or(TURN_FAILED)),
            ChatEntry::Status { .. }
            | ChatEntry::SlashCommand { .. }
            | ChatEntry::CompactionSummary { .. }
            | ChatEntry::Tool(_)
            | ChatEntry::AgentMessage(_)
            | ChatEntry::SkillInvocation(_)
            | ChatEntry::InjectedPrompt(_)
            | ChatEntry::BashExecution(_)
            | ChatEntry::ShellCompletion(_)
            | ChatEntry::RefinementOutcome(_)
            | ChatEntry::CustomPanel(_)
            | ChatEntry::ChatView(_)
            | ChatEntry::Swarm(_)
            | ChatEntry::TurnFooter(_) => {}
        }
    }
    RunEnd::Answered(TURN_FINISHED)
}

fn owned_line(text: &str) -> Option<Text<'static>> {
    Text::line(text, MSG_MAX).map(Text::into_owned)
}

/// The last line of an answer with words in it (a code fence's closing
/// line has none).
fn last_line(text: &str) -> Option<Text<'static>> {
    text.lines()
        .rev()
        .map(str::trim)
        .find(|line| !line.is_empty() && !line.starts_with("```"))
        .and_then(owned_line)
}

/// The first line of `text`, for a `msg`.
pub(crate) fn first_line(text: &str) -> Option<Text<'_>> {
    text.lines()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .and_then(|line| Text::line(line, MSG_MAX))
}

/// What the open panel waits for from the user, if one does: the yes/no
/// confirm, a login, the branch-summary question of `/tree`.
pub(crate) fn blocked(view: &AgentView) -> Option<State<'_>> {
    let (kind, msg, fallback) = if let Some(confirm) = &view.confirm {
        (Kind::Permission, confirm.question(), "Confirm")
    } else if let Some(panel) = &view.auth_panel {
        (Kind::Auth, panel.title(), "Login")
    } else {
        let question = view.tree_selector.as_ref()?.question()?;
        (Kind::Question, question, question)
    };
    Some(State::Blocked {
        kind,
        msg: Text::line(msg, MSG_MAX).unwrap_or(Text(Cow::Borrowed(fallback))),
    })
}

/// The records of the running subagents of the pinned agents block's
/// trees: each node's id is the path of names from the session down to it,
/// unique among its siblings, and its title its name. At most
/// [`CHILDREN_MAX`], sorted by id.
pub(crate) fn child_records(agents: &[AgentRow]) -> Vec<ChildRecord> {
    let mut ancestors: Vec<String> = Vec::new();
    let mut taken: BTreeSet<RecordId> = BTreeSet::new();
    let mut records = Vec::new();
    for row in agents {
        ancestors.truncate(row.line.depth.saturating_sub(1));
        let own = unique_segment(&ancestors, &row.line.name, &taken);
        ancestors.push(own);
        let Some(id) = RecordId::of_segments(&ancestors) else {
            continue;
        };
        taken.insert(id.clone());
        if records.len() < CHILDREN_MAX && runs(row) {
            if let Some(title) = Text::line(&row.line.name, TITLE_MAX) {
                records.push(ChildRecord {
                    id,
                    title: title.into_owned(),
                });
            }
        }
    }
    records.sort_by(|a, b| a.id.cmp(&b.id));
    records
}

/// The node runs: listed as running and not a paused or idle worker.
fn runs(row: &AgentRow) -> bool {
    let active = match row.activity {
        AgentActivity::Idle => false,
        AgentActivity::Working { .. }
        | AgentActivity::Parked(_)
        | AgentActivity::Waiting(_)
        | AgentActivity::Background { .. } => true,
    };
    let running = match row.status {
        TreeStatus::Running => true,
        TreeStatus::Finished | TreeStatus::Failed | TreeStatus::Cancelled => false,
    };
    running && active
}

/// `name`'s segment below `ancestors`, suffixed `+2`, `+3`, ... when a
/// sibling already holds it.
fn unique_segment(ancestors: &[String], name: &str, taken: &BTreeSet<RecordId>) -> String {
    let base = segment(name);
    let free = |candidate: &str| {
        let mut path = ancestors.to_vec();
        path.push(candidate.to_owned());
        RecordId::of_segments(&path).is_none_or(|id| !taken.contains(&id))
    };
    if free(&base) {
        return base;
    }
    let mut n: usize = 2;
    loop {
        let suffix = format!("+{n}");
        let mut candidate = base.clone();
        candidate.truncate(SEGMENT_MAX - suffix.len());
        candidate.push_str(&suffix);
        if free(&candidate) {
            return candidate;
        }
        n += 1;
    }
}

#[cfg(test)]
mod tests;
