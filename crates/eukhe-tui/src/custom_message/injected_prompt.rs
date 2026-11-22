//! Injected-prompt rows (TS `InjectedPromptMessageComponent`): the kind's
//! header line, plus the guttered markdown body in the expanded view.
//! Decode maps each custom type to its kind (TS `isInjectedPromptMessage`);
//! the render ports each header shape and the expand contract.
//!
//! The RLM child status notices left this class (the operator's 2026-10-01
//! directive: "the factory child status notices should be like subagent
//! messages not user messages" -- a spawned child's exit status is
//! child-originated mail, so those rows render in the `agent_message`
//! class now, superseding the 2026-09-23 diamond-row divergence): the
//! kinds here are the engine-injected turn prompts only -- the heartbeat
//! prompt, the goal context, the kernel-state restore, the
//! skills-unavailable report, and the engine continuations.
//!
//! The engine continuations (the Director's reminders, autonomous
//! continuations, the quota and compaction resumes) arrive as hidden
//! custom messages; each shows as one dim `[<label>] <first line>` row at
//! the step column, the whole body at `all`. Goal prompts and engine
//! bookkeeping (`harness_digest`, refine results) stay hidden.
//!
//! Second divergence (operator directive 2026-09-23): the heartbeat prompt
//! row renders the `o` clock glyph -- the unified activity dock's
//! Heartbeats group icon (`chrome.rs::render_activity_dock`) -- where the
//! TS binary still renders a heart. The TS side is expected to
//! adopt the same glyph.

use super::custom_content_text;
use super::render::{spacer, text_rows, truncate_text};
use crate::chat::Detail;
use crate::rows::Gutter;
use crate::theme::{Theme, ThemeColor};
use crate::width::{str_width, truncate_to_width, wrap_text};
use crate::{Line, Span};
use eukhe_types::ai::UserContent;
use eukhe_types::custom_type::CustomType;
use eukhe_types::input_origin::{AutonomousNudge, InputOrigin};
use serde_json::Value;

/// One injected prompt row (TS `InjectedPromptMessageComponent`); the kind
/// picks the header shape, `body` renders as markdown when expanded.
#[derive(Debug, Clone, PartialEq)]
pub struct InjectedPromptRow {
    pub kind: InjectedPromptKind,
    /// Markdown body (`None` renders nothing extra when expanded).
    pub body: Option<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum InjectedPromptKind {
    /// `o Heartbeat prompt * <schedule>` (error pulse, muted label; the
    /// clock glyph is the dock's Heartbeats icon -- the operator-directed
    /// divergence in the module docs).
    Heartbeat { schedule: Option<String> },
    /// `<goal label>[ * <objective preview>]` (muted; TS `goalLabel`/`metaText`).
    Goal {
        kind: Option<String>,
        objective: Option<String>,
    },
    /// `* Restored Python kernel state` / `* Started fresh Python kernel`.
    KernelRestored { restored: bool },
    /// `Python skills unavailable * <skill names>` (muted label, dim
    /// names; TS PR #2381's header -- no marker glyph), expandable to the
    /// full report.
    PythonSkillsUnavailable { skills: Vec<String> },
    /// `[<label>] <first body line>` (dim): an engine continuation the
    /// model read as user input.
    Continuation { origin: ContinuationOrigin },
}

/// The engine continuations a transcript shows: the allow-list over
/// `InputOrigin::hidden_custom_type`. Goal prompts and every other hidden
/// type stay out of the transcript.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContinuationOrigin {
    /// A Director layer's continuation (`[reminder]`).
    Director,
    /// An autonomous-mode continuation (`[auto]`).
    Autonomous,
    /// The marker that resumes a session the provider quota parked
    /// (`[resume]`).
    QuotaResume,
    /// The prompt that resumes a turn a compaction interrupted
    /// (`[compaction]`).
    CompactionResume,
}

impl ContinuationOrigin {
    /// The continuation whose hidden custom type is `custom_type`; `None`
    /// for every type off the allow-list.
    fn of(custom_type: &CustomType) -> Option<Self> {
        [
            (InputOrigin::Director, Self::Director),
            (
                InputOrigin::Autonomous {
                    nudge: AutonomousNudge::Continuation,
                },
                Self::Autonomous,
            ),
            (InputOrigin::QuotaResume, Self::QuotaResume),
            (InputOrigin::CompactionResume, Self::CompactionResume),
        ]
        .into_iter()
        .find_map(|(input, origin)| {
            (input.hidden_custom_type() == Some(custom_type.as_str())).then_some(origin)
        })
    }

    /// The row's bracketed label.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Director => "[reminder]",
            Self::Autonomous => "[auto]",
            Self::QuotaResume => "[resume]",
            Self::CompactionResume => "[compaction]",
        }
    }
}

/// The row of an engine continuation (a hidden custom message on the
/// allow-list), its body the content without an enclosing `<tag>`
/// wrapper (`<system-reminder>`, `<provider_quota_resumed>`); `None` for
/// every other custom type.
pub(crate) fn continuation_row(
    custom_type: &CustomType,
    content: &UserContent,
) -> Option<InjectedPromptRow> {
    let origin = ContinuationOrigin::of(custom_type)?;
    let text = custom_content_text(content);
    Some(InjectedPromptRow {
        kind: InjectedPromptKind::Continuation { origin },
        body: Some(unwrapped(&text).to_string()),
    })
}

/// `text` trimmed, without one `<tag>...</tag>` pair around all of it.
fn unwrapped(text: &str) -> &str {
    let trimmed = text.trim();
    trimmed
        .strip_prefix('<')
        .and_then(|rest| rest.split_once('>'))
        .filter(|(tag, _)| {
            !tag.is_empty()
                && tag
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
        })
        .and_then(|(tag, inner)| inner.strip_suffix(&format!("</{tag}>")))
        .map_or(trimmed, str::trim)
}

/// A line that is only a bracketed header (`[autonomous-continuation]`):
/// the row's label already names it.
fn is_header_line(line: &str) -> bool {
    let line = line.trim();
    line.starts_with('[') && line.ends_with(']')
}

/// One injected-prompt row (TS `isInjectedPromptMessage` kinds); `None`
/// for every other custom type.
pub(crate) fn injected_prompt_row(
    custom_type: &CustomType,
    content: &UserContent,
    details: &Value,
) -> Option<InjectedPromptRow> {
    let kind = match custom_type {
        CustomType::HeartbeatPrompt => InjectedPromptKind::Heartbeat {
            schedule: details
                .get("schedule")
                .and_then(Value::as_str)
                .map(str::to_string),
        },
        CustomType::GoalContext => InjectedPromptKind::Goal {
            kind: details
                .get("kind")
                .and_then(Value::as_str)
                .map(str::to_string),
            objective: details
                .get("objective")
                .and_then(Value::as_str)
                .map(str::to_string),
        },
        CustomType::IpythonStateRestored => InjectedPromptKind::KernelRestored {
            restored: details.get("restored").and_then(Value::as_bool) != Some(false),
        },
        CustomType::PythonSkillsUnavailable => InjectedPromptKind::PythonSkillsUnavailable {
            skills: details
                .get("skills")
                .and_then(Value::as_array)
                .map(|names| {
                    names
                        .iter()
                        .filter_map(Value::as_str)
                        .map(str::to_string)
                        .collect()
                })
                .unwrap_or_default(),
        },
        CustomType::AgentMessage
        | CustomType::AgentReply
        | CustomType::RlmChildFailure
        | CustomType::RlmChildTerminalNotice
        | CustomType::AsyncBashCompletion
        | CustomType::CompactionOutcome
        | CustomType::RefinementOutcome
        | CustomType::ProviderRetryOutcome
        | CustomType::ModelPromptError
        | CustomType::KernelUnavailable
        | CustomType::SessionSlashCommand
        | CustomType::SessionSlashCommandResult
        | CustomType::WorkerRestartNotice
        | CustomType::OutputLimitNotice
        | CustomType::SpawnFailedNotice
        | CustomType::Other(_) => return None,
    };
    let body = match &kind {
        // The kernel-state row stays header-only (TS keeps
        // `ipython_state_restored` header-only).
        InjectedPromptKind::KernelRestored { .. } => None,
        InjectedPromptKind::Heartbeat { .. }
        | InjectedPromptKind::Goal { .. }
        | InjectedPromptKind::PythonSkillsUnavailable { .. }
        | InjectedPromptKind::Continuation { .. } => Some(custom_content_text(content)),
    };
    Some(InjectedPromptRow { kind, body })
}

/// One injected-prompt row (TS `InjectedPromptMessageComponent`): a leading
/// blank unless `leading` is false (the row joins the injected row above
/// it), the kind's header, then the guttered markdown body below it when
/// expanded (the kernel-state row stays header-only in both states). A
/// continuation renders its dim gutter rows instead.
pub(crate) fn render_injected_prompt(
    row: &InjectedPromptRow,
    detail: Detail,
    theme: &Theme,
    width: usize,
    leading: bool,
) -> Vec<Line> {
    let mut out = if leading { vec![spacer()] } else { Vec::new() };
    let header = prompt_header(row, theme);
    if let InjectedPromptKind::Continuation { .. } = row.kind {
        out.extend(continuation_rows(
            &header,
            row.body.as_deref().unwrap_or_default(),
            detail,
            theme,
            width,
        ));
        return out;
    }
    out.extend(text_rows(&header, width));
    if let Some(body) = expanded_prompt_body(row, detail) {
        out.extend(crate::branch::branch_markdown(
            body,
            &super::render::markdown_style(ThemeColor::CustomMessageText, theme),
            theme,
            width,
        ));
    }
    out
}

/// A continuation's rows on the step gutter, in the label's style: the
/// label as the step mark, then the body's first line past its bracketed
/// headers, cut to the width (`...` when more lines follow); at `all`
/// every body line, wrapped rows hanging at the step's body column.
fn continuation_rows(
    label: &Line,
    body: &str,
    detail: Detail,
    theme: &Theme,
    width: usize,
) -> Vec<Line> {
    let Some(label) = label.first() else {
        return Vec::new();
    };
    let lead_width = Gutter::Step.mark_col() + str_width(&label.content) + 1;
    let first_width = width.saturating_sub(lead_width + 1).max(1);
    let hang_width = Gutter::Step.body_width(width);
    let lines: Vec<&str> = body
        .lines()
        .map(str::trim_end)
        .filter(|line| !line.trim().is_empty())
        .collect();
    let text: Vec<String> = if detail.tool_output_expanded() {
        let plain = |line: Line| line.into_iter().map(|span| span.content).collect();
        lines
            .iter()
            .enumerate()
            .flat_map(|(index, line)| {
                wrap_text(line, if index == 0 { first_width } else { hang_width })
            })
            .map(plain)
            .collect()
    } else {
        let shown = lines
            .iter()
            .position(|line| !is_header_line(line))
            .unwrap_or_default();
        let first = lines.get(shown).copied().unwrap_or_default();
        let row = if shown + 1 < lines.len() {
            format!("{first} {}", crate::glyphs::ELLIPSIS)
        } else {
            first.to_string()
        };
        vec![truncate_to_width(
            &row,
            first_width,
            crate::glyphs::ELLIPSIS,
        )]
    };
    let mut rows: Vec<Line> = text
        .into_iter()
        .map(|row| vec![Span::styled(row, label.style)])
        .collect();
    if rows.is_empty() {
        rows.push(Vec::new());
    }
    Gutter::Step.place(Some(label.clone()), rows, theme, width)
}

fn prompt_header(row: &InjectedPromptRow, theme: &Theme) -> Line {
    let muted = theme.fg_style(ThemeColor::Muted);
    let dim = theme.fg_style(ThemeColor::Dim);
    let accent = theme.fg_style(ThemeColor::Accent);
    // TS `InjectedPromptMessageComponent.updateDisplay`: the header always
    // renders; the expanded form adds the markdown body below it (the
    // kernel-state row stays header-only).
    let header: Line = match &row.kind {
        InjectedPromptKind::Heartbeat { schedule } => vec![
            // The o clock (the dock's Heartbeats icon), not the TS heart:
            // the operator-directed divergence in the module docs.
            Span::styled(
                crate::glyphs::HEARTBEAT.to_string(),
                theme.fg_style(ThemeColor::Error),
            ),
            Span::raw(" "),
            Span::styled("Heartbeat prompt".to_string(), muted),
            Span::styled(crate::glyphs::SEP.to_string(), dim),
            Span::styled(heartbeat_schedule(schedule.as_deref()), muted),
        ],
        InjectedPromptKind::Goal { kind, objective } => {
            let mut spans: Line = vec![Span::styled(goal_label(kind.as_deref()), muted)];
            if let Some(objective) = objective {
                spans.push(Span::styled(goal_meta(objective), muted));
            }
            spans
        }
        InjectedPromptKind::KernelRestored { restored } => vec![
            Span::styled(crate::glyphs::NOTICE.to_string(), accent),
            Span::raw(" "),
            Span::styled(
                if *restored {
                    "Restored Python kernel state"
                } else {
                    "Started fresh Python kernel"
                }
                .to_string(),
                muted,
            ),
        ],
        InjectedPromptKind::PythonSkillsUnavailable { skills } => {
            let mut spans = vec![Span::styled("Python skills unavailable".to_string(), muted)];
            if !skills.is_empty() {
                // TS `truncateToWidth(skills.join(", "),
                // max(20, 90 - "Python skills unavailable * ".length))` = 62.
                spans.push(Span::styled(
                    format!(
                        " - {}",
                        truncate_text(&skills.join(", "), 62, crate::glyphs::ELLIPSIS)
                    ),
                    dim,
                ));
            }
            spans
        }
        InjectedPromptKind::Continuation { origin } => {
            vec![Span::styled(origin.label().to_string(), dim)]
        }
    };
    header
}

fn expanded_prompt_body(row: &InjectedPromptRow, detail: Detail) -> Option<&str> {
    row.body
        .as_deref()
        .filter(|_| detail.tool_output_expanded())
}

/// TS `heartbeatPromptSchedule` over `compactHeartbeatSchedule`: a blank
/// schedule shows as `scheduled` (the `prompt` compact form), every other
/// expression as `every <expression>` (a leading case-insensitive `every`
/// plus whitespace stripped from the stored expression first).
fn heartbeat_schedule(schedule: Option<&str>) -> String {
    let trimmed = schedule.map_or("", str::trim);
    let compact = if trimmed.is_empty() {
        "prompt"
    } else if trimmed.get(..5).is_some_and(|prefix| {
        prefix.eq_ignore_ascii_case("every")
            && trimmed[5..].chars().next().is_some_and(char::is_whitespace)
    }) {
        trimmed[5..].trim_start()
    } else {
        trimmed
    };
    if compact == "prompt" {
        "scheduled".to_string()
    } else {
        format!("every {compact}")
    }
}

/// TS `goalLabel`.
fn goal_label(kind: Option<&str>) -> String {
    match kind {
        Some("continuation") => "Goal continuation",
        Some("budget_limit") => "Goal budget limit",
        Some("objective_updated") => "Goal updated",
        _ => "Goal context",
    }
    .to_string()
}

/// TS `metaText`: ` - <collapsed objective>` truncated to the TS budget
/// (`max(20, 90 - width("Goal continuation - "))` = 70) with the default
/// `...` ellipsis.
fn goal_meta(objective: &str) -> String {
    let collapsed: String = objective.split_whitespace().collect::<Vec<_>>().join(" ");
    format!(
        " - {}",
        truncate_text(&collapsed, 70, crate::glyphs::ELLIPSIS)
    )
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::chat::Detail;
    use crate::theme::{ColorMode, Theme};
    use crate::width::str_width;
    use crate::Span;

    fn theme() -> Theme {
        Theme::builtin("forge", ColorMode::TrueColor)
    }

    fn flat(row: &Line) -> String {
        row.iter().map(|s| s.content.as_str()).collect()
    }

    #[test]
    fn heartbeat_header_and_schedule_forms() {
        assert_eq!(heartbeat_schedule(Some("every 10m")), "every 10m");
        assert_eq!(heartbeat_schedule(Some("10m")), "every 10m");
        // TS `/^every\s+/i`: case-insensitive with any whitespace run;
        // `every` without whitespace stays part of the expression.
        assert_eq!(heartbeat_schedule(Some("EVERY  10m")), "every 10m");
        assert_eq!(heartbeat_schedule(Some("every10m")), "every every10m");
        assert_eq!(heartbeat_schedule(Some("prompt")), "scheduled");
        assert_eq!(heartbeat_schedule(Some("  ")), "scheduled");
        assert_eq!(heartbeat_schedule(None), "scheduled");
        let row = InjectedPromptRow {
            kind: InjectedPromptKind::Heartbeat {
                schedule: Some("every 10m".to_string()),
            },
            body: Some("nudge".to_string()),
        };
        let rows = render_injected_prompt(&row, Detail::Overview, &theme(), 60, true);
        assert_eq!(rows.len(), 2, "{rows:?}");
        assert!(rows[0].is_empty());
        assert_eq!(flat(&rows[1]).trim_end(), " @ Heartbeat prompt - every 10m");
        assert_eq!(
            rows[1][1],
            Span::styled("@".to_string(), theme().fg_style(ThemeColor::Error))
        );
    }

    #[test]
    fn goal_header_label_and_meta() {
        let row = InjectedPromptRow {
            kind: InjectedPromptKind::Goal {
                kind: Some("continuation".to_string()),
                objective: Some("ship it today".to_string()),
            },
            body: Some("continue".to_string()),
        };
        let rows = render_injected_prompt(&row, Detail::Overview, &theme(), 60, true);
        assert_eq!(
            flat(&rows[1]).trim_end(),
            " Goal continuation - ship it today"
        );
        // Budget-limit and objective-update kinds carry their own labels.
        for (kind, label) in [
            ("budget_limit", "Goal budget limit"),
            ("objective_updated", "Goal updated"),
            ("other", "Goal context"),
        ] {
            let row = InjectedPromptRow {
                kind: InjectedPromptKind::Goal {
                    kind: Some(kind.to_string()),
                    objective: None,
                },
                body: None,
            };
            let rows = render_injected_prompt(&row, Detail::Overview, &theme(), 60, true);
            assert_eq!(flat(&rows[1]).trim_end(), format!(" {label}"));
        }
        // A long objective truncates to the TS budget with the default
        // `...` ellipsis, after whitespace collapsing. TS `metaText`
        // truncates only the objective (70 columns); the rendered row
        // adds the 1-column inset plus the 20-column
        // `Goal continuation - ` prefix for a 91-wide line.
        let objective = format!("{} tail", "word ".repeat(15));
        let row = InjectedPromptRow {
            kind: InjectedPromptKind::Goal {
                kind: Some("continuation".to_string()),
                objective: Some(objective),
            },
            body: None,
        };
        let rows = render_injected_prompt(&row, Detail::Overview, &theme(), 120, true);
        let rendered = flat(&rows[1]);
        let meta = rendered.trim_end();
        assert!(meta.ends_with("..."), "ellipsized meta: {meta:?}");
        let visible: String = meta.trim_end_matches('.').to_string();
        let preview = visible.trim_end();
        assert_eq!(str_width(preview) + 3, 91, "meta {meta:?}");
        // The truncated objective alone stays within the TS budget.
        let prefix = " Goal continuation - ";
        assert_eq!(
            str_width(preview.trim_start_matches(prefix)) + 3,
            70,
            "objective {meta:?}"
        );
    }

    #[test]
    fn python_skills_unavailable_header_shapes() {
        // Collapsed: muted label + dim names (the TS header has no marker
        // glyph); no body.
        let row = InjectedPromptRow {
            kind: InjectedPromptKind::PythonSkillsUnavailable {
                skills: vec!["lookup".to_string(), "edit".to_string()],
            },
            body: Some("[python-skills-unavailable]\n\n...".to_string()),
        };
        let rows = render_injected_prompt(&row, Detail::Overview, &theme(), 80, true);
        assert_eq!(rows.len(), 2, "{rows:?}");
        assert_eq!(
            flat(&rows[1]).trim_end(),
            " Python skills unavailable - lookup, edit"
        );
        assert_eq!(rows[1][1].style, theme().fg_style(ThemeColor::Muted));
        assert_eq!(rows[1][2].style, theme().fg_style(ThemeColor::Dim));
        // Expanded: no hint, the full report renders as the body.
        let rows = render_injected_prompt(&row, Detail::All, &theme(), 80, true);
        assert!(rows.len() > 2, "body renders expanded: {rows:?}");
        assert_eq!(
            flat(&rows[1]).trim_end(),
            " Python skills unavailable - lookup, edit"
        );
        // The names truncate to the TS budget (62 columns, `...`).
        let long: Vec<String> = (0..12).map(|i| format!("skill-{i}")).collect();
        let row = InjectedPromptRow {
            kind: InjectedPromptKind::PythonSkillsUnavailable { skills: long },
            body: None,
        };
        let rows = render_injected_prompt(&row, Detail::Overview, &theme(), 120, true);
        let row_text = flat(&rows[1]);
        let meta = row_text.trim_end();
        let names = meta.trim_start_matches(" Python skills unavailable - ");
        assert_eq!(str_width(names), 62, "names width: {names}");
        assert!(names.ends_with("..."), "ellipsized names: {names}");
        // No skills details: the label alone.
        let row = InjectedPromptRow {
            kind: InjectedPromptKind::PythonSkillsUnavailable { skills: Vec::new() },
            body: None,
        };
        let rows = render_injected_prompt(&row, Detail::Overview, &theme(), 80, true);
        assert_eq!(flat(&rows[1]).trim_end(), " Python skills unavailable");
    }

    #[test]
    fn kernel_state_labels() {
        for (restored, label) in [
            (true, "Restored Python kernel state"),
            (false, "Started fresh Python kernel"),
        ] {
            let row = InjectedPromptRow {
                kind: InjectedPromptKind::KernelRestored { restored },
                body: None,
            };
            let rows = render_injected_prompt(&row, Detail::All, &theme(), 60, true);
            // Header only, no body even expanded.
            assert_eq!(rows.len(), 2, "{rows:?}");
            assert_eq!(flat(&rows[1]).trim_end(), format!(" * {label}"));
        }
    }

    fn continuation(custom_type: &str, content: &str) -> InjectedPromptRow {
        continuation_row(
            &CustomType::parse(custom_type),
            &UserContent::Text(content.to_string()),
        )
        .expect("a continuation on the allow-list")
    }

    fn texts(rows: &[Line]) -> Vec<String> {
        rows.iter()
            .map(|row| flat(row).trim_end().to_string())
            .collect()
    }

    /// Every engine continuation shows as one dim row at the step column:
    /// its label, then the body.
    #[test]
    fn continuations_render_one_dim_labelled_row() {
        for (custom_type, label) in [
            ("director_continuation", "[reminder]"),
            ("autonomous_continuation", "[auto]"),
            ("quota_resume", "[resume]"),
            ("compaction_resume", "[compaction]"),
        ] {
            let row = continuation(custom_type, "Run the tests before you answer.");
            for detail in [Detail::Overview, Detail::Details, Detail::All] {
                let rows = render_injected_prompt(&row, detail, &theme(), 100, true);
                assert_eq!(
                    texts(&rows),
                    vec![
                        String::new(),
                        format!("   {label} Run the tests before you answer.")
                    ],
                    "{custom_type} at {detail:?}"
                );
                assert_eq!(rows[1][1].style, theme().fg_style(ThemeColor::Dim));
            }
        }
    }

    /// The default levels show the body's first line (`...` when more
    /// follows, cut at the width); `all` shows the whole body. A
    /// `<system-reminder>` wrapper never shows.
    #[test]
    fn a_continuation_shows_its_first_line_until_all() {
        let row = continuation(
            "director_continuation",
            "<system-reminder>Run the tests.\n\nThen report the failures.</system-reminder>",
        );
        assert_eq!(
            row.body.as_deref(),
            Some("Run the tests.\n\nThen report the failures.")
        );
        let rows = render_injected_prompt(&row, Detail::Details, &theme(), 100, false);
        assert_eq!(texts(&rows), vec!["   [reminder] Run the tests. ..."]);
        let rows = render_injected_prompt(&row, Detail::All, &theme(), 100, false);
        assert_eq!(
            texts(&rows),
            vec![
                "   [reminder] Run the tests.",
                "     Then report the failures."
            ]
        );
        // A bracketed header line is the label's twin: the row starts past
        // it. An enclosing tag pair never shows.
        let row = continuation(
            "autonomous_continuation",
            "[autonomous-continuation]\n\nContinue until the tests pass.",
        );
        let rows = render_injected_prompt(&row, Detail::Overview, &theme(), 100, false);
        assert_eq!(
            texts(&rows),
            vec!["   [auto] Continue until the tests pass."]
        );
        let row = continuation(
            "quota_resume",
            "<provider_quota_resumed>\nThe usage limit was reset.\nContinue the task.\n</provider_quota_resumed>",
        );
        assert_eq!(
            row.body.as_deref(),
            Some("The usage limit was reset.\nContinue the task.")
        );
        let rows = render_injected_prompt(&row, Detail::Overview, &theme(), 100, false);
        assert_eq!(
            texts(&rows),
            vec!["   [resume] The usage limit was reset. ..."]
        );
        let row = continuation(
            "director_continuation",
            "[director: forced call to `lookup`]",
        );
        let rows = render_injected_prompt(&row, Detail::Overview, &theme(), 100, false);
        assert_eq!(
            texts(&rows),
            vec!["   [reminder] [director: forced call to `lookup`]"]
        );
        let row = continuation("autonomous_continuation", &"word ".repeat(40));
        let rows = render_injected_prompt(&row, Detail::Overview, &theme(), 40, false);
        let [cut] = texts(&rows).try_into().expect("one row");
        assert!(cut.starts_with("   [auto] word word"), "{cut:?}");
        assert!(cut.ends_with("..."), "{cut:?}");
        assert!(str_width(&cut) < 40, "{cut:?}");
        let rows = render_injected_prompt(&row, Detail::All, &theme(), 40, false);
        assert!(rows.len() > 1, "{rows:?}");
        assert!(texts(&rows)
            .iter()
            .all(|row| row.starts_with("   ") && str_width(row) < 40));
    }

    /// Goal prompts, displayed injected prompts and engine bookkeeping are
    /// off the allow-list.
    #[test]
    fn only_the_engine_continuations_are_on_the_allow_list() {
        for custom_type in [
            "goal_prompt",
            "goal_context",
            "heartbeat_prompt",
            "harness_digest",
            "refinement_notice",
            "session_slash_command_result",
            "eukhe.worker_recovery",
        ] {
            assert_eq!(
                continuation_row(
                    &CustomType::parse(custom_type),
                    &UserContent::Text("body".to_string())
                ),
                None,
                "{custom_type}"
            );
        }
    }
}
