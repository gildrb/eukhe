use super::*;
use crate::chrome::ContextUsage;
use crate::git_placement::LinkedWorktree;
use crate::theme::ColorMode;

fn theme() -> Theme {
    Theme::builtin("eukhe", ColorMode::TrueColor)
}

fn text(line: &Line) -> String {
    line.iter().map(|span| span.content.as_str()).collect()
}

fn base() -> ChromeState {
    ChromeState {
        cwd: "/work/eukhe".to_string(),
        model_id: Some("mock".to_string()),
        context: Some(ContextUsage {
            tokens: 0,
            context_window: 128_000,
        }),
        git: Some(GitPlacement {
            branch: Some("main".to_string()),
            worktree: None,
        }),
        activity: Some(ActivityDock::default()),
        ..ChromeState::default()
    }
}

const ROOTS: PathRoots = PathRoots {
    home: Some("/home/u"),
    temp: "/scratch",
};

#[test]
fn the_idle_line_reads_model_path_branch_and_context() {
    let line = render_status_line(&base(), Detail::Overview, &theme(), 60);
    assert_eq!(
        text(&line),
        format!(
            " [M] mock - [D] eukhe - @ main{}ctx: 0.0%/128K",
            " ".repeat(15)
        )
    );
    // Model brighter than the rest; the context label brighter than
    // its value.
    let theme = theme();
    let fg = |needle: &str| {
        line.iter()
            .find(|span| span.content == needle)
            .unwrap_or_else(|| panic!("missing span {needle:?}"))
            .style
            .fg
    };
    assert_eq!(fg("[M] mock"), theme.fg_style(ThemeColor::Muted).fg);
    assert_eq!(fg("[D] eukhe"), theme.fg_style(ThemeColor::Dim).fg);
    assert_eq!(fg(" - "), theme.fg_style(ThemeColor::Dim).fg);
    assert_eq!(fg("ctx: "), theme.fg_style(ThemeColor::Text).fg);
    assert_eq!(fg("0.0%/128K"), theme.fg_style(ThemeColor::Dim).fg);
    assert!(line.iter().all(|span| span.style.bg.is_none()));
}

/// A dictation take leads the line: red while it records, accent while it
/// transcribes; no take, no segment.
#[test]
fn the_dictation_phase_leads_the_line() {
    let theme = theme();
    let lead = |phase| {
        let state = ChromeState {
            dictation: phase,
            ..base()
        };
        let line = render_status_line(&state, Detail::Overview, &theme, 120);
        let span = &line[1];
        (span.content.clone(), span.style.fg)
    };
    assert_eq!(
        (
            lead(Some(crate::dictation::Phase::Recording)),
            lead(Some(crate::dictation::Phase::Transcribing)),
            lead(None).0,
        ),
        (
            (
                "[REC] recording, esc cancels".to_string(),
                theme.fg_style(ThemeColor::Error).fg
            ),
            (
                "[STT] transcribing, esc cancels".to_string(),
                theme.fg_style(ThemeColor::Accent).fg
            ),
            "[M] mock".to_string(),
        )
    );
}

#[test]
fn the_model_segment_carries_the_tier_badge_and_thinking_level() {
    let state = ChromeState {
        model_id: Some("opus".to_string()),
        thinking_suffix: Some("medium".to_string()),
        service_tier: Some("priority".to_string()),
        ..ChromeState::default()
    };
    assert_eq!(
        model_segment(&state, &theme()).map(|line| text(&line)),
        Some("[M] opus >> - [med]".to_string())
    );
    let flex = ChromeState {
        service_tier: Some("flex".to_string()),
        thinking_suffix: Some("off".to_string()),
        ..state
    };
    assert_eq!(
        model_segment(&flex, &theme()).map(|line| text(&line)),
        Some("[M] opus flex - [ ] off".to_string())
    );
    assert_eq!(model_segment(&ChromeState::default(), &theme()), None);
}

#[test]
fn the_path_label_shortens_like_omp() {
    let worktree = |branch: &str| GitPlacement {
        branch: Some(branch.to_string()),
        worktree: Some(LinkedWorktree {
            project: "eukhe".to_string(),
            name: "eukhe-CLI".to_string(),
        }),
    };
    let cases = [
        (
            "/home/u/Repos/eukhe-CLI",
            Some(worktree("CLI")),
            "[wt] eukhe/eukhe-CLI",
        ),
        (
            "/home/u/Repos/eukhe-CLI",
            Some(worktree("eukhe-CLI")),
            "[wt] eukhe",
        ),
        ("/home/u/src/app", None, "[D] ~/src/app"),
        ("/home/u", None, "[D] ~"),
        ("/home/u/Projects/app/web", None, "[D] app/web"),
        ("/work/app", None, "[D] app"),
        ("/opt/app", None, "[D] /opt/app"),
        ("/scratch/run-1", None, "[T] run-1"),
        ("/tmp", None, "[T] /tmp"),
        (
            "/home/u/src/a-rather-long-directory/with/many/levels",
            None,
            "[D] ...-long-directory/with/many/levels",
        ),
    ];
    let got: Vec<String> = cases
        .iter()
        .map(|(cwd, git, _)| path_label(cwd, git.as_ref(), &ROOTS))
        .collect();
    let want: Vec<String> = cases
        .iter()
        .map(|(_, _, label)| (*label).to_string())
        .collect();
    assert_eq!(got, want);
}

#[test]
fn context_counts_and_tones_follow_omp() {
    let counts: Vec<String> = [
        999,
        1_500,
        10_000,
        128_000,
        1_000_000,
        2_500_000,
        1_000_000_000,
    ]
    .into_iter()
    .map(format_count)
    .collect();
    assert_eq!(counts, ["999", "1.5K", "10K", "128K", "1M", "2.5M", "1B"]);
    let tones = [
        context_color(0, 128_000),
        context_color(63_999, 128_000),
        context_color(64_000, 128_000),
        context_color(89_600, 128_000),
        context_color(115_200, 128_000),
        // A 1M window turns at the same shares: 16% of it (160K tokens,
        // above the old absolute 150K level) is still dim.
        context_color(160_000, 1_000_000),
        context_color(500_000, 1_000_000),
        context_color(700_000, 1_000_000),
        context_color(900_000, 1_000_000),
        // An unknown window reaches no band.
        context_color(2_000, 0),
    ];
    assert_eq!(
        tones,
        [
            ThemeColor::Dim,
            ThemeColor::Dim,
            ThemeColor::Warning,
            ThemeColor::ContextHigh,
            ThemeColor::Error,
            ThemeColor::Dim,
            ThemeColor::Warning,
            ThemeColor::ContextHigh,
            ThemeColor::Error,
            ThemeColor::Dim,
        ]
    );
    let unknown_window = ContextUsage {
        tokens: 2_000,
        context_window: 0,
    };
    assert_eq!(
        text(&context_segment(unknown_window, &theme())),
        "ctx: 2K/?"
    );
}

#[test]
fn optional_segments_show_only_while_they_carry_something() {
    let state = ChromeState {
        tray_override: Some("Press Ctrl+C again to exit".to_string()),
        session_name: Some("refactor".to_string()),
        cost_usd: Some(0.126),
        tray_depth: Some(1),
        memory: Some(crate::memory_block::MemoryGauge::after(
            &eukhe_types::daemon::MemoryUpdate::Summarized {
                lines: vec![eukhe_types::daemon::MemoryLine {
                    id: 41,
                    count: 1,
                    text: "user: ship it".to_string(),
                }],
                view_bytes: 90_100,
            },
            crate::memory_block::UpdateTiming::InRequest,
        )),
        context: None,
        ..base()
    };
    let line = render_status_line(&state, Detail::All, &theme(), 120);
    assert_eq!(
        text(&line),
        " Press Ctrl+C again to exit - [M] mock - [D] eukhe - @ main - refactor - $0.13 - depth 1 - mem 90K/128K ~ - expanded"
    );
    let quiet = ChromeState {
        session_name: Some(String::new()),
        cost_usd: Some(0.0),
        tray_depth: Some(0),
        context: None,
        git: None,
        ..base()
    };
    let line = render_status_line(&quiet, Detail::Overview, &theme(), 120);
    assert_eq!(text(&line), " [M] mock - [D] eukhe");
    let line = render_status_line(&quiet, Detail::Details, &theme(), 120);
    assert_eq!(text(&line), " [M] mock - [D] eukhe - details");
}

#[test]
fn activity_segments_show_live_counts_only_until_focused() {
    let theme = theme();
    let texts = |dock: &ActivityDock| -> Vec<String> {
        activity_segments(dock, &theme).iter().map(text).collect()
    };
    assert_eq!(texts(&ActivityDock::default()), Vec::<String>::new());
    let live = ActivityDock {
        subagents_running_direct: 1,
        subagents_running_nested: 1,
        subagents_queued: 1,
        heartbeats: 3,
        heartbeats_paused: 1,
        bash_running: 1,
        factory_group: true,
        goal_label: Some("Pursuing goal (0s)".to_string()),
        ..ActivityDock::default()
    };
    assert_eq!(
        texts(&live),
        [
            "2 subagents - 1 queued",
            "3 heartbeats - 1 paused",
            "1 shell",
            "Pursuing goal (0s)"
        ]
    );
    let success = theme.fg_style(ThemeColor::Success).fg;
    assert!(activity_segments(&live, &theme)
        .iter()
        .all(|segment| segment[0].style.fg == success));
    // A focused dock shows every group, the zero counts included, and
    // the selected one behind the selection band (its text keeps its
    // own color).
    let focused = ActivityDock {
        factory_group: true,
        selected: ActivityGroup::Heartbeats,
        focused: true,
        ..ActivityDock::default()
    };
    assert_eq!(
        texts(&focused),
        ["0 subagents", "0 heartbeats", "0 shells", "0 factory"]
    );
    let band = theme.selection_row_style();
    let segments = activity_segments(&focused, &theme);
    let banded: Vec<bool> = segments
        .iter()
        .map(|segment| segment[0].style.bg == band.bg)
        .collect();
    assert_eq!(banded, [false, true, false, false]);
    assert_eq!(
        segments[1][0].style.fg,
        theme.fg_style(ThemeColor::Muted).fg
    );
}

#[test]
fn a_short_row_cuts_the_left_side_and_keeps_the_context() {
    let state = ChromeState {
        tray_override: Some("Press Ctrl+C again to exit".to_string()),
        ..base()
    };
    for width in 20..=60 {
        let line = render_status_line(&state, Detail::Overview, &theme(), width);
        let row = text(&line);
        assert_eq!(line_width(&line), width - 1, "{row:?}");
        assert!(row.ends_with("ctx: 0.0%/128K"), "{row:?}");
        assert!(row.contains("..."), "{row:?}");
    }
    let line = render_status_line(&state, Detail::Overview, &theme(), 14);
    assert_eq!(text(&line), " Press Ctr...");
}

/// The speed segment yields first: at a narrow width the other segments
/// (the detail level too) stay whole and the speed drops; with some room
/// it shows cut; with room enough it shows whole after the model.
#[test]
fn the_speed_segment_yields_to_the_other_segments() {
    let state = ChromeState {
        speed: Some(crate::gen_speed::SpeedPhase::Done(
            crate::gen_speed::ResponseSpeed {
                ttft: std::time::Duration::from_millis(500),
                prefill: crate::gen_speed::Prefill::Rate(2000.0),
                decode_tokens_per_second: Some(50.0),
            },
        )),
        ..base()
    };
    let row = |width: usize| text(&render_status_line(&state, Detail::All, &theme(), width));
    assert_eq!(
        [row(60), row(80), row(120)],
        [
            format!(
                " [M] mock - [D] eukhe - @ main - expanded{}ctx: 0.0%/128K",
                " ".repeat(4)
            ),
            " [M] mock - prefill 2000 tok/... - [D] eukhe - @ main - expanded ctx: 0.0%/128K"
                .to_string(),
            format!(
                " [M] mock - prefill 2000 tok/s (TTFT 0.50s) · decode 50.0 tok/s - [D] eukhe - @ main - expanded{}ctx: 0.0%/128K",
                " ".repeat(10)
            ),
        ]
    );
}

/// A long title and a long speed text on a 120-column row: the title
/// cuts first, then the speed text, then the title drops; the model,
/// its thinking level, the `mem` gauge, the detail label and the
/// context usage stay whole at every width.
#[test]
fn the_title_and_the_speed_yield_before_the_fixed_segments() {
    let state = ChromeState {
        thinking_suffix: Some("medium".to_string()),
        session_name: Some(
            "Fix the typo in the release notes and tell me what changed".to_string(),
        ),
        memory: Some(crate::memory_block::MemoryGauge::seeded(1_140)),
        speed: Some(crate::gen_speed::SpeedPhase::Done(
            crate::gen_speed::ResponseSpeed {
                ttft: std::time::Duration::from_millis(500),
                prefill: crate::gen_speed::Prefill::Rate(2000.0),
                decode_tokens_per_second: Some(50.0),
            },
        )),
        git: None,
        ..base()
    };
    let row = |width: usize| {
        text(&render_status_line(
            &state,
            Detail::Details,
            &theme(),
            width,
        ))
    };
    assert_eq!(
        row(140),
        " [M] mock - [med] - prefill 2000 tok/s (TTFT 0.50s) · decode 50.0 tok/s - [D] eukhe - Fix the t... - mem 1.1K/128K - details ctx: 0.0%/128K"
    );
    assert_eq!(
        row(120),
        " [M] mock - [med] - prefill 2000 tok/s (TTFT 0.50s) ... - [D] eukhe - Fix t... - mem 1.1K/128K - details ctx: 0.0%/128K"
    );
    assert_eq!(
        row(100),
        " [M] mock - [med] - prefill 2000... - [D] eukhe - Fix t... - mem 1.1K/128K - details ctx: 0.0%/128K"
    );
    assert_eq!(
        row(80),
        format!(
            " [M] mock - [med] - [D] eukhe - mem 1.1K/128K - details{}ctx: 0.0%/128K",
            " ".repeat(10)
        )
    );
    for width in 80..=200 {
        let row = row(width);
        assert!(
            row.contains("[M] mock - [med] - ")
                && row.contains(" - mem 1.1K/128K - details")
                && row.ends_with("ctx: 0.0%/128K"),
            "{width}: {row:?}"
        );
    }
}
