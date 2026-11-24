//! The text a computer call returns: windows one per line, an observation
//! (its window, screenshot frame and tree), and an act's effect per step.

use std::fmt::Write as _;

use eukhe_desktop::{
    ActReport, Done, Effect, Focus, FoundNode, Screenshot, Step, Tree, Truncation, Window,
};

use super::policy::Policy;

/// `window` as one line, ending in whether its app is allowed.
fn window_line(out: &mut String, window: &Window, policy: &Policy) {
    let Window {
        id,
        title,
        app,
        bounds,
        focus,
        ..
    } = window;
    let _infallible = write!(
        out,
        "- id={id} app={app:?} title={title:?} at {},{} {}x{}",
        bounds.x, bounds.y, bounds.width, bounds.height
    );
    match focus {
        Focus::Focused => out.push_str(" focused"),
        Focus::Unfocused => {}
    }
    if !policy.allows(app) {
        out.push_str(" (not in computer.apps)");
    }
    out.push('\n');
}

/// The window list of `computer_windows`.
pub(super) fn windows(windows: &[Window], policy: &Policy) -> String {
    if windows.is_empty() {
        return "No windows match.".to_owned();
    }
    let mut out = String::new();
    for window in windows {
        window_line(&mut out, window, policy);
    }
    out
}

/// An observation: its window, the frame of the screenshot the model got,
/// and its tree.
pub(super) fn observation(
    out: &mut String,
    window: &Window,
    screenshot: Option<&Screenshot>,
    tree: Option<&Tree>,
    policy: &Policy,
) {
    window_line(out, window, policy);
    if let Some(screenshot) = screenshot {
        let _infallible = writeln!(
            out,
            "Screenshot {}x{} px: pixel clicks use this frame.",
            screenshot.size.width, screenshot.size.height
        );
    }
    if let Some(tree) = tree {
        out.push_str(&tree.text);
        if !tree.text.ends_with('\n') {
            out.push('\n');
        }
        match tree.truncation {
            Truncation::Complete => {}
            Truncation::Truncated => {
                out.push_str("(tree cut short: use `find`, or a smaller `max_depth`)\n");
            }
        }
    }
}

/// The elements `find` matched, one per line with its ref.
pub(super) fn found(out: &mut String, nodes: &[FoundNode]) {
    if nodes.is_empty() {
        out.push_str("No element matches.\n");
    }
    for node in nodes {
        let _infallible = write!(out, "- {}", node.native_role);
        if let Some(title) = &node.title {
            let _infallible = write!(out, " {title:?}");
        }
        if let Some(value) = &node.value {
            let _infallible = write!(out, " value={value:?}");
        }
        let _infallible = writeln!(out, " [ref={}]", node.reference);
    }
}

/// The step's kind as the tool names it.
pub(super) fn kind(step: &Step) -> &'static str {
    match step {
        Step::Press { .. } => "press",
        Step::SetValue { .. } => "set_value",
        Step::Type { .. } => "type",
        Step::Key { .. } => "key",
        Step::Click { .. } => "click",
        Step::Scroll { .. } => "scroll",
        Step::Menu { .. } => "menu",
        Step::SelectText { .. } => "select_text",
    }
}

/// Each step's effect, by the steps' `kinds`; the steps after the first
/// one not confirmed did not run.
pub(super) fn report(out: &mut String, kinds: &[&str], report: &ActReport) {
    for (index, kind) in kinds.iter().enumerate() {
        let _infallible = write!(out, "{}. {kind}: ", index + 1);
        let _infallible = match report.steps.get(index) {
            Some(Effect::Confirmed {
                done: Done::Delivered,
            }) => writeln!(out, "confirmed"),
            Some(Effect::Confirmed {
                done: Done::Selected { selection },
            }) => writeln!(
                out,
                "confirmed, selected {} UTF-16 units at {}",
                selection.length, selection.start
            ),
            Some(Effect::Unverifiable { reason }) => {
                writeln!(out, "unverifiable (input went out): {reason}")
            }
            Some(Effect::Refused { reason }) => writeln!(out, "refused: {reason}"),
            None => writeln!(out, "not run"),
        };
    }
}

#[cfg(test)]
mod tests {
    use eukhe_desktop::{
        ElementRef, Error, GlobalRect, Refusal, StaleCause, StaleRef, Unverified, WindowId,
    };

    use super::*;

    fn target(reference: &str) -> ElementRef {
        reference
            .parse()
            .unwrap_or_else(|error| panic!("{reference}: {error:?}"))
    }

    /// One line per step: what it did, why a step was refused or left
    /// unconfirmed (the desktop's own typed reason), and which steps the
    /// batch never ran.
    #[test]
    fn a_report_names_each_steps_effect() {
        let steps = [
            Step::Press {
                target: target("e1"),
            },
            Step::SetValue {
                target: target("e2"),
                value: "x".to_owned(),
            },
            Step::Press {
                target: target("e3"),
            },
            Step::Press {
                target: target("e4"),
            },
        ];
        let stale = Error::Refused(Refusal::StaleRef(StaleRef {
            reference: target("e3"),
            cause: StaleCause::Expired,
        }));
        let refused = stale.to_string();
        let effects = ActReport {
            steps: vec![
                Effect::Confirmed {
                    done: Done::Delivered,
                },
                Effect::Unverifiable {
                    reason: Unverified::InputFailed {
                        detail: "the app stopped answering".into(),
                    },
                },
                Effect::from(stale),
            ],
        };
        let kinds: Vec<&str> = steps.iter().map(kind).collect();
        let mut out = String::new();
        report(&mut out, &kinds, &effects);
        assert_eq!(
            out,
            format!(
                "1. press: confirmed\n2. set_value: unverifiable (input went out): {}\n\
                 3. press: refused: {refused}\n4. press: not run\n",
                Unverified::InputFailed {
                    detail: "the app stopped answering".into()
                }
            )
        );
    }

    /// A window outside `computer.apps` is listed and marked.
    #[test]
    fn the_window_list_marks_apps_the_user_did_not_allow() {
        let window = |id: &str, app: &str, focus: Focus| Window {
            id: WindowId::new(id),
            title: "Draft".to_owned(),
            app: app.to_owned(),
            pid: None,
            bounds: GlobalRect {
                x: 10,
                y: 20,
                width: 800,
                height: 600,
            },
            focus,
        };
        let policy = Policy::new(&["TextEdit"], Vec::new());
        assert_eq!(
            windows(
                &[
                    window("1", "TextEdit", Focus::Focused),
                    window("2", "Mail", Focus::Unfocused)
                ],
                &policy
            ),
            "- id=1 app=\"TextEdit\" title=\"Draft\" at 10,20 800x600 focused\n\
             - id=2 app=\"Mail\" title=\"Draft\" at 10,20 800x600 (not in computer.apps)\n"
        );
    }
}
