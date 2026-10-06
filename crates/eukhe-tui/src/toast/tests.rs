use super::*;

fn now() -> Instant {
    Instant::now()
}

/// A toast starts active, expires after its TTL, and pruning drops it.
#[test]
fn toasts_expire_on_their_ttl() {
    let mut toasts = Toasts::default();
    toasts.push("Copied");
    assert_eq!(toasts.active(now()).len(), 1);
    toasts.age_by(TOAST_TTL + Duration::from_millis(1));
    assert!(toasts.active(now()).is_empty());
    assert!(toasts.prune_expired(now()));
    assert!(toasts.entries.is_empty());
}

/// Pruning with nothing to drop reports no change.
#[test]
fn pruning_a_fresh_stack_reports_no_change() {
    let mut toasts = Toasts::default();
    toasts.push("Again");
    assert!(!toasts.prune_expired(now()));
    assert_eq!(toasts.entries.len(), 1);
}

/// The stack keeps the newest toasts and caps at the limit.
#[test]
fn the_stack_caps_at_the_limit() {
    let mut toasts = Toasts::default();
    for index in 0..=TOAST_STACK_LIMIT {
        toasts.push(format!("toast {index}"));
    }
    let texts: Vec<String> = toasts.active(now());
    assert_eq!(texts, vec!["toast 1", "toast 2", "toast 3"]);
}

/// Consecutive repeats of the same action COALESCE: the toast stack
/// holds one entry, its TTL resets (the repeat keeps it alive), and
/// its label carries the count bump.
#[test]
fn consecutive_repeats_coalesce_into_one_toast() {
    let mut toasts = Toasts::default();
    toasts.push("Copied to clipboard");
    toasts.push("Copied to clipboard");
    toasts.push("Copied to clipboard");
    let labels = toasts.active(now());
    assert_eq!(labels.len(), 1, "three copies are one toast, not rows");
    assert_eq!(labels[0], "Copied to clipboard (x3)");
    assert_eq!(toasts.entries.len(), 1);
    // The TTL reset: half the TTL twice stays inside a refreshed
    // window (an unrefreshed toast expires before the second half).
    toasts.age_by(TOAST_TTL / 2);
    toasts.push("Copied to clipboard");
    toasts.age_by(TOAST_TTL / 2);
    assert_eq!(
        toasts.active(now()),
        vec!["Copied to clipboard (x4)"],
        "the refresh keeps the coalesced toast alive"
    );
}

/// A repeat AFTER the previous toast's TTL starts a fresh window: no
/// count bump for a confirmation the user has already seen expire.
#[test]
fn a_repeat_after_the_ttl_starts_a_fresh_toast() {
    let mut toasts = Toasts::default();
    toasts.push("Copied to clipboard");
    toasts.age_by(TOAST_TTL + Duration::from_millis(1));
    toasts.push("Copied to clipboard");
    assert_eq!(
        toasts.active(now()),
        vec!["Copied to clipboard"],
        "the fresh toast carries no count bump"
    );
}

/// Distinct actions keep their own toasts; a repeat of one of them
/// coalesces into THAT toast (it is the toast the user last triggered)
/// and moves it to the bottom of the stack.
#[test]
fn distinct_actions_stack_and_a_repeat_coalesces_into_its_own_toast() {
    let mut toasts = Toasts::default();
    toasts.push("Copied last agent message to clipboard");
    toasts.push("Copied selection to clipboard");
    let labels = toasts.active(now());
    assert_eq!(
        labels,
        vec![
            "Copied last agent message to clipboard",
            "Copied selection to clipboard",
        ],
        "distinct actions are separate toasts"
    );
    toasts.push("Copied last agent message to clipboard");
    assert_eq!(
        toasts.active(now()),
        vec![
            "Copied selection to clipboard",
            "Copied last agent message to clipboard (x2)",
        ],
        "the repeat refreshes its own toast, newest at the bottom"
    );
}

/// Each toast is one right-aligned pill row, oldest first, carrying the
/// toast style; an overlong pill truncates to the width.
#[test]
fn toasts_render_as_right_aligned_pill_rows() {
    let style = Style::default().fg(crate::style::Color::Indexed(5));
    let rows = render_toasts(&["Copied".to_string(), "x".repeat(30)], 12, style);
    assert_eq!(
        rows,
        vec![
            vec![Span::raw("    "), Span::styled(" Copied ", style)],
            vec![
                Span::raw(""),
                Span::styled(format!(" {}", "x".repeat(11)), style)
            ],
        ]
    );
}
