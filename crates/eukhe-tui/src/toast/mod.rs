//! Ephemeral action toasts: right-aligned auto-dismiss rows in the live
//! area for short-lived action confirmations (clipboard copies and their
//! kin).
//!
//! SANCTIONED DIVERGENCE from TS (documented per the #289 precedent): the
//! TS product has no in-TUI toast surface -- confirmations render as
//! durable chat status rows (`showStatus`), and its "toast" surfaces are
//! OS-level notifications (the termux notifier). The
//! Rust product keeps the chat row for anything the
//! transcript should remember and surfaces action acks the user only
//! needs for a moment as a live row instead: the confirmation never
//! enters the transcript or the scrollback.

use std::time::{Duration, Instant};

use crate::style::Style;
use crate::{Line, Span};

/// How long a toast stays on screen before it auto-dismisses.
pub const TOAST_TTL: Duration = Duration::from_secs(3);

/// How many distinct toasts stack at once (the oldest drop first).
pub const TOAST_STACK_LIMIT: usize = 3;

/// One ephemeral confirmation: its text, how many times its action
/// repeated inside the live window, and its expiry.
#[derive(Debug, Clone)]
struct Toast {
    text: String,
    repeats: usize,
    expires_at: Instant,
}

impl Toast {
    fn new(text: String) -> Self {
        let now = Instant::now();
        Toast {
            text,
            repeats: 1,
            expires_at: expiry(now),
        }
    }

    /// The overlay label: the second and later repeats of the same action
    /// inside the window read as the count bump ("Copied ... (x3)"), so a
    /// coalesced repeat still visibly acknowledges every copy.
    fn label(&self) -> String {
        if self.repeats > 1 {
            format!(
                "{text} (x{repeats})",
                text = self.text,
                repeats = self.repeats
            )
        } else {
            self.text.clone()
        }
    }
}

/// The expiry `TOAST_TTL` out from `now` (an overflow near the monotonic
/// clock's end lands at `now`, which reads as expired).
fn expiry(now: Instant) -> Instant {
    now.checked_add(TOAST_TTL).unwrap_or(now)
}

/// The active toast stack (oldest first, newest last).
#[derive(Debug, Default)]
pub struct Toasts {
    entries: Vec<Toast>,
}

impl Toasts {
    /// Show a toast. A repeat of an action whose toast is still on screen
    /// COALESCES into that toast: its TTL resets and its repeat count
    /// climbs, so three consecutive copies read as one "Copied ... (x3)"
    /// toast -- never three identical rows stacked. The coalesced toast
    /// moves to the bottom of the stack (it is the newest action). A
    /// distinct action keeps its own toast; the stack caps at the limit
    /// with the oldest dropping first.
    pub fn push(&mut self, text: impl Into<String>) {
        let text = text.into();
        // Only a still-visible toast coalesces: one whose TTL already
        // passed starts fresh (the earlier confirmation is gone).
        let now = Instant::now();
        if let Some(index) = self
            .entries
            .iter()
            .rposition(|toast| toast.text == text && toast.expires_at > now)
        {
            let mut toast = self.entries.remove(index);
            toast.expires_at = expiry(Instant::now());
            toast.repeats += 1;
            self.entries.push(toast);
        } else {
            self.entries.push(Toast::new(text));
        }
        while self.entries.len() > TOAST_STACK_LIMIT {
            self.entries.remove(0);
        }
    }

    /// Drop the toasts whose TTL passed at `now`; `true` when any went.
    pub fn prune_expired(&mut self, now: Instant) -> bool {
        let before = self.entries.len();
        self.entries.retain(|toast| toast.expires_at > now);
        before != self.entries.len()
    }

    /// The earliest entry's expiry, active or not: the run loop arms its
    /// TTL wakeup on this so an idle surface still repaints the overlay
    /// away (a stale past deadline self-drains -- the prune at that
    /// iteration empties it).
    #[must_use]
    pub fn next_expiry(&self) -> Option<Instant> {
        self.entries.iter().map(|toast| toast.expires_at).min()
    }

    /// The still-active toasts' labels, oldest first.
    pub fn active(&self, now: Instant) -> Vec<String> {
        self.entries
            .iter()
            .filter(|toast| toast.expires_at > now)
            .map(Toast::label)
            .collect()
    }

    /// Fast-forward every toast's expiry by `age` (test hook: expiry
    /// without a wall-clock wait; an expiry already too close to the
    /// monotonic clock's start lands at `now`, which reads as expired).
    #[cfg(test)]
    pub(crate) fn age_by(&mut self, age: Duration) {
        let now = Instant::now();
        for toast in &mut self.entries {
            toast.expires_at = toast.expires_at.checked_sub(age).unwrap_or(now);
        }
    }
}

/// The toast rows of the live area, oldest first: each toast is a
/// compact right-aligned pill on its own row. A pill wider than `width`
/// truncates to it.
#[must_use]
pub fn render_toasts(toasts: &[String], width: usize, style: Style) -> Vec<Line> {
    toasts
        .iter()
        .map(|text| {
            let pill = crate::width::truncate_to_width(&format!(" {text} "), width, "");
            let col = width.saturating_sub(crate::width::str_width(&pill));
            vec![Span::raw(" ".repeat(col)), Span::styled(pill, style)]
        })
        .collect()
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
