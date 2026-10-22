//! Pacing of streamed assistant text (docs/interface.md S8, rule 2; model
//! `bend/screen.bend` section 2, `pace.step`).
//!
//! Text arrives in chunks of any size. Each frame shows more of it: at
//! least `min` characters while there is a backlog, and `1/(1+lag)` of
//! the backlog when that is more. The screen never shows text that did
//! not arrive, and never shows less than before. A frame runs as the Bend
//! model, one call of the compiled core (`bend/ffi_screen.bend`, law
//! `screen_ffi_pace`).

use eukhe_bend::wire::NAT_MAX;
use eukhe_bend::Entry;

/// How fast a frame reveals the backlog.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PaceRate {
    /// The characters each frame reveals at least (while there is a
    /// backlog).
    pub min: usize,
    /// A frame reveals `1/(1+lag)` of the backlog when that is more than
    /// `min`.
    pub lag: usize,
}

impl PaceRate {
    /// The default rate, tuned for the 16 ms frame gate: a steady stream
    /// of `R` characters a second trails by about `4R/62` characters
    /// (some 60 ms), and a burst of 400 characters shows in 19 frames
    /// (about 300 ms).
    pub const DEFAULT: PaceRate = PaceRate { min: 2, lag: 3 };
}

impl Default for PaceRate {
    fn default() -> Self {
        PaceRate::DEFAULT
    }
}

/// What arrived and what the screen shows, in characters.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Pace {
    recv: usize,
    shown: usize,
}

impl Pace {
    /// The characters that arrived.
    #[must_use]
    pub fn recv(self) -> usize {
        self.recv
    }

    /// The characters the screen shows.
    #[must_use]
    pub fn shown(self) -> usize {
        self.shown
    }

    /// Whether every character that arrived shows.
    #[must_use]
    pub fn drained(self) -> bool {
        self.shown >= self.recv
    }

    /// `more` characters arrived, then the renderer draws a frame (model
    /// `Chunk{more}` then `Frame{}`): the frame reveals part of the
    /// backlog.
    ///
    /// Each count goes to the core saturated at the wire's largest Nat
    /// ([`NAT_MAX`], some 10^14): a lag or a minimum at the cap reveals as
    /// one past every backlog would (law `pace_lag_at_cap`), and a message
    /// never holds 10^14 characters, so `recv` and `more` stay exact.
    pub fn frame(&mut self, rate: PaceRate, more: usize) {
        let cap = |n: usize| u64::try_from(n).map_or(NAT_MAX, |n| n.min(NAT_MAX));
        let recv = cap(self.recv);
        let shown = cap(self.shown);
        let more = cap(more).min(NAT_MAX - recv);
        let (recv, shown) = crate::bend_core::decide(
            Entry::Screen,
            |writer| {
                writer
                    .tag(1)
                    .nat(cap(rate.min))
                    .nat(cap(rate.lag))
                    .nat(recv)
                    .nat(shown)
                    .nat(more);
            },
            |reader| Ok((reader.count()?, reader.count()?)),
        );
        self.recv = recv;
        self.shown = shown;
    }

    /// The text was replaced by a shorter one (a provider snapshot can
    /// shrink): the pace restarts at what still exists. Outside the
    /// model, which only grows.
    pub fn shrink_to(&mut self, recv: usize) {
        self.recv = recv;
        self.shown = self.shown.min(recv);
    }

    /// The characters that render changed (the detail level shows or
    /// hides thinking): `recv` and `shown` each move to `at` of their
    /// count, the same place in the message counted the new way. Outside
    /// the model, where the visible text only grows.
    pub fn recount(&mut self, at: impl Fn(usize) -> usize) {
        self.recv = at(self.recv);
        self.shown = at(self.shown);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// With no backlog a frame shows nothing new; a shrunk text never
    /// shows more than it holds.
    #[test]
    fn a_frame_without_backlog_and_a_shrink_keep_the_pace_behind() {
        let mut pace = Pace::default();
        pace.frame(PaceRate::DEFAULT, 0);
        assert_eq!(pace, Pace::default());
        pace.frame(PaceRate { min: 8, lag: 0 }, 10);
        pace.shrink_to(5);
        assert_eq!(pace, Pace { recv: 5, shown: 5 });
    }

    /// The largest lag and minimum (`terminal.streamPace` at its maximum)
    /// reach the core saturated: the lag reveals `min` a frame, the
    /// minimum the whole backlog, and no number overflows.
    #[test]
    fn the_largest_lag_reveals_the_minimum() {
        let mut pace = Pace::default();
        pace.frame(
            PaceRate {
                min: 2,
                lag: usize::MAX,
            },
            10,
        );
        assert_eq!(pace, Pace { recv: 10, shown: 2 });
        pace.frame(
            PaceRate {
                min: usize::MAX,
                lag: usize::MAX,
            },
            0,
        );
        assert_eq!(
            pace,
            Pace {
                recv: 10,
                shown: 10
            }
        );
    }
}
