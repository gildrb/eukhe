//! Pacing of streamed assistant text (docs/interface.md S8, rule 2; model
//! `bend/screen.bend` section 2, `pace.step`).
//!
//! Text arrives in chunks of any size. Each frame shows more of it: at
//! least `min` characters while there is a backlog, and `1/(1+lag)` of
//! the backlog when that is more. The screen never shows text that did
//! not arrive, and never shows less than before.

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

    /// `n` more characters arrived (model `Chunk{n}`).
    pub fn chunk(&mut self, n: usize) {
        self.recv += n;
    }

    /// The renderer draws a frame (model `Frame{}`): reveal part of the
    /// backlog.
    pub fn frame(&mut self, rate: PaceRate) {
        self.shown += reveal(rate, self.recv.saturating_sub(self.shown));
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

/// The characters one frame adds with `backlog` characters waiting
/// (model `reveal`).
#[must_use]
pub fn reveal(rate: PaceRate, backlog: usize) -> usize {
    backlog.min(rate.min.max(backlog / rate.lag.saturating_add(1)))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A burst drains in a bounded number of frames, each frame shows
    /// more than the one before, and none shows text that did not arrive.
    #[test]
    fn a_burst_drains_smoothly_and_never_runs_ahead() {
        let mut pace = Pace::default();
        pace.chunk(400);
        let mut shown = Vec::new();
        while !pace.drained() {
            pace.frame(PaceRate::DEFAULT);
            shown.push(pace.shown());
        }
        assert_eq!(
            shown,
            [
                100, 175, 231, 273, 304, 328, 346, 359, 369, 376, 382, 386, 389, 391, 393, 395,
                397, 399, 400
            ]
        );
    }

    /// With no backlog a frame shows nothing new; a shrunk text never
    /// shows more than it holds.
    #[test]
    fn a_frame_without_backlog_and_a_shrink_keep_the_pace_behind() {
        let mut pace = Pace::default();
        pace.frame(PaceRate::DEFAULT);
        assert_eq!(pace, Pace::default());
        pace.chunk(10);
        pace.frame(PaceRate { min: 8, lag: 0 });
        pace.shrink_to(5);
        assert_eq!(pace, Pace { recv: 5, shown: 5 });
    }

    /// The largest lag (`terminal.streamPace.lag` at its maximum) reveals
    /// `min` a frame: `1 + lag` saturates instead of overflowing.
    #[test]
    fn the_largest_lag_reveals_the_minimum() {
        let mut pace = Pace::default();
        pace.chunk(10);
        pace.frame(PaceRate {
            min: 2,
            lag: usize::MAX,
        });
        assert_eq!(pace, Pace { recv: 10, shown: 2 });
    }
}
