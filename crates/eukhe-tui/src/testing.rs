//! Test helpers: [`Rng`] generates the same inputs on every run.

/// A small xorshift generator: the inputs are the same on every run.
pub struct Rng(pub u64);

impl Rng {
    /// The next number of the sequence.
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    /// A number in `0..n` (`n > 0`).
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    /// A number in `low..=high`.
    pub fn range(&mut self, low: u64, high: u64) -> u64 {
        low + self.next() % (high - low + 1)
    }
}
