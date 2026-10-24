//! The terminal colors (`bend/tui_color.bend`, entry
//! `bend/ffi_tui_color.bend`; `laws/tui_color.bend`): the effort ramp
//! between two colors, the usage band of a context, and the token of every
//! color slot of the terminal UI. Each function encodes its facts, calls
//! [`Entry::TuiColor`] and decodes the answer.

use crate::wire::{Reader, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Error};

/// The most rungs a ramp takes: the entry refuses a longer one (no ramp
/// of more rungs has distinct colors: a channel spans at most 255).
pub const RAMP_MAX: usize = 255;

/// A color as its red, green and blue channels.
pub type Rgb = [u8; 3];

/// The `rungs` rungs of the effort ramp from `low` to `high`, lowest
/// first (`TC.ramp`): rung `rungs` is `high`.
///
/// # Panics
///
/// When `rungs` is above [`RAMP_MAX`] (the entry refuses it): callers
/// pass a model's effort ladder, a few levels of the level vocabulary.
#[must_use]
pub fn ramp(low: Rgb, high: Rgb, rungs: usize) -> Vec<Rgb> {
    expect_core(Entry::TuiColor, ramp_call(low, high, rungs))
}

fn ramp_call(low: Rgb, high: Rgb, rungs: usize) -> Result<Vec<Rgb>, Error> {
    let mut request = Writer::new();
    request.tag(0);
    for channel in low.into_iter().chain(high) {
        request.nat(u64::from(channel));
    }
    request.count(rungs);
    let reply = call(Entry::TuiColor, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let count = reader.count()?;
    let mut colors = Vec::with_capacity(count);
    for _ in 0..count {
        colors.push([
            channel(&mut reader)?,
            channel(&mut reader)?,
            channel(&mut reader)?,
        ]);
    }
    reader.end()?;
    Ok(colors)
}

/// One channel of a reply: a Nat below 256 (read as a tag of 256 values,
/// so a larger one is malformed at its offset).
fn channel(reader: &mut Reader<'_>) -> Result<u8, Error> {
    let value = reader.tag_of(256, "a channel (0 to 255)")?;
    Ok(u8::try_from(value).expect("tag_of(256) answers a value below 256"))
}

/// The usage band of `tokens` in a `window`-token context (`TC.band`): how
/// many of the shares 1/2, 7/10 and 9/10 of the window the tokens reach; an
/// unknown window (0) reaches none. Both counts saturate at the wire's
/// largest Nat ([`NAT_MAX`], about 10^14 tokens).
#[must_use]
pub fn band(tokens: u64, window: u64) -> usize {
    expect_core(Entry::TuiColor, band_call(tokens, window))
}

fn band_call(tokens: u64, window: u64) -> Result<usize, Error> {
    let mut request = Writer::new();
    request
        .tag(1)
        .nat(tokens.min(NAT_MAX))
        .nat(window.min(NAT_MAX));
    let reply = call(Entry::TuiColor, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let band = reader.tag_of(4, "a usage band (0 to 3)")?;
    reader.end()?;
    Ok(band as usize)
}

/// The token index (in the theme's token table) of every color slot of
/// the terminal UI, in slot order (`TC.roles`): the ink slots, the surface
/// slots, then the ramp ends, the lift ends and the canvas.
#[must_use]
pub fn roles() -> Vec<usize> {
    expect_core(Entry::TuiColor, roles_call())
}

fn roles_call() -> Result<Vec<usize>, Error> {
    let mut request = Writer::new();
    request.tag(2);
    let reply = call(Entry::TuiColor, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let count = reader.count()?;
    let mut tokens = Vec::with_capacity(count);
    for _ in 0..count {
        tokens.push(reader.count()?);
    }
    reader.end()?;
    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::{band, ramp, roles, NAT_MAX};

    /// Each question reaches the compiled core: a ramp, a band at the
    /// wire's largest window (no product past the runtime's Nat), the
    /// roles.
    #[test]
    fn the_codec_carries_each_question_through_the_core() {
        assert_eq!(
            ramp([135, 95, 135], [139, 0, 139], 3),
            [[136, 63, 136], [137, 31, 137], [139, 0, 139]]
        );
        assert_eq!(band(64_000, 128_000), 1);
        assert_eq!(band(NAT_MAX / 10 * 9, NAT_MAX), 2);
        // t * 10 is past the runtime's 2^48 - 1: the entry never forms it.
        assert_eq!(band(28_147_497_671_066, 28_147_497_671_066), 3);
        assert_eq!(band(u64::MAX, u64::MAX), 3);
        assert_eq!(roles().len(), 58);
    }
}
