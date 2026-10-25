//! The color math of the themes (`bend/color.bend`, entry
//! `bend/ffi_color.bend`; `laws/color.bend`): the xterm-256 index a
//! 256-color terminal paints for a color, whether a color is light (its
//! WCAG relative luminance above one half), and the xterm-256 palette.
//! A color is its `[red, green, blue]` channels.

use std::sync::LazyLock;

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// The xterm-256 index a 256-color terminal paints for `rgb`.
#[must_use]
pub fn to256(rgb: [u8; 3]) -> u8 {
    expect_core(
        Entry::Color,
        ask(0, &[rgb], |r| {
            let index = r.u32()?;
            u8::try_from(index).map_err(|_| WireError::Malformed {
                at: 0,
                expected: "an xterm-256 index",
            })
        }),
    )[0]
}

/// Whether `rgb` is light: its relative luminance is above one half.
#[must_use]
pub fn light(rgb: [u8; 3]) -> bool {
    // `Reader::bool` is fixed to one reader lifetime; `ask` needs a reader
    // of any lifetime, which only a closure gives.
    #[allow(clippy::redundant_closure_for_method_calls)]
    expect_core(Entry::Color, ask(1, &[rgb], |r| r.bool()))[0]
}

/// The xterm-256 palette, read once from the core.
static PALETTE: LazyLock<Vec<[u8; 3]>> =
    LazyLock::new(|| expect_core(Entry::Color, palette_call()));

/// The color of xterm-256 index `index`: the ANSI-16 table, the 6x6x6
/// cube, then the 24-step gray ramp.
#[must_use]
pub fn ansi256(index: u8) -> [u8; 3] {
    PALETTE[usize::from(index)]
}

fn put_rgb(w: &mut Writer, [r, g, b]: [u8; 3]) {
    w.u32(r.into()).u32(g.into()).u32(b.into());
}

/// A color the reply holds: three channels of at most 255.
pub(crate) fn get_rgb(r: &mut Reader<'_>) -> Result<[u8; 3], WireError> {
    let mut channel = || {
        let c = r.u32()?;
        u8::try_from(c).map_err(|_| WireError::Malformed {
            at: 0,
            expected: "a channel of at most 255",
        })
    };
    Ok([channel()?, channel()?, channel()?])
}

/// Request `tag` over `colors`; the reply's answer per color.
fn ask<T>(
    tag: u32,
    colors: &[[u8; 3]],
    mut item: impl FnMut(&mut Reader<'_>) -> Result<T, WireError>,
) -> Result<Vec<T>, Error> {
    let mut w = Writer::new();
    w.tag(tag).count(colors.len());
    for &rgb in colors {
        put_rgb(&mut w, rgb);
    }
    let reply = call(Entry::Color, &w.finish()?)?;
    let mut r = Reader::reply(&reply)?;
    let n = r.count()?;
    if n != colors.len() {
        return Err(WireError::Malformed {
            at: 0,
            expected: "an answer per color",
        }
        .into());
    }
    let out = (0..n)
        .map(|_| item(&mut r))
        .collect::<Result<Vec<T>, _>>()?;
    r.end()?;
    Ok(out)
}

fn palette_call() -> Result<Vec<[u8; 3]>, Error> {
    let reply = call(Entry::Color, &Writer::new().tag(2).finish()?)?;
    let mut r = Reader::reply(&reply)?;
    if r.count()? != 256 {
        return Err(WireError::Malformed {
            at: 0,
            expected: "the 256 colors of the palette",
        }
        .into());
    }
    let colors = (0..256)
        .map(|_| get_rgb(&mut r))
        .collect::<Result<Vec<_>, _>>()?;
    r.end()?;
    Ok(colors)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The core is reached: red quantizes to the cube's red, white is
    /// light, index 1 is the ANSI-16 maroon.
    #[test]
    fn the_core_answers() {
        assert_eq!(
            (to256([255, 0, 0]), light([255, 255, 255]), ansi256(1)),
            (196, true, [128, 0, 0])
        );
    }
}
