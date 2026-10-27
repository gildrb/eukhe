//! The vertical stack of the live area (rule 4; model
//! `bend/screen.bend` section 4, `vstack`): children one under the other
//! from the top of the viewport, clipped to its height. No child is drawn
//! outside the viewport, no two overlap, and children that fit are drawn
//! whole. The placement runs as the Bend model, one call of the compiled
//! core (`bend/ffi_screen.bend`, law `screen_ffi_stack`).

use eukhe_bend::wire::NAT_MAX;
use eukhe_bend::Entry;

use crate::Line;

/// Stack `children` into a viewport of `rows` rows (the terminal's rows,
/// a `u16`): each child's rows go at its rect (model `vstack`), cut to the
/// rect's visible height.
///
/// Each child's height goes to the core cut at `rows`: a child cannot show
/// more than `rows` rows, and every child after a cut one starts at or
/// past the bottom, so the visible heights are the same, and the rows the
/// core adds up stay below `(children + 1) * rows`.
pub(crate) fn stack_rows(children: Vec<Vec<Line>>, rows: usize) -> Vec<Line> {
    let cap = |n: usize| u64::try_from(n).map_or(NAT_MAX, |n| n.min(NAT_MAX));
    let rows = cap(rows);
    let visible: Vec<usize> = crate::bend_core::decide(
        Entry::Screen,
        |writer| {
            writer.tag(2).count(children.len());
            for child in &children {
                writer.nat(cap(child.len()).min(rows));
            }
            writer.nat(0).nat(rows);
        },
        |reader| {
            let rects = reader.count()?;
            let mut visible = Vec::with_capacity(rects);
            for _ in 0..rects {
                let _y = reader.nat()?;
                visible.push(reader.count()?);
            }
            Ok(visible)
        },
    );
    let mut out: Vec<Line> = Vec::with_capacity(visible.iter().sum());
    for (child, h) in children.into_iter().zip(visible) {
        out.extend(child.into_iter().take(h));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Children that overflow the viewport are cut at its bottom; the
    /// ones after the bottom get no rows.
    #[test]
    fn children_past_the_bottom_are_clipped() {
        let row = |text: &str| vec![crate::Span::raw(text.to_string())];
        assert_eq!(
            stack_rows(
                vec![vec![row("a")], vec![row("b"), row("c")], vec![row("d")]],
                2
            ),
            [row("a"), row("b")]
        );
    }
}
