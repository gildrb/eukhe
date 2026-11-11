//! The vertical stack of the live area (rule 4; model
//! `bend/screen.bend` section 4, `vstack`): children one under the other
//! from the top of the viewport, clipped to its height. No child is drawn
//! outside the viewport, no two overlap, and children that fit are drawn
//! whole. The placement runs as the Bend model, one call of the compiled
//! core (`bend/ffi_screen.bend`, law `screen_ffi_answers_spelled`).

use eukhe_bend::wire::NAT_MAX;
use eukhe_bend::Entry;

use crate::Line;

/// Stack `children` into a viewport of `rows` rows (the terminal's rows,
/// a `u16`): each child's rows go at its rect (model `vstack`), cut to the
/// rect's visible height.
pub(crate) fn stack_rows(children: Vec<Vec<Line>>, rows: usize) -> Vec<Line> {
    let cap = |n: usize| u64::try_from(n).map_or(NAT_MAX, |n| n.min(NAT_MAX));
    let rows = cap(rows);
    let heights = cut_heights(children.iter().map(|child| cap(child.len())), rows);
    let visible: Vec<usize> = eukhe_bend::decide(
        Entry::Screen,
        |writer| {
            writer.tag(2).count(heights.len());
            for &height in &heights {
                writer.nat(height);
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

/// The heights the core gets: each child's height cut at the rows left
/// above it. A child shows at most the rows left, and every child after
/// the bottom gets 0 rows whatever its height, so the visible heights are
/// the model's on the uncut heights; and the rows the core adds up (the
/// start of each child, from 0) stay at most `rows`, never past the
/// compiled core's 2^48-1 however many children there are.
fn cut_heights(heights: impl Iterator<Item = u64>, rows: u64) -> Vec<u64> {
    let mut left = rows;
    heights
        .map(|height| {
            let cut = height.min(left);
            left -= cut;
            cut
        })
        .collect()
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

    /// The heights the core adds up stay within the rows, however many
    /// children there are and however tall each one is (a sum past the
    /// compiled core's 2^48-1 would stop the process), and each child
    /// keeps the rows it shows.
    #[test]
    fn heights_sent_add_up_to_at_most_the_rows() {
        let tall = [NAT_MAX, NAT_MAX, 3, NAT_MAX];
        assert_eq!(cut_heights(tall.into_iter(), NAT_MAX), [NAT_MAX, 0, 0, 0]);
        assert_eq!(cut_heights([2, 5, 1, 4].into_iter(), 6), [2, 4, 0, 0]);
        assert_eq!(cut_heights([1, 2].into_iter(), 6), [1, 2]);
    }
}
