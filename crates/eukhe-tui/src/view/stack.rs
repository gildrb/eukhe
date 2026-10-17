//! The vertical stack of the live area (docs/interface.md S8, rule 4; model
//! `bend/screen.bend` section 4, `vstack`): children one under the other
//! from the top of the viewport, clipped to its height. No child is drawn
//! outside the viewport, no two overlap, and children that fit are drawn
//! whole.

use crate::Line;

/// A placed child: its top row and its visible height.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Rect {
    pub(crate) y: usize,
    pub(crate) h: usize,
}

/// Place children of heights `heights` from row `y` in a viewport of
/// `rows` rows (model `vstack`).
pub(crate) fn vstack(heights: &[usize], y: usize, rows: usize) -> Vec<Rect> {
    let mut top = y;
    heights
        .iter()
        .map(|&h| {
            let rect = Rect {
                y: top,
                h: h.min(rows.saturating_sub(top)),
            };
            top += h;
            rect
        })
        .collect()
}

/// Stack `children` into a viewport of `rows` rows: each child's rows go
/// at its rect, cut to the rect's height.
pub(crate) fn stack_rows(children: Vec<Vec<Line>>, rows: usize) -> Vec<Line> {
    let heights: Vec<usize> = children.iter().map(Vec::len).collect();
    let rects = vstack(&heights, 0, rows);
    let mut out: Vec<Line> = Vec::with_capacity(rects.iter().map(|rect| rect.h).sum());
    for (child, rect) in children.into_iter().zip(rects) {
        out.extend(child.into_iter().take(rect.h));
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
        assert_eq!(
            vstack(&[2, 3, 4], 1, 5),
            [
                Rect { y: 1, h: 2 },
                Rect { y: 3, h: 2 },
                Rect { y: 6, h: 0 }
            ]
        );
        let row = |text: &str| vec![crate::Span::raw(text.to_string())];
        assert_eq!(
            stack_rows(vec![vec![row("a")], vec![row("b"), row("c")]], 2),
            [row("a"), row("b")]
        );
    }
}
