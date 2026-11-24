//! Points, sizes and rectangles. Pixels of a delivered screenshot and global
//! desktop points are distinct types: only a frame maps one to the other.

use serde::{Deserialize, Serialize};

/// A point in pixels of the last screenshot delivered for a window.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct FramePoint {
    pub x: f64,
    pub y: f64,
}

/// A point in global logical desktop coordinates (points, not pixels).
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct GlobalPoint {
    pub x: f64,
    pub y: f64,
}

/// The size of an image in pixels.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PixelSize {
    pub width: u32,
    pub height: u32,
}

impl PixelSize {
    /// Bytes of an RGBA image of this size; `None` past `usize`.
    pub(crate) fn rgba_len(self) -> Option<usize> {
        usize::try_from(u64::from(self.width) * u64::from(self.height) * 4).ok()
    }
}

/// A window or display rectangle in global logical points.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GlobalRect {
    pub x: i32,
    pub y: i32,
    pub width: u32,
    pub height: u32,
}

/// An element's bounds in global logical points, as accessibility reports
/// them.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct ElementBounds {
    pub x: f64,
    pub y: f64,
    pub width: f64,
    pub height: f64,
}

impl ElementBounds {
    /// The point a click on the element goes to.
    #[must_use]
    pub fn center(&self) -> GlobalPoint {
        GlobalPoint {
            x: self.x + self.width / 2.0,
            y: self.y + self.height / 2.0,
        }
    }
}

/// Scroll distance in lines; positive `dy` scrolls down, positive `dx` right.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScrollDelta {
    pub dx: i32,
    pub dy: i32,
}
