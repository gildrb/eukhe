//! Screenshot frames: what a delivered image shows, and the map from its
//! pixels to global points (port of omp `crates/natives/src/desktop/frame.rs`).

use serde::{Deserialize, Serialize};

use crate::error::{Error, Refusal};
use crate::geometry::{FramePoint, GlobalPoint, GlobalRect, PixelSize};
use crate::types::{ImageCaps, Window, WindowId};

/// An RGBA image, four bytes per pixel, rows top to bottom.
pub(crate) struct Rgba {
    size: PixelSize,
    data: Vec<u8>,
}

impl Rgba {
    /// `data` as an image of `size`; refused unless its length matches.
    #[allow(
        dead_code,
        reason = "the platform backends build their captures with it"
    )]
    pub(crate) fn new(size: PixelSize, data: Vec<u8>) -> Result<Self, Error> {
        if size.width == 0 || size.height == 0 || size.rgba_len() != Some(data.len()) {
            return Err(Error::Refused(Refusal::Capture {
                detail: format!(
                    "the capture returned {} bytes for {}x{} pixels",
                    data.len(),
                    size.width,
                    size.height
                )
                .into(),
            }));
        }
        Ok(Self { size, data })
    }

    /// The image averaged down to `target`, which is no larger.
    fn downscale(self, target: PixelSize) -> Self {
        if target == self.size {
            return self;
        }
        let (sw, sh) = (self.size.width as usize, self.size.height as usize);
        let (dw, dh) = (target.width as usize, target.height as usize);
        let mut data = Vec::with_capacity(dw * dh * 4);
        for y in 0..dh {
            let (y0, y1) = span(y, sh, dh);
            for x in 0..dw {
                let (x0, x1) = span(x, sw, dw);
                let mut sum = [0u64; 4];
                for row in y0..y1 {
                    let start = (row * sw + x0) * 4;
                    let pixels = &self.data[start..start + (x1 - x0) * 4];
                    for pixel in pixels.as_chunks::<4>().0 {
                        for (total, channel) in sum.iter_mut().zip(pixel) {
                            *total += u64::from(*channel);
                        }
                    }
                }
                let count = ((y1 - y0) * (x1 - x0)) as u64;
                data.extend(
                    sum.iter()
                        .map(|total| u8::try_from(total / count).unwrap_or(u8::MAX)),
                );
            }
        }
        Self { size: target, data }
    }

    fn png(&self) -> Result<Vec<u8>, Error> {
        let failed = |error: png::EncodingError| {
            Error::Refused(Refusal::Capture {
                detail: format!("PNG encoding failed: {error}").into(),
            })
        };
        let mut out = Vec::with_capacity(self.data.len() / 2);
        let mut encoder = png::Encoder::new(&mut out, self.size.width, self.size.height);
        encoder.set_color(png::ColorType::Rgba);
        encoder.set_depth(png::BitDepth::Eight);
        let mut writer = encoder.write_header().map_err(failed)?;
        writer.write_image_data(&self.data).map_err(failed)?;
        writer.finish().map_err(failed)?;
        Ok(out)
    }
}

/// The source pixels `[start, end)` destination pixel `index` of `target`
/// averages, never empty.
fn span(index: usize, source: usize, target: usize) -> (usize, usize) {
    let start = index * source / target;
    let end = ((index + 1) * source / target).max(start + 1);
    (start, end)
}

/// The largest size within `caps` with `size`'s aspect ratio, never larger
/// than `size`.
fn capped(size: PixelSize, caps: ImageCaps) -> PixelSize {
    let (w, h) = (u64::from(size.width), u64::from(size.height));
    let (max_w, max_h) = (
        u64::from(caps.max_width.get()),
        u64::from(caps.max_height.get()),
    );
    if w <= max_w && h <= max_h {
        return size;
    }
    let (width, height) = if w * max_h >= h * max_w {
        (max_w, ((h * max_w + w / 2) / w).max(1))
    } else {
        (((w * max_h + h / 2) / h).max(1), max_h)
    };
    PixelSize {
        width: u32::try_from(width).unwrap_or(caps.max_width.get()),
        height: u32::try_from(height).unwrap_or(caps.max_height.get()),
    }
}

/// What a window capture shows: its pixels and the logical part of the
/// window they cover (the whole window, or the part on the captured screen).
#[allow(dead_code, reason = "the platform backends construct it")]
pub(crate) struct Capture {
    pub(crate) image: Rgba,
    pub(crate) shows: GlobalRect,
}

/// A screenshot as delivered: PNG bytes and their size in pixels. Pixel
/// steps on the window use this frame until the next screenshot.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Screenshot {
    pub png: Vec<u8>,
    pub size: PixelSize,
}

/// The geometry of the last screenshot delivered for a window.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FrameGeometry {
    size: PixelSize,
    /// The shown part's origin relative to the window's, in points.
    offset_x: i32,
    offset_y: i32,
    /// The shown part's size in points.
    part_width: u32,
    part_height: u32,
    /// The window's size when captured: a resize invalidates the frame.
    captured_width: u32,
    captured_height: u32,
}

impl FrameGeometry {
    fn new(window: &Window, shows: GlobalRect, size: PixelSize) -> Self {
        Self {
            size,
            offset_x: shows.x.saturating_sub(window.bounds.x),
            offset_y: shows.y.saturating_sub(window.bounds.y),
            part_width: shows.width,
            part_height: shows.height,
            captured_width: window.bounds.width,
            captured_height: window.bounds.height,
        }
    }

    /// The global point `point` of this frame shows, with the window now at
    /// `current`'s position.
    pub(crate) fn map_point(
        &self,
        point: FramePoint,
        current: &Window,
    ) -> Result<GlobalPoint, FrameError> {
        let inside =
            |value: f64, limit: u32| value.is_finite() && value >= 0.0 && value < f64::from(limit);
        if !inside(point.x, self.size.width) || !inside(point.y, self.size.height) {
            return Err(FrameError::Outside {
                point,
                size: self.size,
            });
        }
        if current.bounds.width != self.captured_width
            || current.bounds.height != self.captured_height
        {
            return Err(FrameError::Resized {
                window: current.id.clone(),
            });
        }
        let local_x = point.x * f64::from(self.part_width) / f64::from(self.size.width);
        let local_y = point.y * f64::from(self.part_height) / f64::from(self.size.height);
        Ok(GlobalPoint {
            x: f64::from(current.bounds.x) + f64::from(self.offset_x) + local_x,
            y: f64::from(current.bounds.y) + f64::from(self.offset_y) + local_y,
        })
    }
}

/// Scales `capture` of `window` into `caps` and encodes it; returns the
/// screenshot and the frame pixel steps map through.
pub(crate) fn deliver(
    capture: Capture,
    window: &Window,
    caps: ImageCaps,
) -> Result<(Screenshot, FrameGeometry), Error> {
    let size = capped(capture.image.size, caps);
    let image = capture.image.downscale(size);
    let png = image.png()?;
    Ok((
        Screenshot { png, size },
        FrameGeometry::new(window, capture.shows, size),
    ))
}

/// Why a frame pixel names no point.
#[derive(Clone, Debug, PartialEq, thiserror::Error, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum FrameError {
    #[error("no screenshot of window {window} yet: pixel steps are in pixels of the window's last screenshot; observe it with a screenshot first, or act on an element ref; nothing was sent")]
    NoCapture { window: WindowId },
    #[error("({}, {}) is outside the last screenshot ({}x{} px); pixel steps are in pixels of the window's last screenshot; nothing was sent", .point.x, .point.y, .size.width, .size.height)]
    Outside { point: FramePoint, size: PixelSize },
    #[error("window {window} was resized since its last screenshot; take another before pixel steps; nothing was sent")]
    Resized { window: WindowId },
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroU32;

    use super::*;
    use crate::types::{Focus, Pid};

    fn window(x: i32, y: i32, width: u32, height: u32) -> Window {
        Window {
            id: WindowId::new("4"),
            title: String::new(),
            app: "App".to_owned(),
            pid: Some(Pid(1)),
            bounds: GlobalRect {
                x,
                y,
                width,
                height,
            },
            focus: Focus::Unfocused,
        }
    }

    fn caps(width: u32, height: u32) -> ImageCaps {
        ImageCaps {
            max_width: NonZeroU32::new(width).unwrap_or(NonZeroU32::MIN),
            max_height: NonZeroU32::new(height).unwrap_or(NonZeroU32::MIN),
        }
    }

    fn size(width: u32, height: u32) -> PixelSize {
        PixelSize { width, height }
    }

    /// A 2x window capture of an 800x600 window, scaled into 1280x896.
    fn frame() -> FrameGeometry {
        let window = window(100, 50, 800, 600);
        FrameGeometry::new(
            &window,
            window.bounds,
            capped(size(1600, 1200), caps(1280, 896)),
        )
    }

    #[test]
    fn captures_shrink_into_the_caps_keeping_their_ratio() {
        assert_eq!(frame().size, size(1195, 896));
        assert_eq!(capped(size(4000, 100), caps(1280, 896)), size(1280, 32));
        assert_eq!(capped(size(640, 480), caps(1280, 896)), size(640, 480));
    }

    #[test]
    fn frame_pixels_map_to_global_points_of_the_window_where_it_is_now() {
        let frame = frame();
        let point = |x, y| FramePoint { x, y };
        let at = |point: GlobalPoint| (point.x.round(), point.y.round());
        assert_eq!(
            frame
                .map_point(point(597.5, 448.0), &window(100, 50, 800, 600))
                .map(at),
            Ok((500.0, 350.0))
        );
        assert_eq!(
            frame
                .map_point(point(0.0, 0.0), &window(300, 70, 800, 600))
                .map(at),
            Ok((300.0, 70.0))
        );
    }

    #[test]
    fn points_outside_the_frame_or_on_a_resized_window_are_refused() {
        let frame = frame();
        let current = window(100, 50, 800, 600);
        for x in [-1.0, 1195.0, f64::NAN] {
            assert!(matches!(
                frame.map_point(FramePoint { x, y: 1.0 }, &current),
                Err(FrameError::Outside { .. })
            ));
        }
        assert_eq!(
            frame.map_point(FramePoint { x: 1.0, y: 1.0 }, &window(100, 50, 801, 600)),
            Err(FrameError::Resized {
                window: WindowId::new("4")
            })
        );
    }

    #[test]
    fn a_part_capture_maps_from_its_own_origin() {
        let window = window(-200, 0, 800, 600);
        let shows = GlobalRect {
            x: 0,
            y: 0,
            width: 600,
            height: 600,
        };
        let frame = FrameGeometry::new(&window, shows, size(600, 600));
        assert_eq!(
            frame
                .map_point(FramePoint { x: 10.0, y: 20.0 }, &window)
                .map(|point| (point.x.round(), point.y.round())),
            Ok((10.0, 20.0))
        );
    }

    #[test]
    fn downscaling_averages_each_box() {
        let image = Rgba::new(size(2, 1), vec![0, 0, 0, 255, 200, 100, 50, 255])
            .unwrap_or_else(|error| panic!("{error}"));
        let small = image.downscale(size(1, 1));
        assert_eq!(small.data, [100, 50, 25, 255]);
        assert!(Rgba::new(size(2, 2), vec![0; 4]).is_err());
    }
}
