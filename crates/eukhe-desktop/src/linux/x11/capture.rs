//! Window capture: from the pixmap a compositing manager keeps of the window
//! (Composite), else from the screen under a server grab (port of omp
//! `crates/natives/src/desktop/linux/x11/capture.rs`).

use x11rb::connection::Connection;
use x11rb::protocol::composite::ConnectionExt as _;
use x11rb::protocol::xproto::{self, ConnectionExt as _, ImageFormat, ImageOrder, VisualClass};
use x11rb::rust_connection::RustConnection;

use super::{XError, XWindow, X11};
use crate::error::{Error, Refusal, WindowError};
use crate::frame::{Capture, Rgba};
use crate::geometry::{GlobalRect, PixelSize};
use crate::types::{Support, Window};

/// Asks for Composite 0.2, which names window pixmaps.
pub(super) fn composite(conn: &RustConnection) -> Result<Support, XError> {
    let version = conn.composite_query_version(0, 4)?.reply()?;
    Ok(
        if (version.major_version, version.minor_version) >= (0, 2) {
            Support::Supported
        } else {
            Support::Unsupported
        },
    )
}

fn failed(detail: String) -> Error {
    Error::Refused(Refusal::Capture {
        detail: detail.into(),
    })
}

/// How a drawable's pixels are stored.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PixelFormat {
    order: ImageOrder,
    red: u32,
    green: u32,
    blue: u32,
    alpha: Alpha,
}

/// A 32-bit ARGB visual's alpha is premultiplied; other visuals are opaque.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Alpha {
    Opaque,
    Premultiplied(u32),
}

/// One channel of `pixel` under `mask`, scaled to 8 bits.
fn channel(pixel: u32, mask: u32) -> u8 {
    if mask == 0 {
        return 0;
    }
    let value = (pixel & mask) >> mask.trailing_zeros();
    let max = mask >> mask.trailing_zeros();
    u8::try_from(u64::from(value) * 255 / u64::from(max)).unwrap_or(u8::MAX)
}

/// 32-bit pixels of `size` as straight RGBA; `None` when `data` is short.
fn to_rgba(data: &[u8], format: PixelFormat, size: PixelSize) -> Option<Vec<u8>> {
    let pixels = size.rgba_len()? / 4;
    let words = data.get(..pixels * 4)?;
    let mut out = Vec::with_capacity(pixels * 4);
    for bytes in words.as_chunks::<4>().0 {
        let pixel = match format.order {
            ImageOrder::MSB_FIRST => u32::from_be_bytes(*bytes),
            _ => u32::from_le_bytes(*bytes),
        };
        let (red, green, blue) = (
            channel(pixel, format.red),
            channel(pixel, format.green),
            channel(pixel, format.blue),
        );
        match format.alpha {
            Alpha::Opaque => out.extend_from_slice(&[red, green, blue, u8::MAX]),
            Alpha::Premultiplied(mask) => {
                let alpha = channel(pixel, mask);
                let straight = |value: u8| match alpha {
                    0 => 0,
                    alpha => {
                        u8::try_from(u16::from(value) * 255 / u16::from(alpha)).unwrap_or(u8::MAX)
                    }
                };
                out.extend_from_slice(&[straight(red), straight(green), straight(blue), alpha]);
            }
        }
    }
    Some(out)
}

impl X11 {
    /// The pixels of a 32-bit visual `visual` of `depth`.
    fn format(&self, visual: xproto::Visualid, depth: u8) -> Result<PixelFormat, Error> {
        let setup = self.conn.setup();
        let bits = setup
            .pixmap_formats
            .iter()
            .find(|format| format.depth == depth)
            .map(|format| format.bits_per_pixel);
        if bits != Some(32) {
            return Err(failed(format!(
                "depth {depth} stores {bits:?} bits per pixel; only 32-bit pixels are read"
            )));
        }
        let visual = setup
            .roots
            .iter()
            .flat_map(|screen| &screen.allowed_depths)
            .flat_map(|depth| &depth.visuals)
            .find(|candidate| candidate.visual_id == visual)
            .filter(|visual| {
                matches!(
                    visual.class,
                    VisualClass::TRUE_COLOR | VisualClass::DIRECT_COLOR
                )
            })
            .ok_or_else(|| failed(format!("visual {visual:#x} is no true-color visual")))?;
        let rgb = visual.red_mask | visual.green_mask | visual.blue_mask;
        Ok(PixelFormat {
            order: setup.image_byte_order,
            red: visual.red_mask,
            green: visual.green_mask,
            blue: visual.blue_mask,
            alpha: match depth {
                32 => Alpha::Premultiplied(!rgb),
                _ => Alpha::Opaque,
            },
        })
    }

    /// `window`'s content, shadow excluded.
    pub(in crate::linux) fn capture(&self, window: &Window) -> Result<Capture, Error> {
        let client = XWindow::of(&window.id)?;
        let placed = self
            .placed(client)
            .map_err(|_| WindowError::NotFound(window.id.clone()))?;
        let named = match self.extensions.composite {
            Support::Supported => self.capture_named(client, placed)?,
            Support::Unsupported => None,
        };
        match named {
            Some(capture) => Ok(capture),
            None => self.capture_screen(placed),
        }
    }

    /// The window read from the pixmap of the innermost redirected window
    /// holding it; `None` when no window from it up to the root is.
    fn capture_named(&self, client: XWindow, placed: GlobalRect) -> Result<Option<Capture>, Error> {
        let mut chain = vec![client.0];
        while let Some(parent) = chain.last().and_then(|last| self.parent(*last)) {
            if parent == self.root || chain.len() > super::TREE_WALK_LIMIT {
                break;
            }
            chain.push(parent);
        }
        let pixmap = self.conn.generate_id().map_err(XError::from)?;
        for holder in chain {
            let named = self
                .conn
                .composite_name_window_pixmap(holder, pixmap)
                .map_err(XError::from)?
                .check();
            if named.is_err() {
                continue;
            }
            let read = self.read_pixmap(holder, pixmap, placed);
            self.conn.free_pixmap(pixmap).map_err(XError::from)?;
            return read.map(Some);
        }
        Ok(None)
    }

    fn read_pixmap(
        &self,
        holder: xproto::Window,
        pixmap: xproto::Pixmap,
        placed: GlobalRect,
    ) -> Result<Capture, Error> {
        let attributes = self
            .conn
            .get_window_attributes(holder)
            .map_err(XError::from)?
            .reply()
            .map_err(XError::from)?;
        let geometry = self
            .conn
            .get_geometry(holder)
            .map_err(XError::from)?
            .reply()
            .map_err(XError::from)?;
        let origin = self
            .conn
            .translate_coordinates(holder, self.root, 0, 0)
            .map_err(XError::from)?
            .reply()
            .map_err(XError::from)?;
        // The pixmap starts at the holder's outer corner, border included.
        let border = i32::from(geometry.border_width);
        let x = placed.x - (i32::from(origin.dst_x) - border);
        let y = placed.y - (i32::from(origin.dst_y) - border);
        let size = PixelSize {
            width: placed.width,
            height: placed.height,
        };
        let format = self.format(attributes.visual, geometry.depth)?;
        let image = self.get_image(pixmap, x, y, size, format)?;
        Ok(Capture {
            image,
            shows: placed,
        })
    }

    /// The part of `rect` on the root window, read from the screen under a
    /// server grab so nothing moves over it between the check and the read.
    fn capture_screen(&self, rect: GlobalRect) -> Result<Capture, Error> {
        let screen = self
            .conn
            .get_geometry(self.root)
            .map_err(XError::from)?
            .reply()
            .map_err(XError::from)?;
        let shows = intersect(
            rect,
            GlobalRect {
                x: 0,
                y: 0,
                width: u32::from(screen.width),
                height: u32::from(screen.height),
            },
        )
        .ok_or_else(|| failed("the window lies off the screen".to_owned()))?;
        let root = self
            .conn
            .get_window_attributes(self.root)
            .map_err(XError::from)?
            .reply()
            .map_err(XError::from)?;
        let format = self.format(root.visual, screen.depth)?;
        self.conn.grab_server().map_err(XError::from)?;
        let image = self.get_image(
            self.root,
            shows.x,
            shows.y,
            PixelSize {
                width: shows.width,
                height: shows.height,
            },
            format,
        );
        self.conn
            .ungrab_server()
            .and_then(|_| self.conn.flush())
            .map_err(XError::from)?;
        Ok(Capture {
            image: image?,
            shows,
        })
    }

    fn get_image(
        &self,
        drawable: xproto::Drawable,
        x: i32,
        y: i32,
        size: PixelSize,
        format: PixelFormat,
    ) -> Result<Rgba, Error> {
        let edge = |value: i32| {
            i16::try_from(value)
                .map_err(|_| failed(format!("offset {value} is past the X coordinate range")))
        };
        let length = |value: u32| {
            u16::try_from(value)
                .map_err(|_| failed(format!("size {value} is past the X coordinate range")))
        };
        let reply = self
            .conn
            .get_image(
                ImageFormat::Z_PIXMAP,
                drawable,
                edge(x)?,
                edge(y)?,
                length(size.width)?,
                length(size.height)?,
                !0,
            )
            .map_err(XError::from)?
            .reply()
            .map_err(XError::from)?;
        let data = to_rgba(&reply.data, format, size).ok_or_else(|| {
            failed(format!(
                "the server returned {} bytes for {}x{} pixels",
                reply.data.len(),
                size.width,
                size.height
            ))
        })?;
        Rgba::new(size, data)
    }
}

/// The overlap of two rectangles; `None` when they do not meet.
fn intersect(a: GlobalRect, b: GlobalRect) -> Option<GlobalRect> {
    let end = |rect: GlobalRect, width: u32| i64::from(rect.x) + i64::from(width);
    let left = a.x.max(b.x);
    let top = a.y.max(b.y);
    let right = end(a, a.width).min(end(b, b.width));
    let bottom = (i64::from(a.y) + i64::from(a.height)).min(i64::from(b.y) + i64::from(b.height));
    let width = u32::try_from(right - i64::from(left))
        .ok()
        .filter(|width| *width > 0)?;
    let height = u32::try_from(bottom - i64::from(top))
        .ok()
        .filter(|height| *height > 0)?;
    Some(GlobalRect {
        x: left,
        y: top,
        width,
        height,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const BGRX: PixelFormat = PixelFormat {
        order: ImageOrder::LSB_FIRST,
        red: 0x00ff_0000,
        green: 0x0000_ff00,
        blue: 0x0000_00ff,
        alpha: Alpha::Opaque,
    };

    #[test]
    fn little_endian_bgrx_reads_as_opaque_rgba() {
        let size = PixelSize {
            width: 2,
            height: 1,
        };
        let data = [0x30, 0x20, 0x10, 0x00, 0xff, 0x00, 0x00, 0x99];
        assert_eq!(
            to_rgba(&data, BGRX, size),
            Some(vec![0x10, 0x20, 0x30, 0xff, 0x00, 0x00, 0xff, 0xff])
        );
        assert_eq!(to_rgba(&data[..4], BGRX, size), None);
    }

    #[test]
    fn premultiplied_alpha_is_undone() {
        let argb = PixelFormat {
            alpha: Alpha::Premultiplied(0xff00_0000),
            ..BGRX
        };
        let size = PixelSize {
            width: 1,
            height: 1,
        };
        // Half-transparent white, premultiplied: 0x80 in every channel.
        assert_eq!(
            to_rgba(&[0x80, 0x80, 0x80, 0x80], argb, size),
            Some(vec![0xff, 0xff, 0xff, 0x80])
        );
    }

    #[test]
    fn a_window_partly_off_screen_is_cut_to_it() {
        let screen = GlobalRect {
            x: 0,
            y: 0,
            width: 100,
            height: 100,
        };
        let window = GlobalRect {
            x: -10,
            y: 90,
            width: 50,
            height: 50,
        };
        assert_eq!(
            intersect(window, screen),
            Some(GlobalRect {
                x: 0,
                y: 90,
                width: 40,
                height: 10
            })
        );
        let away = GlobalRect { x: 200, ..window };
        assert_eq!(intersect(away, screen), None);
    }
}
