//! One window's pixels through `ScreenCaptureKit` (port of omp
//! `crates/natives/src/desktop/macos/capture.rs`).

use super::ffi::capture::{self, CaptureFailure};
use super::ffi::quartz;
use super::windows;
use crate::error::{Error, Permission, Refusal};
use crate::frame::{Capture, Rgba};
use crate::geometry::PixelSize;
use crate::types::Window;

pub(super) fn window(window: &Window) -> Result<Capture, Error> {
    if !quartz::screen_capture_access() {
        return Err(Error::Refused(Refusal::NotPermitted {
            permission: Permission::ScreenRecording,
        }));
    }
    let id = windows::server_id(window).ok_or_else(|| {
        Error::Refused(Refusal::Capture {
            detail: format!("window {} has no window number", window.id).into(),
        })
    })?;
    let image = capture::window(id).map_err(|failure| {
        Error::Refused(Refusal::Capture {
            detail: match failure {
                CaptureFailure::NotListed => {
                    format!("ScreenCaptureKit does not list window {id}; it may be off screen")
                        .into()
                }
                CaptureFailure::Convert => "the captured image could not be read".into(),
                CaptureFailure::Failed(detail) => detail.into(),
                CaptureFailure::Timeout => "ScreenCaptureKit did not answer in time".into(),
            },
        })
    })?;
    let size = PixelSize {
        width: image.width,
        height: image.height,
    };
    Ok(Capture {
        image: Rgba::new(size, unpremultiply(image.rgba))?,
        shows: window.bounds,
    })
}

/// Straight alpha from Quartz's premultiplied pixels, as PNG stores them.
fn unpremultiply(mut rgba: Vec<u8>) -> Vec<u8> {
    for pixel in rgba.as_chunks_mut::<4>().0 {
        let alpha = u16::from(pixel[3]);
        if alpha == 0 || alpha == 255 {
            continue;
        }
        for channel in &mut pixel[..3] {
            let straight = (u16::from(*channel) * 255 + alpha / 2) / alpha;
            *channel = u8::try_from(straight).unwrap_or(u8::MAX);
        }
    }
    rgba
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn translucent_pixels_get_straight_alpha_and_opaque_ones_stay() {
        assert_eq!(
            unpremultiply(vec![10, 20, 30, 255, 64, 32, 0, 128, 9, 9, 9, 0]),
            [10, 20, 30, 255, 128, 64, 0, 128, 9, 9, 9, 0]
        );
    }
}
