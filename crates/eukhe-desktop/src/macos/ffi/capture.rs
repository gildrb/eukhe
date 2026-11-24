//! `ScreenCaptureKit` window capture, in process (port of omp
//! `crates/natives/src/desktop/macos/capture/screen_capture_kit.rs`, whose
//! helper process only worked around Bun's run loop).

use std::ffi::c_void;
use std::sync::mpsc;
use std::time::Duration;

use block2::RcBlock;
use objc2::AllocAnyThread;
use objc2_core_foundation::{CGPoint, CGRect, CGSize};
use objc2_core_graphics::{
    kCGColorSpaceSRGB, CGBitmapContextCreate, CGColorSpace, CGContext, CGImage, CGImageAlphaInfo,
    CGImageByteOrderInfo,
};
use objc2_foundation::NSError;
use objc2_screen_capture_kit::{
    SCContentFilter, SCScreenshotManager, SCShareableContent, SCStreamConfiguration,
};

/// A captured window: premultiplied RGBA rows, top to bottom.
pub(crate) struct Image {
    pub(crate) width: u32,
    pub(crate) height: u32,
    pub(crate) rgba: Vec<u8>,
}

#[derive(Debug)]
pub(crate) enum CaptureFailure {
    /// `ScreenCaptureKit` does not list the window.
    NotListed,
    /// The image could not be drawn into memory.
    Convert,
    /// `ScreenCaptureKit`'s own error.
    Failed(String),
    Timeout,
}

/// How long one capture may take.
const CAPTURE_TIMEOUT: Duration = Duration::from_secs(5);

type Reply = Result<Image, CaptureFailure>;

/// Captures window `id` alone, at its backing resolution, without shadow
/// or cursor.
pub(crate) fn window(id: u32) -> Reply {
    let (sender, answer) = mpsc::sync_channel::<Reply>(1);
    let on_content = RcBlock::new(
        move |content: *mut SCShareableContent, error: *mut NSError| {
            // SAFETY: ScreenCaptureKit passes live objects or null for the
            // duration of the handler.
            let (content, error) = unsafe { (content.as_ref(), error.as_ref()) };
            match (content, error) {
                (Some(content), _) => capture(content, id, sender.clone()),
                (None, error) => {
                    sender.try_send(Err(failure(error))).ok();
                }
            }
        },
    );
    // SAFETY: the handler is a block of the declared signature; the call
    // copies it.
    unsafe {
        SCShareableContent::getShareableContentExcludingDesktopWindows_onScreenWindowsOnly_completionHandler(
            true, true, &on_content,
        );
    }
    answer
        .recv_timeout(CAPTURE_TIMEOUT)
        .unwrap_or(Err(CaptureFailure::Timeout))
}

fn capture(content: &SCShareableContent, id: u32, sender: mpsc::SyncSender<Reply>) {
    // SAFETY: plain getters on a live SCShareableContent and its windows.
    let window = unsafe { content.windows() }
        .iter()
        .find(|window| unsafe { window.windowID() } == id);
    let Some(window) = window else {
        sender.try_send(Err(CaptureFailure::NotListed)).ok();
        return;
    };
    // SAFETY: a fresh filter for one live SCWindow.
    let filter = unsafe {
        SCContentFilter::initWithDesktopIndependentWindow(SCContentFilter::alloc(), &window)
    };
    // SAFETY: the info getters read a live filter.
    let (scale, rect) = unsafe {
        let info = SCShareableContent::infoForFilter(&filter);
        (f64::from(info.pointPixelScale()), info.contentRect())
    };
    let configuration = unsafe { SCStreamConfiguration::new() };
    // SAFETY: plain setters on a fresh configuration; sizes are whole
    // pixels of the window's content.
    unsafe {
        configuration.setWidth(pixels(rect.size.width, scale));
        configuration.setHeight(pixels(rect.size.height, scale));
        configuration.setShowsCursor(false);
        configuration.setIgnoreShadowsSingleWindow(true);
    }
    let on_image = RcBlock::new(move |image: *mut CGImage, error: *mut NSError| {
        // SAFETY: as for the content handler.
        let (image, error) = unsafe { (image.as_ref(), error.as_ref()) };
        let reply = match image {
            Some(image) => rgba(image).ok_or(CaptureFailure::Convert),
            None => Err(failure(error)),
        };
        sender.try_send(reply).ok();
    });
    // SAFETY: live filter and configuration; the call copies the block.
    unsafe {
        SCScreenshotManager::captureImageWithFilter_configuration_completionHandler(
            &filter,
            &configuration,
            Some(&on_image),
        );
    }
}

fn pixels(points: f64, scale: f64) -> usize {
    let pixels = (points * scale).round().min(f64::from(u32::MAX));
    if pixels.is_finite() && pixels >= 1.0 {
        #[allow(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "a finite value between 1 and u32::MAX"
        )]
        let pixels = pixels as usize;
        pixels
    } else {
        1
    }
}

fn failure(error: Option<&NSError>) -> CaptureFailure {
    CaptureFailure::Failed(error.map_or_else(
        || "ScreenCaptureKit returned no image".to_owned(),
        |error| error.localizedDescription().to_string(),
    ))
}

/// `image` drawn into premultiplied RGBA bytes.
fn rgba(image: &CGImage) -> Option<Image> {
    let width = CGImage::width(Some(image));
    let height = CGImage::height(Some(image));
    let row = width.checked_mul(4)?;
    let mut data = vec![0u8; row.checked_mul(height)?];
    // SAFETY: the sRGB name constant is process-lived.
    let space = CGColorSpace::with_name(Some(unsafe { kCGColorSpaceSRGB }))?;
    // SAFETY: `data` holds `row * height` bytes and outlives the context,
    // which is dropped below before `data` is returned.
    let context: objc2_core_foundation::CFRetained<CGContext> = unsafe {
        CGBitmapContextCreate(
            data.as_mut_ptr().cast::<c_void>(),
            width,
            height,
            8,
            row,
            Some(&space),
            CGImageAlphaInfo::PremultipliedLast.0 | CGImageByteOrderInfo::Order32Big.0,
        )
    }?;
    #[allow(
        clippy::cast_precision_loss,
        reason = "image edges are far below 2^52 pixels"
    )]
    let size = CGSize {
        width: width as f64,
        height: height as f64,
    };
    CGContext::draw_image(
        Some(&context),
        CGRect {
            origin: CGPoint { x: 0.0, y: 0.0 },
            size,
        },
        Some(image),
    );
    drop(context);
    Some(Image {
        width: u32::try_from(width).ok()?,
        height: u32::try_from(height).ok()?,
        rgba: data,
    })
}
