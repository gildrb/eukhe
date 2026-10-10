//! The image processor `read` uses. Port of `tools/image-processor.ts`.

use futures::future::BoxFuture;

/// Limits an image the model sees must keep; the defaults below are the
/// coding agent's.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ImageLimits {
    /// Pixels. Default 2000.
    pub max_width: u64,
    /// Pixels. Default 2000.
    pub max_height: u64,
    /// Bytes of base64. Default 4.5 MiB, below Anthropic's 5 MB.
    pub max_bytes: u64,
}

pub const DEFAULT_IMAGE_LIMITS: ImageLimits = ImageLimits {
    max_width: 2000,
    max_height: 2000,
    max_bytes: 4 * 1024 * 1024 + 512 * 1024,
};

/// The width and height of an image, in pixels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ImageSize {
    pub width: u64,
    pub height: u64,
}

/// An image's size before and after resizing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ImageResize {
    pub from: ImageSize,
    pub to: ImageSize,
}

/// An image the model can take: a supported format, within the limits, as
/// base64.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedImage {
    pub data: String,
    pub mime_type: String,
    /// Set when the image was resized: its size before and after, for the
    /// model to map coordinates back.
    pub resized: Option<ImageResize>,
    /// The original format, set when it differs from `mime_type`: BMP becomes
    /// PNG, a large PNG may become JPEG.
    pub converted_from: Option<String>,
}

/// Decodes, orients, resizes, and re-encodes images so the model can take
/// them. `read` uses one when given; without one, it passes supported images
/// within the byte limit through as they are.
///
/// Rust-only: no processor ships with the crate (TS's Photon backend in
/// `@earendil-works/pi-durable/images` is not ported); hosts supply one.
/// `prepare` returns a boxed future so `read` can hold the processor as
/// `dyn ImageProcessor`.
pub trait ImageProcessor: Send + Sync {
    /// The image, prepared to fit `limits`, or `None` when it cannot be
    /// decoded or made to fit.
    fn prepare<'a>(
        &'a self,
        bytes: &'a [u8],
        mime_type: &'a str,
        limits: ImageLimits,
    ) -> BoxFuture<'a, Option<PreparedImage>>;
}

/// Formats every provider takes inline; others, such as BMP, need converting.
pub(crate) const INLINE_IMAGE_TYPES: [&str; 4] =
    ["image/png", "image/jpeg", "image/gif", "image/webp"];

const BASE64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// Standard base64 of `bytes`.
pub(crate) fn to_base64(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let a = chunk[0];
        let b = chunk.get(1).copied();
        let c = chunk.get(2).copied();
        let sextet = |value: u8| char::from(BASE64[usize::from(value & 63)]);
        out.push(sextet(a >> 2));
        out.push(sextet(((a & 3) << 4) | (b.unwrap_or(0) >> 4)));
        out.push(b.map_or('=', |b| sextet(((b & 15) << 2) | (c.unwrap_or(0) >> 6))));
        out.push(c.map_or('=', sextet));
    }
    out
}

/// The length of the base64 of `byte_length` bytes.
pub(crate) const fn base64_length(byte_length: u64) -> u64 {
    byte_length.div_ceil(3) * 4
}
