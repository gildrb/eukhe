//! Image files a read shows as images: PNG and JPEG, recognized by their
//! signature, with the pixel size their header gives.

/// The format of a read image.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImageFormat {
    Png,
    Jpeg,
}

impl ImageFormat {
    #[must_use]
    pub fn mime_type(self) -> &'static str {
        match self {
            Self::Png => "image/png",
            Self::Jpeg => "image/jpeg",
        }
    }

    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Png => "PNG",
            Self::Jpeg => "JPEG",
        }
    }
}

/// A read image: its format, pixel size, and bytes as on disk.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImageView {
    pub format: ImageFormat,
    pub width: u32,
    pub height: u32,
    pub bytes: Vec<u8>,
}

const PNG_SIGNATURE: &[u8] = b"\x89PNG\r\n\x1a\n";

/// The format and pixel size of `bytes`, when they are a PNG or a JPEG
/// whose header gives a nonzero size.
pub(super) fn sniff(bytes: &[u8]) -> Option<(ImageFormat, u32, u32)> {
    let (format, width, height) = if bytes.starts_with(PNG_SIGNATURE) {
        // The first chunk of a PNG is `IHDR`: width, then height.
        (bytes.get(12..16)? == b"IHDR").then_some(())?;
        (ImageFormat::Png, be32(bytes, 16)?, be32(bytes, 20)?)
    } else if bytes.starts_with(&[0xFF, 0xD8, 0xFF]) {
        let (width, height) = jpeg_size(bytes)?;
        (ImageFormat::Jpeg, width, height)
    } else {
        return None;
    };
    (width > 0 && height > 0).then_some((format, width, height))
}

fn be16(bytes: &[u8], at: usize) -> Option<u32> {
    let pair = bytes.get(at..at + 2)?;
    Some(u32::from(u16::from_be_bytes([pair[0], pair[1]])))
}

fn be32(bytes: &[u8], at: usize) -> Option<u32> {
    let quad = bytes.get(at..at + 4)?;
    Some(u32::from_be_bytes([quad[0], quad[1], quad[2], quad[3]]))
}

/// Walk the JPEG markers to the first start-of-frame: height, then width.
fn jpeg_size(bytes: &[u8]) -> Option<(u32, u32)> {
    let mut at = 2;
    loop {
        // Fill bytes (0xFF) may precede a marker.
        while bytes.get(at) == Some(&0xFF) && bytes.get(at + 1) == Some(&0xFF) {
            at += 1;
        }
        if bytes.get(at) != Some(&0xFF) {
            return None;
        }
        let marker = *bytes.get(at + 1)?;
        match marker {
            0xC0..=0xC3 | 0xC5..=0xC7 | 0xC9..=0xCB | 0xCD..=0xCF => {
                return Some((be16(bytes, at + 7)?, be16(bytes, at + 5)?));
            }
            // Markers without a length: TEM, RSTn, SOI.
            0x01 | 0xD0..=0xD8 => at += 2,
            // End of image or of the scan headers: no frame came first.
            0xD9 | 0xDA => return None,
            _ => at += 2 + usize::try_from(be16(bytes, at + 2)?).ok()?,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn png(width: u32, height: u32) -> Vec<u8> {
        let mut bytes = PNG_SIGNATURE.to_vec();
        bytes.extend_from_slice(&13u32.to_be_bytes());
        bytes.extend_from_slice(b"IHDR");
        bytes.extend_from_slice(&width.to_be_bytes());
        bytes.extend_from_slice(&height.to_be_bytes());
        bytes.extend_from_slice(&[8, 6, 0, 0, 0]);
        bytes
    }

    /// SOI, an APP0 segment, then a baseline frame of `width`x`height`.
    fn jpeg(width: u16, height: u16) -> Vec<u8> {
        let mut bytes = vec![
            0xFF, 0xD8, 0xFF, 0xE0, 0x00, 0x04, 0x4A, 0x46, 0xFF, 0xC0, 0x00, 0x11, 8,
        ];
        bytes.extend_from_slice(&height.to_be_bytes());
        bytes.extend_from_slice(&width.to_be_bytes());
        bytes.extend_from_slice(&[3, 1, 0x22, 0, 2, 0x11, 1, 3, 0x11, 1]);
        bytes
    }

    #[test]
    fn png_and_jpeg_headers_give_format_and_size() {
        assert_eq!(
            [
                sniff(&png(1440, 900)),
                sniff(&jpeg(1568, 980)),
                sniff(&png(0, 900)),
                sniff(&png(1440, 900)[..20]),
                sniff(b"GIF89a\x01\x00\x01\x00"),
                sniff(&[0xFF, 0xD8, 0xFF, 0xD9]),
            ],
            [
                Some((ImageFormat::Png, 1440, 900)),
                Some((ImageFormat::Jpeg, 1568, 980)),
                None,
                None,
                None,
                None,
            ]
        );
    }
}
