//! Pixel size from the header of base64 image data: decodes just enough of
//! the payload to parse a PNG, JPEG, GIF or WebP header; the channel and
//! alpha facts those headers carry are dropped, nothing here prices them.

use super::image::ImageSize;

/// Enough decoded bytes to reach a JPEG SOF marker behind typical EXIF/ICC
/// segments; PNG/GIF/WebP need only the first 30 bytes. A multiple of 4 so
/// the base64 slice decodes cleanly: `4 * ceil(64 KiB / 3)`.
const HEADER_BASE64_CHARS: usize = 4 * (64 * 1024usize).div_ceil(3);

/// Pixel size read from the header of base64-encoded image data; `None`
/// when the data is empty, not a PNG/JPEG/GIF/WebP, or its header carries
/// no non-zero size.
#[must_use]
pub fn base64_image_size(base64: &str) -> Option<ImageSize> {
    if base64.is_empty() {
        return None;
    }
    let header = decode_base64_prefix(base64, HEADER_BASE64_CHARS);
    let metadata = parse_image_metadata(&header)?;
    match (metadata.width, metadata.height) {
        (Some(width), Some(height)) if width > 0 && height > 0 => Some(ImageSize { width, height }),
        _ => None,
    }
}

/// Decodes the first `max_chars` characters of `input` the way Node's
/// `Buffer.from(…, "base64")` does: the standard and URL-safe alphabets,
/// other characters (whitespace) skipped, decoding stopped at the first
/// `=`, and a trailing partial byte dropped.
fn decode_base64_prefix(input: &str, max_chars: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(max_chars / 4 * 3);
    let mut bits: u32 = 0;
    let mut bit_count = 0;
    for byte in input.bytes().take(max_chars) {
        let sextet = match byte {
            b'A'..=b'Z' => byte - b'A',
            b'a'..=b'z' => byte - b'a' + 26,
            b'0'..=b'9' => byte - b'0' + 52,
            b'+' | b'-' => 62,
            b'/' | b'_' => 63,
            b'=' => break,
            _ => continue,
        };
        bits = (bits << 6) | u32::from(sextet);
        bit_count += 6;
        if bit_count >= 8 {
            bit_count -= 8;
            #[allow(clippy::cast_possible_truncation)] // masked to the low eight bits
            out.push(((bits >> bit_count) & 0xff) as u8);
            bits &= (1 << bit_count) - 1;
        }
    }
    out
}

/// The size facts a header carries; a recognized format whose header is cut
/// short has neither.
struct ImageMetadata {
    width: Option<u32>,
    height: Option<u32>,
}

impl ImageMetadata {
    const UNSIZED: Self = Self {
        width: None,
        height: None,
    };

    const fn sized(width: u32, height: u32) -> Self {
        Self {
            width: Some(width),
            height: Some(height),
        }
    }
}

const PNG_MAGIC: &[u8] = &[0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a];
const JPEG_MAGIC: &[u8] = &[0xff, 0xd8, 0xff];

fn magic_equals(header: &[u8], offset: usize, magic: &[u8]) -> bool {
    header.get(offset..offset + magic.len()) == Some(magic)
}

fn u16_be(header: &[u8], offset: usize) -> u16 {
    u16::from_be_bytes([header[offset], header[offset + 1]])
}

fn u16_le(header: &[u8], offset: usize) -> u16 {
    u16::from_le_bytes([header[offset], header[offset + 1]])
}

fn u32_be(header: &[u8], offset: usize) -> u32 {
    u32::from_be_bytes([
        header[offset],
        header[offset + 1],
        header[offset + 2],
        header[offset + 3],
    ])
}

fn u32_le(header: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes([
        header[offset],
        header[offset + 1],
        header[offset + 2],
        header[offset + 3],
    ])
}

fn u24_le(header: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes([header[offset], header[offset + 1], header[offset + 2], 0])
}

fn parse_png(header: &[u8]) -> Option<ImageMetadata> {
    if !magic_equals(header, 0, PNG_MAGIC) {
        return None;
    }
    if !magic_equals(header, 12, b"IHDR") || header.len() < 26 {
        return Some(ImageMetadata::UNSIZED);
    }
    Some(ImageMetadata::sized(u32_be(header, 16), u32_be(header, 20)))
}

fn parse_jpeg(header: &[u8]) -> Option<ImageMetadata> {
    if !magic_equals(header, 0, JPEG_MAGIC) {
        return None;
    }
    let mut offset = 2;
    while offset + 9 < header.len() {
        if header[offset] != 0xff {
            offset += 1;
            continue;
        }
        let mut marker_offset = offset + 1;
        while marker_offset < header.len() && header[marker_offset] == 0xff {
            marker_offset += 1;
        }
        if marker_offset >= header.len() {
            break;
        }
        let marker = header[marker_offset];
        let segment_offset = marker_offset + 1;
        if matches!(marker, 0xd8 | 0xd9 | 0x01 | 0xd0..=0xd7) {
            offset = segment_offset;
            continue;
        }
        if segment_offset + 1 >= header.len() {
            break;
        }
        let segment_length = usize::from(u16_be(header, segment_offset));
        if segment_length < 2 {
            break;
        }
        let start_of_frame = matches!(marker, 0xc0..=0xcf) && !matches!(marker, 0xc4 | 0xc8 | 0xcc);
        if start_of_frame {
            if segment_offset + 7 >= header.len() {
                break;
            }
            let height = u16_be(header, segment_offset + 3);
            let width = u16_be(header, segment_offset + 5);
            return Some(ImageMetadata::sized(u32::from(width), u32::from(height)));
        }
        offset = segment_offset + segment_length;
    }
    Some(ImageMetadata::UNSIZED)
}

fn parse_gif(header: &[u8]) -> Option<ImageMetadata> {
    if !magic_equals(header, 0, b"GIF87a") && !magic_equals(header, 0, b"GIF89a") {
        return None;
    }
    if header.len() < 10 {
        return Some(ImageMetadata::UNSIZED);
    }
    Some(ImageMetadata::sized(
        u32::from(u16_le(header, 6)),
        u32::from(u16_le(header, 8)),
    ))
}

fn parse_webp(header: &[u8]) -> Option<ImageMetadata> {
    if !magic_equals(header, 0, b"RIFF") || !magic_equals(header, 8, b"WEBP") {
        return None;
    }
    if header.len() < 30 {
        return Some(ImageMetadata::UNSIZED);
    }
    if magic_equals(header, 12, b"VP8X") {
        return Some(ImageMetadata::sized(
            u24_le(header, 24) + 1,
            u24_le(header, 27) + 1,
        ));
    }
    if magic_equals(header, 12, b"VP8L") {
        let bits = u32_le(header, 21);
        return Some(ImageMetadata::sized(
            (bits & 0x3fff) + 1,
            ((bits >> 14) & 0x3fff) + 1,
        ));
    }
    if magic_equals(header, 12, b"VP8 ") {
        return Some(ImageMetadata::sized(
            u32::from(u16_le(header, 26) & 0x3fff),
            u32::from(u16_le(header, 28) & 0x3fff),
        ));
    }
    Some(ImageMetadata::UNSIZED)
}

/// The first recognized format wins, sized or not.
fn parse_image_metadata(header: &[u8]) -> Option<ImageMetadata> {
    parse_png(header)
        .or_else(|| parse_jpeg(header))
        .or_else(|| parse_gif(header))
        .or_else(|| parse_webp(header))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn encode(bytes: &[u8]) -> String {
        const ALPHABET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
        let mut out = String::new();
        for chunk in bytes.chunks(3) {
            let padded = [
                chunk[0],
                *chunk.get(1).unwrap_or(&0),
                *chunk.get(2).unwrap_or(&0),
            ];
            let n = u32::from_be_bytes([0, padded[0], padded[1], padded[2]]);
            for i in 0..=chunk.len() {
                let index = usize::try_from((n >> (18 - 6 * i)) & 63).expect("six bits");
                out.push(char::from(ALPHABET[index]));
            }
            for _ in chunk.len()..3 {
                out.push('=');
            }
        }
        out
    }

    fn png(width: u32, height: u32) -> Vec<u8> {
        let mut bytes = PNG_MAGIC.to_vec();
        bytes.extend_from_slice(&13u32.to_be_bytes());
        bytes.extend_from_slice(b"IHDR");
        bytes.extend_from_slice(&width.to_be_bytes());
        bytes.extend_from_slice(&height.to_be_bytes());
        bytes.extend_from_slice(&[8, 6, 0, 0, 0]);
        bytes
    }

    #[test]
    fn decodes_like_node_buffers() {
        assert_eq!(decode_base64_prefix("aGVsbG8=", 100), b"hello");
        assert_eq!(decode_base64_prefix("aGVs\nbG8", 100), b"hello");
        assert_eq!(decode_base64_prefix("-_-_", 100), [0xfb, 0xff, 0xbf]);
        assert_eq!(decode_base64_prefix("aGVsbG8=", 4), b"hel");
        assert_eq!(encode(b"hello"), "aGVsbG8=");
    }

    #[test]
    fn reads_png_sizes() {
        assert_eq!(
            base64_image_size(&encode(&png(1568, 1562))),
            Some(ImageSize {
                width: 1568,
                height: 1562
            })
        );
        assert_eq!(base64_image_size(&encode(&png(0, 10))), None);
        assert_eq!(base64_image_size(""), None);
        assert_eq!(base64_image_size(&encode(PNG_MAGIC)), None);
    }

    #[test]
    fn reads_jpeg_sizes_behind_app_segments() {
        let mut jpeg = vec![0xff, 0xd8];
        // APP0 segment of 16 bytes, then a baseline SOF0.
        jpeg.extend_from_slice(&[0xff, 0xe0, 0x00, 0x10]);
        jpeg.extend_from_slice(&[0; 14]);
        jpeg.extend_from_slice(&[0xff, 0xc0, 0x00, 0x11, 0x08, 0x00, 0x08, 0x04, 0x4c, 0x03]);
        jpeg.extend_from_slice(&[0; 12]);
        assert_eq!(
            base64_image_size(&encode(&jpeg)),
            Some(ImageSize {
                width: 1100,
                height: 8
            })
        );
        // A JPEG cut before its frame header is recognized but unsized.
        assert_eq!(base64_image_size(&encode(&jpeg[..20])), None);
    }

    #[test]
    fn reads_gif_and_webp_sizes() {
        let mut gif = b"GIF89a".to_vec();
        gif.extend_from_slice(&[0x20, 0x03, 0x58, 0x02]);
        assert_eq!(
            base64_image_size(&encode(&gif)),
            Some(ImageSize {
                width: 800,
                height: 600
            })
        );

        let riff = |chunk: &[u8; 4], body: &[u8]| {
            let mut bytes = b"RIFF\0\0\0\0WEBP".to_vec();
            bytes.extend_from_slice(chunk);
            bytes.extend_from_slice(body);
            bytes.resize(30, 0);
            bytes
        };
        // VP8X: 24-bit little-endian sizes minus one at 24 and 27.
        let mut extended = [0u8; 14];
        extended[8..11].copy_from_slice(&[0x1f, 0x06, 0x00]);
        extended[11..14].copy_from_slice(&[0x19, 0x06, 0x00]);
        assert_eq!(
            base64_image_size(&encode(&riff(b"VP8X", &extended))),
            Some(ImageSize {
                width: 1568,
                height: 1562
            })
        );
        // VP8L: 14-bit sizes minus one packed after the 0x2f signature.
        let bits: u32 = 0x061f | (0x0619 << 14); // 1567, 1561
        let mut lossless = [0u8; 9];
        lossless[4] = 0x2f;
        lossless[5..9].copy_from_slice(&bits.to_le_bytes());
        assert_eq!(
            base64_image_size(&encode(&riff(b"VP8L", &lossless))),
            Some(ImageSize {
                width: 1568,
                height: 1562
            })
        );
        // Lossy VP8: 14-bit sizes at 26 and 28.
        let mut lossy = [0u8; 14];
        lossy[10..12].copy_from_slice(&1568u16.to_le_bytes());
        lossy[12..14].copy_from_slice(&1562u16.to_le_bytes());
        assert_eq!(
            base64_image_size(&encode(&riff(b"VP8 ", &lossy))),
            Some(ImageSize {
                width: 1568,
                height: 1562
            })
        );
        assert_eq!(base64_image_size(&encode(b"not an image at all")), None);
    }
}
