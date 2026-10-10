//! Image type detection by content. Port of `tools/image.ts`.

use std::future::Future;

use super::image_processor::ImageSize;
use crate::env::FileError;

const PNG_SIGNATURE: [u8; 8] = [0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a];
/// Bytes every check except the APNG chunk walk needs: BMP reads up to offset
/// 29.
const HEADER_BYTES: u64 = 32;
const BLOCK_BYTES: u64 = 64 * 1024;

/// Positional reads of a file of `size` bytes.
///
/// Implementations return up to `length` bytes at `offset`, fewer only at the
/// end of the file, and fail with the [`FileError`] of the underlying read.
pub(crate) trait ByteSource: Sync {
    fn size(&self) -> u64;
    fn read(
        &self,
        offset: u64,
        length: u64,
    ) -> impl Future<Output = Result<Vec<u8>, FileError>> + Send;
}

/// [`detect_supported_image_mime_type`] of a whole file, reading only its
/// header and, for PNG, the chunk headers up to the first `acTL` or `IDAT`.
pub(crate) async fn detect_supported_image_mime_type_of<S: ByteSource>(
    source: &S,
) -> Result<Option<&'static str>, FileError> {
    let header = source.read(0, HEADER_BYTES).await?;
    if !header.starts_with(&PNG_SIGNATURE) {
        return Ok(detect_supported_image_mime_type(&header));
    }
    Ok((is_png(&header) && !is_animated_png_of(source).await?).then_some("image/png"))
}

/// `is_animated_png` over a file read in blocks.
async fn is_animated_png_of<S: ByteSource>(source: &S) -> Result<bool, FileError> {
    let size = source.size();
    let mut block: Vec<u8> = Vec::new();
    let mut block_start: u64 = 0;
    let mut offset = PNG_SIGNATURE.len() as u64;
    while offset + 8 <= size {
        if offset < block_start || offset + 8 > block_start + block.len() as u64 {
            block_start = offset;
            block = source.read(offset, BLOCK_BYTES).await?;
        }
        // `subarray` clamps to the bytes the read returned.
        let start = usize::try_from(offset - block_start)
            .unwrap_or(usize::MAX)
            .min(block.len());
        let chunk_header = &block[start..block.len().min(start + 8)];
        let chunk_length = read_uint32_be(chunk_header, 0);
        if starts_with_ascii(chunk_header, 4, "acTL") {
            return Ok(true);
        }
        if starts_with_ascii(chunk_header, 4, "IDAT") {
            return Ok(false);
        }
        // A JS number does not wrap: an overflow is past the end.
        let Some(next_offset) = (offset + 8 + 4).checked_add(chunk_length) else {
            return Ok(false);
        };
        if next_offset <= offset || next_offset > size {
            return Ok(false);
        }
        offset = next_offset;
    }
    Ok(false)
}

pub(crate) fn detect_supported_image_mime_type(buffer: &[u8]) -> Option<&'static str> {
    if buffer.starts_with(&[0xff, 0xd8, 0xff]) {
        return (buffer.get(3) != Some(&0xf7)).then_some("image/jpeg");
    }
    if buffer.starts_with(&PNG_SIGNATURE) {
        return (is_png(buffer) && !is_animated_png(buffer)).then_some("image/png");
    }
    if starts_with_ascii(buffer, 0, "GIF87a") || starts_with_ascii(buffer, 0, "GIF89a") {
        return Some("image/gif");
    }
    if starts_with_ascii(buffer, 0, "RIFF") && starts_with_ascii(buffer, 8, "WEBP") {
        return Some("image/webp");
    }
    if starts_with_ascii(buffer, 0, "BM") && is_bmp(buffer) {
        return Some("image/bmp");
    }
    None
}

/// The width and height an image of `mime_type` declares in its header,
/// without decoding it: PNG's IHDR, GIF's screen, WebP's VP8, VP8L, or VP8X
/// chunk, JPEG's first SOF segment. `None` when the header cannot be read.
pub(crate) fn image_dimensions(bytes: &[u8], mime_type: &str) -> Option<ImageSize> {
    let size = |width, height| Some(ImageSize { width, height });
    match mime_type {
        "image/png" if bytes.len() >= 24 => {
            size(read_uint32_be(bytes, 16), read_uint32_be(bytes, 20))
        }
        "image/gif" if bytes.len() >= 10 => {
            size(read_uint16_le(bytes, 6), read_uint16_le(bytes, 8))
        }
        "image/webp" if bytes.len() >= 30 => {
            if starts_with_ascii(bytes, 12, "VP8 ") {
                return size(
                    read_uint16_le(bytes, 26) & 0x3fff,
                    read_uint16_le(bytes, 28) & 0x3fff,
                );
            }
            if starts_with_ascii(bytes, 12, "VP8L") {
                let bits = read_uint32_le(bytes, 21);
                return size((bits & 0x3fff) + 1, ((bits >> 14) & 0x3fff) + 1);
            }
            if starts_with_ascii(bytes, 12, "VP8X") {
                let uint24 = |offset: usize| {
                    read_uint16_le(bytes, offset) + (byte_at(bytes, offset + 2) << 16)
                };
                return size(uint24(24) + 1, uint24(27) + 1);
            }
            None
        }
        "image/jpeg" => {
            let mut offset = 2;
            while offset + 9 <= bytes.len() {
                if bytes[offset] != 0xff {
                    return None;
                }
                let marker = bytes[offset + 1];
                if marker == 0xff {
                    offset += 1;
                    continue;
                }
                // SOF0 to SOF15, except DHT (C4), JPG (C8), and DAC (CC), which share the range.
                if (0xc0..=0xcf).contains(&marker) && ![0xc4, 0xc8, 0xcc].contains(&marker) {
                    return size(
                        read_uint16_be(bytes, offset + 7),
                        read_uint16_be(bytes, offset + 5),
                    );
                }
                // Not above `bytes.len()` plus 65537, so it fits.
                offset +=
                    2 + usize::try_from(read_uint16_be(bytes, offset + 2)).unwrap_or(usize::MAX);
            }
            None
        }
        _ => None,
    }
}

fn is_png(buffer: &[u8]) -> bool {
    buffer.len() >= 16
        && read_uint32_be(buffer, PNG_SIGNATURE.len()) == 13
        && starts_with_ascii(buffer, 12, "IHDR")
}

fn is_animated_png(buffer: &[u8]) -> bool {
    let mut offset = PNG_SIGNATURE.len();
    while offset + 8 <= buffer.len() {
        let chunk_length = read_uint32_be(buffer, offset);
        let chunk_type_offset = offset + 4;
        if starts_with_ascii(buffer, chunk_type_offset, "acTL") {
            return true;
        }
        if starts_with_ascii(buffer, chunk_type_offset, "IDAT") {
            return false;
        }
        let next_offset = offset as u64 + 8 + chunk_length + 4;
        if next_offset <= offset as u64 || next_offset > buffer.len() as u64 {
            return false;
        }
        // Not above `buffer.len()`, so it fits.
        offset = usize::try_from(next_offset).unwrap_or(usize::MAX);
    }
    false
}

fn is_bmp(buffer: &[u8]) -> bool {
    if buffer.len() < 26 {
        return false;
    }
    let declared_file_size = read_uint32_le(buffer, 2);
    let pixel_data_offset = read_uint32_le(buffer, 10);
    let dib_header_size = read_uint32_le(buffer, 14);
    if declared_file_size != 0 && declared_file_size < 26 {
        return false;
    }
    if pixel_data_offset < 14 + dib_header_size {
        return false;
    }
    if declared_file_size != 0 && pixel_data_offset >= declared_file_size {
        return false;
    }

    let (color_planes, bits_per_pixel) = if dib_header_size == 12 {
        (read_uint16_le(buffer, 22), read_uint16_le(buffer, 24))
    } else if (40..=124).contains(&dib_header_size) {
        if buffer.len() < 30 {
            return false;
        }
        (read_uint16_le(buffer, 26), read_uint16_le(buffer, 28))
    } else {
        return false;
    };
    color_planes == 1 && [1, 4, 8, 16, 24, 32].contains(&bits_per_pixel)
}

/// The byte at `offset`, or 0 past the end (the TS `buffer[offset] ?? 0`).
fn byte_at(buffer: &[u8], offset: usize) -> u64 {
    buffer.get(offset).copied().map_or(0, u64::from)
}

fn read_uint16_le(buffer: &[u8], offset: usize) -> u64 {
    byte_at(buffer, offset) + (byte_at(buffer, offset + 1) << 8)
}

fn read_uint16_be(buffer: &[u8], offset: usize) -> u64 {
    (byte_at(buffer, offset) << 8) + byte_at(buffer, offset + 1)
}

fn read_uint32_be(buffer: &[u8], offset: usize) -> u64 {
    byte_at(buffer, offset) * 0x0100_0000
        + (byte_at(buffer, offset + 1) << 16)
        + (byte_at(buffer, offset + 2) << 8)
        + byte_at(buffer, offset + 3)
}

fn read_uint32_le(buffer: &[u8], offset: usize) -> u64 {
    byte_at(buffer, offset)
        + (byte_at(buffer, offset + 1) << 8)
        + (byte_at(buffer, offset + 2) << 16)
        + byte_at(buffer, offset + 3) * 0x0100_0000
}

fn starts_with_ascii(buffer: &[u8], offset: usize, text: &str) -> bool {
    buffer
        .get(offset..offset + text.len())
        .is_some_and(|bytes| bytes == text.as_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_the_complete_gif87a_signature() {
        assert_eq!(
            detect_supported_image_mime_type(b"GIF87a"),
            Some("image/gif")
        );
    }

    #[test]
    fn detects_the_complete_gif89a_signature() {
        assert_eq!(
            detect_supported_image_mime_type(b"GIF89a"),
            Some("image/gif")
        );
    }

    fn chunk(kind: &str, length: u32) -> Vec<u8> {
        let mut bytes = length.to_be_bytes().to_vec();
        bytes.extend_from_slice(kind.as_bytes());
        bytes.resize(bytes.len() + length as usize + 4, 0);
        bytes
    }

    fn png(chunks: &[(&str, u32)]) -> Vec<u8> {
        let mut bytes = PNG_SIGNATURE.to_vec();
        for (kind, length) in chunks {
            bytes.extend(chunk(kind, *length));
        }
        bytes
    }

    struct Bytes(Vec<u8>);

    impl ByteSource for Bytes {
        fn size(&self) -> u64 {
            self.0.len() as u64
        }

        fn read(
            &self,
            offset: u64,
            length: u64,
        ) -> impl Future<Output = Result<Vec<u8>, FileError>> + Send {
            let start = usize::try_from(offset).unwrap().min(self.0.len());
            let end = usize::try_from(offset + length).unwrap().min(self.0.len());
            std::future::ready(Ok(self.0[start..end].to_vec()))
        }
    }

    /// The image half of the `tools-read-differential` case "detects animated
    /// PNGs whose acTL chunk lies far beyond the header": the bounded walk
    /// agrees with the whole-buffer check.
    #[tokio::test]
    async fn detects_animated_pngs_whose_actl_chunk_lies_far_beyond_the_header() {
        let animated = png(&[("IHDR", 13), ("iCCP", 200_000), ("acTL", 8), ("IDAT", 10)]);
        assert_eq!(detect_supported_image_mime_type(&animated), None);
        assert_eq!(
            detect_supported_image_mime_type_of(&Bytes(animated))
                .await
                .unwrap(),
            None
        );

        let still = png(&[("IHDR", 13), ("iCCP", 200_000), ("IDAT", 10), ("acTL", 8)]);
        assert_eq!(detect_supported_image_mime_type(&still), Some("image/png"));
        assert_eq!(
            detect_supported_image_mime_type_of(&Bytes(still))
                .await
                .unwrap(),
            Some("image/png")
        );
    }

    #[test]
    fn detects_jpeg_webp_and_bmp_headers() {
        assert_eq!(
            detect_supported_image_mime_type(&[0xff, 0xd8, 0xff]),
            Some("image/jpeg")
        );
        assert_eq!(
            detect_supported_image_mime_type(&[0xff, 0xd8, 0xff, 0xf7]),
            None
        );
        assert_eq!(
            detect_supported_image_mime_type(b"RIFF\0\0\0\0WEBP"),
            Some("image/webp")
        );
        let mut bmp = vec![0u8; 30];
        bmp[..2].copy_from_slice(b"BM");
        bmp[10] = 54;
        bmp[14] = 40;
        bmp[26] = 1;
        bmp[28] = 24;
        assert_eq!(detect_supported_image_mime_type(&bmp), Some("image/bmp"));
        bmp[28] = 3;
        assert_eq!(detect_supported_image_mime_type(&bmp), None);
    }
}
