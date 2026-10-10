//! EXIF orientation of JPEG and WebP files, read from the bytes without
//! decoding the image. Port of `images/exif.ts`.

/// The EXIF orientation of a JPEG or WebP, 1 to 8; 1 when absent or
/// unreadable.
#[must_use]
pub fn exif_orientation(bytes: &[u8]) -> u16 {
    let Some(tiff) = tiff_start(bytes) else {
        return 1;
    };
    if tiff + 8 > bytes.len() {
        return 1;
    }
    let little = bytes[tiff] == 0x49 && bytes[tiff + 1] == 0x49;
    let u16_at = |at: usize| {
        let pair = [bytes[at], bytes[at + 1]];
        if little {
            u16::from_le_bytes(pair)
        } else {
            u16::from_be_bytes(pair)
        }
    };
    let quad = [
        bytes[tiff + 4],
        bytes[tiff + 5],
        bytes[tiff + 6],
        bytes[tiff + 7],
    ];
    let first = if little {
        u32::from_le_bytes(quad)
    } else {
        u32::from_be_bytes(quad)
    };
    let Some(directory) = usize::try_from(first)
        .ok()
        .and_then(|first| tiff.checked_add(first))
    else {
        return 1;
    };
    if directory + 2 > bytes.len() {
        return 1;
    }
    let entries = usize::from(u16_at(directory));
    for index in 0..entries {
        let entry = directory + 2 + index * 12;
        if entry + 12 > bytes.len() {
            return 1;
        }
        // Tag 0x0112 is Orientation, a SHORT whose value sits in the entry.
        if u16_at(entry) == 0x0112 {
            let value = u16_at(entry + 8);
            return if (1..=8).contains(&value) { value } else { 1 };
        }
    }
    1
}

/// Where the TIFF header of a JPEG's APP1 or a WebP's EXIF chunk starts;
/// `None` when there is none.
fn tiff_start(bytes: &[u8]) -> Option<usize> {
    if bytes.starts_with(&[0xff, 0xd8]) {
        let mut offset = 2;
        while offset + 4 <= bytes.len() {
            if bytes[offset] != 0xff {
                return None;
            }
            let marker = bytes[offset + 1];
            if marker == 0xff {
                offset += 1;
                continue;
            }
            if marker == 0xe1 && is_exif_header(bytes, offset + 4) {
                return Some(offset + 10);
            }
            offset += 2 + usize::from(u16::from_be_bytes([bytes[offset + 2], bytes[offset + 3]]));
        }
        return None;
    }
    if ascii(bytes, 0, "RIFF") && ascii(bytes, 8, "WEBP") {
        let mut offset: usize = 12;
        while offset + 8 <= bytes.len() {
            let size = u32::from_le_bytes([
                bytes[offset + 4],
                bytes[offset + 5],
                bytes[offset + 6],
                bytes[offset + 7],
            ]);
            // Some WebP files prefix the TIFF header with "Exif\0\0".
            if ascii(bytes, offset, "EXIF") {
                return Some(if is_exif_header(bytes, offset + 8) {
                    offset + 14
                } else {
                    offset + 8
                });
            }
            // RIFF chunks are padded to an even size. A size past the end
            // ends the walk, as the loop condition would.
            offset = usize::try_from(u64::from(size) + u64::from(size % 2) + 8)
                .ok()
                .and_then(|step| offset.checked_add(step))?;
        }
    }
    None
}

fn is_exif_header(bytes: &[u8], offset: usize) -> bool {
    ascii(bytes, offset, "Exif")
        && bytes.get(offset + 4) == Some(&0)
        && bytes.get(offset + 5) == Some(&0)
}

fn ascii(bytes: &[u8], offset: usize, text: &str) -> bool {
    bytes
        .get(offset..offset + text.len())
        .is_some_and(|slice| slice == text.as_bytes())
}
