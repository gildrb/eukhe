//! Decoding that matches `new TextDecoder().decode(bytes)` of the whole input
//! when the input arrives in pieces. Port of `env/decode.ts`.
//!
//! Node's streaming decoder with BOM handling can drop a U+FEFF that follows a
//! chunk boundary, not only a leading byte-order mark, so these decoders turn
//! BOM handling off and drop a leading mark themselves.

/// Where decoded text goes: a string, or only its UTF-8 length.
trait Utf8Sink {
    fn push_str(&mut self, text: &str);
    fn push_char(&mut self, character: char);
}

impl Utf8Sink for String {
    fn push_str(&mut self, text: &str) {
        String::push_str(self, text);
    }

    fn push_char(&mut self, character: char) {
        self.push(character);
    }
}

/// Counts the UTF-8 bytes of decoded text without building it.
struct ByteCount(usize);

impl Utf8Sink for ByteCount {
    fn push_str(&mut self, text: &str) {
        self.0 += text.len();
    }

    fn push_char(&mut self, character: char) {
        self.0 += character.len_utf8();
    }
}

/// A WHATWG UTF-8 decoder with BOM handling off (`ignoreBOM: true`): the JS
/// `new TextDecoder("utf-8", { ignoreBOM: true })`. Invalid input becomes
/// U+FFFD per maximal subpart, exactly as the WHATWG Encoding Standard
/// specifies.
#[derive(Clone, Debug)]
pub struct Utf8Decoder {
    code_point: u32,
    bytes_needed: u8,
    bytes_seen: u8,
    lower_boundary: u8,
    upper_boundary: u8,
}

impl Default for Utf8Decoder {
    fn default() -> Self {
        Self::new()
    }
}

impl Utf8Decoder {
    /// A decoder at the start of a stream.
    #[must_use]
    pub fn new() -> Self {
        Self {
            code_point: 0,
            bytes_needed: 0,
            bytes_seen: 0,
            lower_boundary: 0x80,
            upper_boundary: 0xbf,
        }
    }

    /// `decode(bytes, { stream: true })`: text for `bytes`, holding back an
    /// incomplete character.
    pub fn decode_chunk(&mut self, bytes: &[u8]) -> String {
        let mut text = String::with_capacity(bytes.len());
        self.run(bytes, &mut text);
        text
    }

    /// `decode()`: the end of the stream; an incomplete character becomes
    /// U+FFFD. The decoder is then ready for a new stream.
    pub fn finish(&mut self) -> String {
        let mut text = String::new();
        self.end(&mut text);
        text
    }

    /// `decode(bytes)` without `stream`: the chunk and the end of the stream.
    pub fn decode_all(&mut self, bytes: &[u8]) -> String {
        let mut text = String::with_capacity(bytes.len());
        self.run(bytes, &mut text);
        self.end(&mut text);
        text
    }

    /// UTF-8 length of what [`Utf8Decoder::decode_chunk`] would return.
    pub(crate) fn decode_chunk_len(&mut self, bytes: &[u8]) -> usize {
        let mut count = ByteCount(0);
        self.run(bytes, &mut count);
        count.0
    }

    /// UTF-8 length of what [`Utf8Decoder::finish`] would return.
    pub(crate) fn finish_len(&mut self) -> usize {
        let mut count = ByteCount(0);
        self.end(&mut count);
        count.0
    }

    fn reset(&mut self) {
        self.code_point = 0;
        self.bytes_needed = 0;
        self.bytes_seen = 0;
        self.lower_boundary = 0x80;
        self.upper_boundary = 0xbf;
    }

    fn end(&mut self, sink: &mut impl Utf8Sink) {
        if self.bytes_needed != 0 {
            self.reset();
            sink.push_char(char::REPLACEMENT_CHARACTER);
        }
    }

    fn run(&mut self, bytes: &[u8], sink: &mut impl Utf8Sink) {
        let mut rest = bytes;
        while !rest.is_empty() {
            if self.bytes_needed == 0 {
                // Valid runs decode at once; std validation is the same as WHATWG's.
                match std::str::from_utf8(rest) {
                    Ok(text) => {
                        sink.push_str(text);
                        return;
                    }
                    Err(error) => {
                        let (valid, invalid) = rest.split_at(error.valid_up_to());
                        if let Ok(text) = std::str::from_utf8(valid) {
                            sink.push_str(text);
                        }
                        rest = invalid;
                    }
                }
            }
            // Byte by byte until the decoder is between characters again.
            loop {
                let Some((&byte, tail)) = rest.split_first() else {
                    return;
                };
                if self.step(byte, sink) {
                    rest = tail;
                }
                if self.bytes_needed == 0 {
                    break;
                }
            }
        }
    }

    /// One step of the WHATWG UTF-8 decoder; returns whether `byte` was
    /// consumed (false: it must be processed again).
    fn step(&mut self, byte: u8, sink: &mut impl Utf8Sink) -> bool {
        if self.bytes_needed == 0 {
            match byte {
                0x00..=0x7f => sink.push_char(char::from(byte)),
                0xc2..=0xdf => {
                    self.bytes_needed = 1;
                    self.code_point = u32::from(byte & 0x1f);
                }
                0xe0..=0xef => {
                    if byte == 0xe0 {
                        self.lower_boundary = 0xa0;
                    }
                    if byte == 0xed {
                        self.upper_boundary = 0x9f;
                    }
                    self.bytes_needed = 2;
                    self.code_point = u32::from(byte & 0x0f);
                }
                0xf0..=0xf4 => {
                    if byte == 0xf0 {
                        self.lower_boundary = 0x90;
                    }
                    if byte == 0xf4 {
                        self.upper_boundary = 0x8f;
                    }
                    self.bytes_needed = 3;
                    self.code_point = u32::from(byte & 0x07);
                }
                _ => sink.push_char(char::REPLACEMENT_CHARACTER),
            }
            return true;
        }
        if byte < self.lower_boundary || byte > self.upper_boundary {
            self.reset();
            sink.push_char(char::REPLACEMENT_CHARACTER);
            return false;
        }
        self.lower_boundary = 0x80;
        self.upper_boundary = 0xbf;
        self.code_point = (self.code_point << 6) | u32::from(byte & 0x3f);
        self.bytes_seen += 1;
        if self.bytes_seen == self.bytes_needed {
            let code_point = self.code_point;
            self.reset();
            sink.push_char(char::from_u32(code_point).unwrap_or(char::REPLACEMENT_CHARACTER));
        }
        true
    }
}

/// A streaming decoder for a byte range; callers that start at the beginning
/// of a file skip a leading mark themselves.
#[must_use]
pub fn range_decoder() -> Utf8Decoder {
    Utf8Decoder::new()
}

/// Whether decoding the whole input drops its first three bytes as a
/// byte-order mark.
#[must_use]
pub fn starts_with_bom(first_bytes: &[u8]) -> bool {
    first_bytes.starts_with(&[0xef, 0xbb, 0xbf])
}

/// Decodes one stream chunk by chunk exactly like decoding all of it at once.
#[derive(Clone, Debug, Default)]
pub struct StreamDecoder {
    decoder: Utf8Decoder,
    started: bool,
}

impl StreamDecoder {
    /// A decoder at the start of a stream.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Text for `bytes`, holding back an incomplete character.
    pub fn decode(&mut self, bytes: &[u8]) -> String {
        let text = self.decoder.decode_chunk(bytes);
        self.strip_leading_mark(text)
    }

    /// The end of the stream: the TS `decode()` without bytes.
    pub fn finish(&mut self) -> String {
        let text = self.decoder.finish();
        self.strip_leading_mark(text)
    }

    fn strip_leading_mark(&mut self, text: String) -> String {
        if self.started || text.is_empty() {
            return text;
        }
        self.started = true;
        // U+FEFF encodes only as EF BB BF, so a leading U+FEFF is exactly a
        // byte-order mark at the stream's start.
        match text.strip_prefix('\u{feff}') {
            Some(rest) => rest.to_owned(),
            None => text,
        }
    }
}
