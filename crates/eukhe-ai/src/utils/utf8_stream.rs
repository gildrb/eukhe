//! Streaming UTF-8 decoding (TS `TextDecoder` with `{ stream: true }`):
//! invalid sequences become U+FFFD, an incomplete trailing sequence waits
//! for the next chunk.

#[derive(Debug, Default)]
pub(crate) struct Utf8StreamDecoder {
    pending: Vec<u8>,
}

impl Utf8StreamDecoder {
    /// Decode `bytes` onto `out`, keeping an incomplete trailing sequence.
    pub(crate) fn decode_into(&mut self, bytes: &[u8], out: &mut String) {
        self.pending.extend_from_slice(bytes);
        let mut rest: &[u8] = &self.pending;
        loop {
            match std::str::from_utf8(rest) {
                Ok(text) => {
                    out.push_str(text);
                    rest = &[];
                    break;
                }
                Err(error) => {
                    let (valid, after) = rest.split_at(error.valid_up_to());
                    out.push_str(std::str::from_utf8(valid).unwrap_or_default());
                    let Some(length) = error.error_len() else {
                        rest = after;
                        break;
                    };
                    out.push(char::REPLACEMENT_CHARACTER);
                    rest = &after[length..];
                }
            }
        }
        let consumed = self.pending.len() - rest.len();
        self.pending.drain(..consumed);
    }

    /// [`Self::decode_into`] a new string.
    pub(crate) fn decode(&mut self, bytes: &[u8]) -> String {
        let mut out = String::new();
        self.decode_into(bytes, &mut out);
        out
    }

    /// `decoder.decode()` at end of input: a pending incomplete sequence
    /// becomes one U+FFFD.
    pub(crate) fn finish_into(&mut self, out: &mut String) {
        if !self.pending.is_empty() {
            self.pending.clear();
            out.push(char::REPLACEMENT_CHARACTER);
        }
    }

    /// [`Self::finish_into`] a new string.
    pub(crate) fn finish(&mut self) -> String {
        let mut out = String::new();
        self.finish_into(&mut out);
        out
    }
}
