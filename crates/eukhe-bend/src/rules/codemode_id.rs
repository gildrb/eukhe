//! The identifiers of code mode (`bend/codemode_id.bend`, entry
//! `bend/ffi_codemode_id.bend`; `laws/codemode_id.bend`): the identifier a
//! script uses for a tool, and whether a text already is one. Each function
//! encodes its text, calls [`Entry::CodemodeId`] and decodes the reply.

use crate::wire::{Reader, Writer};
use crate::{call, Entry, Error};

/// The identifier a code-mode script uses for the tool named `name`: each
/// char a JavaScript identifier may not hold at its place becomes `_` (the
/// first may be an ASCII letter, `_` or `$`; a later one also an ASCII
/// digit); `""` is `_` (`Ci.of`).
///
/// # Errors
///
/// [`Error::Wire`] when `name` is past [`crate::wire::STR_MAX`] chars; else
/// only from an inconsistent build (see [`crate::expect_core`]).
pub fn identifier(name: &str) -> Result<String, Error> {
    let mut request = Writer::new();
    request.tag(0).str(name);
    let reply = call(Entry::CodemodeId, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let identifier = reply.str()?.to_string();
    reply.end()?;
    Ok(identifier)
}

/// Whether `text` is an identifier of code mode: not empty, an ASCII letter,
/// `_` or `$` first, then also ASCII digits (`Ci.test`).
///
/// # Errors
///
/// As [`identifier`].
pub fn is_identifier(text: &str) -> Result<bool, Error> {
    let mut request = Writer::new();
    request.tag(1).str(text);
    let reply = call(Entry::CodemodeId, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let is = reply.bool()?;
    reply.end()?;
    Ok(is)
}

#[cfg(test)]
mod tests {
    use super::{identifier, is_identifier};

    #[test]
    fn the_codec_carries_each_question_through_the_core() {
        assert_eq!(identifier("1st.tool😀").unwrap(), "_st_tool_");
        assert_eq!(identifier("").unwrap(), "_");
        assert!(is_identifier("$x_1").unwrap());
        assert!(!is_identifier("my-tool").unwrap());
    }
}
