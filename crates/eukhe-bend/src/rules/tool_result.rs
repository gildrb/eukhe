//! The blocks a tool result sends to a provider that takes only text in a
//! result marked as an error (`bend/tool_result.bend`, entry
//! `bend/ffi_tool_result.bend`; `laws/tool_result.bend`, spec
//! `spec/harness/tool_result.bend`): Anthropic refuses a `tool_result`
//! marked `is_error` that carries an image block, and the result stays in
//! the transcript, so every later request of the session fails. An error
//! result sends every text block unchanged and each image as one text
//! line, in order; a successful result sends its blocks unchanged.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// What a block of a tool result's content is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Block {
    Text,
    Image,
}

/// How one block of a tool result is sent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sent {
    /// As it is.
    Keep,
    /// As a text block holding this line.
    Line(String),
}

/// How each block of a tool result's content is sent, one answer per block
/// of `blocks`, in order: `is_error` is the result's error flag.
#[must_use]
pub fn sent(is_error: bool, blocks: &[Block]) -> Vec<Sent> {
    expect_core(Entry::ToolResult, sent_call(is_error, blocks))
}

fn sent_call(is_error: bool, blocks: &[Block]) -> Result<Vec<Sent>, Error> {
    let mut request = Writer::new();
    request.bool(is_error).count(blocks.len());
    for block in blocks {
        request.bool(match block {
            Block::Text => false,
            Block::Image => true,
        });
    }
    let reply = call(Entry::ToolResult, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    if reader.count()? != blocks.len() {
        return Err(WireError::Malformed {
            at: 0,
            expected: "one answer per block",
        }
        .into());
    }
    let mut answers = Vec::with_capacity(blocks.len());
    for _ in blocks {
        // tag_of refuses a tag past 1: 0 keeps the block, 1 holds a line.
        answers.push(if reader.tag_of(2, "a block's answer")? == 0 {
            Sent::Keep
        } else {
            Sent::Line(reader.str()?.to_owned())
        });
    }
    reader.end()?;
    Ok(answers)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The table comes from the compiled core: an error result sends its
    /// text as it is and each image as the omitted line, in order; a
    /// successful result keeps every block; an empty result sends nothing.
    #[test]
    fn the_core_sends_an_error_result_as_text_only() {
        let line = || Sent::Line("[image omitted: error result]".to_owned());
        assert_eq!(
            [
                sent(true, &[Block::Text, Block::Image]),
                sent(true, &[Block::Image, Block::Text, Block::Image]),
                sent(true, &[Block::Text, Block::Text]),
                sent(false, &[Block::Text, Block::Image]),
                sent(false, &[Block::Image]),
                sent(true, &[]),
            ],
            [
                vec![Sent::Keep, line()],
                vec![line(), Sent::Keep, line()],
                vec![Sent::Keep, Sent::Keep],
                vec![Sent::Keep, Sent::Keep],
                vec![Sent::Keep],
                vec![],
            ]
        );
    }
}
