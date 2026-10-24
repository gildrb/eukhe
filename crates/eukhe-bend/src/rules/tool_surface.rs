//! The tool surface (`bend/tools.bend` sections 1 and 2, entry
//! `bend/ffi_tool_surface.bend`; `laws/tool_surface.bend`): the schema the
//! harness sends for a tool, and which tools a call through `dyn` reaches
//! as tools join and quit. The caller interns names as numbers (a schema's
//! intent parameter `i` is [`INTENT`]); each function encodes them, calls
//! [`Entry::ToolSurface`] and decodes the decision.

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

/// The number of a schema's intent parameter `i` (`Tl.intent`).
pub const INTENT: u64 = 0;

/// A tool schema as numbers: its parameters, in order, and its version.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Schema {
    pub params: Vec<u64>,
    pub version: u64,
}

/// The schema the harness sends for a tool that declares `declared`
/// (`Tl.build`).
#[must_use]
pub fn build(declared: &Schema) -> Schema {
    expect_core(Entry::ToolSurface, build_call(declared))
}

fn build_call(declared: &Schema) -> Result<Schema, Error> {
    let mut request = Writer::new();
    request.tag(0);
    nats(&mut request, &declared.params);
    request.nat(declared.version);
    let reply = call(Entry::ToolSurface, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let params = read_nats(&mut reader)?;
    let version = reader.nat()?;
    reader.end()?;
    Ok(Schema { params, version })
}

/// The dynamic tools (as the model keeps them) after `tool` joins
/// (`Tl.step` of `Join`).
#[must_use]
pub fn join(dynamic: &[u64], tool: u64) -> Vec<u64> {
    expect_core(Entry::ToolSurface, event_call(1, dynamic, tool))
}

/// The dynamic tools after `tool` quits (`Tl.step` of `Quit`).
#[must_use]
pub fn quit(dynamic: &[u64], tool: u64) -> Vec<u64> {
    expect_core(Entry::ToolSurface, event_call(2, dynamic, tool))
}

fn event_call(tag: u32, dynamic: &[u64], tool: u64) -> Result<Vec<u64>, Error> {
    let mut request = Writer::new();
    request.tag(tag);
    nats(&mut request, dynamic);
    request.nat(tool);
    let reply = call(Entry::ToolSurface, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let after = read_nats(&mut reader)?;
    reader.end()?;
    Ok(after)
}

/// Whether a call through `dyn` reaches `tool` (`Tl.dyn_call`).
#[must_use]
pub fn reaches(dynamic: &[u64], tool: u64) -> bool {
    expect_core(Entry::ToolSurface, reaches_call(dynamic, tool))
}

fn reaches_call(dynamic: &[u64], tool: u64) -> Result<bool, Error> {
    let mut request = Writer::new();
    request.tag(3);
    nats(&mut request, dynamic);
    request.nat(tool);
    let reply = call(Entry::ToolSurface, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let reached = reader.bool()?;
    reader.end()?;
    Ok(reached)
}

fn nats(request: &mut Writer, xs: &[u64]) {
    request.count(xs.len());
    for &x in xs {
        request.nat(x);
    }
}

fn read_nats(reader: &mut Reader<'_>) -> Result<Vec<u64>, Error> {
    let count = reader.count()?;
    let mut xs = Vec::with_capacity(count);
    for _ in 0..count {
        xs.push(reader.nat()?);
    }
    Ok(xs)
}

#[cfg(test)]
mod tests {
    use super::{build, join, quit, reaches, Schema};

    #[test]
    fn the_codec_carries_each_question_through_the_core() {
        let joined = join(&[4], 4);
        let left = quit(&[4, 2, 4], 4);
        assert_eq!(
            (
                build(&Schema {
                    params: vec![2, 3],
                    version: 0,
                }),
                build(&Schema {
                    params: vec![2, 0],
                    version: 5,
                }),
                joined.clone(),
                left.clone(),
                reaches(&joined, 4),
                reaches(&left, 4),
            ),
            (
                Schema {
                    params: vec![0, 2, 3],
                    version: 1,
                },
                Schema {
                    params: vec![2, 0],
                    version: 5,
                },
                vec![4, 4],
                vec![2],
                true,
                false,
            )
        );
    }
}
