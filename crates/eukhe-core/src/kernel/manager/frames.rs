//! The bounded kernel-to-host protocol (docs/harness.md S3; model
//! `bend/sandbox.bend`, `serve`): the host decides, the kernel executes.
//!
//! The stdout reader cuts the kernel's byte stream into frames
//! ([`FrameSplitter`]) and asks the [`Gate`] about each one, in order. The
//! gate is the one place that decides:
//!
//! - a host request within [`MAX_PROTOCOL_LINE_BYTES`], with a fresh id and
//!   a type the host serves, is served: only such a frame reaches a handler,
//!   and the handler's reply is its one reply;
//! - a host request over the limit, of a type the host does not serve, or
//!   with an id seen before, is refused: it gets one error reply at once
//!   and does nothing (a seen id's reply has the status `duplicate`, which
//!   the runtime drops: see [`Refusal::reply`]);
//! - other events are served (they answer the host's own requests and
//!   need no reply), and an oversized stream or display event is dropped
//!   with a diagnostic;
//! - a frame the host cannot answer (not UTF-8, not a protocol frame, or
//!   oversized with no host-request header) is a [`ProtocolFault`]: the
//!   stream is unrecoverable and the protocol repair replaces the kernel.
//!
//! The limits are the constants below.

use std::collections::{HashSet, VecDeque};
use std::ops::ControlFlow;

use serde_json::Value;

use crate::kernel::protocol::{parse_event, Event};

/// The largest protocol line. The largest legit frame is an attachment
/// display event, base64 capped at `MAX_ATTACHMENT_DATA_CHARS`, and the
/// runtime caps `display` and `host_request` payloads at 16 MiB
/// (`repl.py` `_PAYLOAD_CAP`): a longer line is refused or dropped, never
/// buffered.
pub(crate) const MAX_PROTOCOL_LINE_BYTES: usize = 32 * 1024 * 1024;
/// How much of an oversized line the gate reads for its header: the
/// runtime writes `event` and `id` first (`repl.py` `_send`).
pub(crate) const FRAME_HEAD_BYTES: usize = 4096;
/// Runtime-minted host-request ids never repeat; the bound only guards a
/// misbehaving runtime from growing the seen-id set forever.
pub(crate) const MAX_HANDLED_HOST_REQUEST_IDS: usize = 1024;

/// One frame of the kernel's stream, as the splitter cuts it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RawFrame<'a> {
    /// A whole line within the limit, without its newline.
    Line(&'a [u8]),
    /// A line over the limit, seen when it passed the limit: its first
    /// bytes (at most [`FRAME_HEAD_BYTES`]). The splitter drops the rest
    /// of it, up to its newline.
    Oversize(&'a [u8]),
}

/// Cuts the kernel's byte stream into newline-terminated frames, holding
/// at most `max` bytes of one frame. A blank line is not a frame.
pub(crate) struct FrameSplitter {
    max: usize,
    /// The newline-free tail of earlier reads.
    tail: Vec<u8>,
    /// The rest of an oversized line is being dropped.
    skipping: bool,
}

impl FrameSplitter {
    pub(crate) fn new(max: usize) -> Self {
        Self {
            max,
            tail: Vec::new(),
            skipping: false,
        }
    }

    /// Cut `bytes` (the next read) into frames, in order; `on_frame` may
    /// stop the cut. Each byte is scanned once.
    pub(crate) fn feed(
        &mut self,
        mut bytes: &[u8],
        on_frame: &mut impl FnMut(RawFrame<'_>) -> ControlFlow<()>,
    ) -> ControlFlow<()> {
        while !bytes.is_empty() {
            let newline = bytes.iter().position(|&b| b == b'\n');
            if self.skipping {
                match newline {
                    Some(at) => {
                        self.skipping = false;
                        bytes = &bytes[at + 1..];
                        continue;
                    }
                    None => return ControlFlow::Continue(()),
                }
            }
            let Some(at) = newline else {
                if self.tail.len() + bytes.len() > self.max {
                    let head = self.take_head(bytes);
                    self.skipping = true;
                    return on_frame(RawFrame::Oversize(&head));
                }
                self.tail.extend_from_slice(bytes);
                return ControlFlow::Continue(());
            };
            let (line, rest) = (&bytes[..at], &bytes[at + 1..]);
            bytes = rest;
            let flow = if self.tail.len() + line.len() > self.max {
                let head = self.take_head(line);
                on_frame(RawFrame::Oversize(&head))
            } else if self.tail.is_empty() {
                if blank(line) {
                    ControlFlow::Continue(())
                } else {
                    on_frame(RawFrame::Line(line))
                }
            } else {
                self.tail.extend_from_slice(line);
                let flow = if blank(&self.tail) {
                    ControlFlow::Continue(())
                } else {
                    on_frame(RawFrame::Line(&self.tail))
                };
                self.tail.clear();
                flow
            };
            flow?;
        }
        ControlFlow::Continue(())
    }

    /// The first [`FRAME_HEAD_BYTES`] of the tail followed by `more`; the
    /// tail empties.
    fn take_head(&mut self, more: &[u8]) -> Vec<u8> {
        let mut head = std::mem::take(&mut self.tail);
        head.truncate(FRAME_HEAD_BYTES);
        let room = FRAME_HEAD_BYTES - head.len();
        head.extend_from_slice(&more[..room.min(more.len())]);
        head
    }
}

/// Whether `line` holds only whitespace.
fn blank(line: &[u8]) -> bool {
    line.iter().all(u8::is_ascii_whitespace)
}

/// Why the host refused a host request: the error its one reply carries.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum Refusal {
    #[error("host request frame exceeds the {max}-byte protocol line limit")]
    Oversize { max: usize },
    #[error("host request type \"{kind}\" is not available in this session")]
    KindNotServed { kind: String },
    #[error("host request payload must be an object with a string type")]
    NoKind,
    #[error("host request id \"{id}\" was already used")]
    DuplicateId { id: String },
}

impl Refusal {
    /// The `data` of the one reply to the refused frame. A duplicate id
    /// gets the status `duplicate`, not `error`: the reply goes out under
    /// the id of a request that may still be in flight, and the runtime
    /// (`repl.py` `_resolve_host_reply`) drops it, so it never settles that
    /// request's waiter in place of its real reply.
    pub(crate) fn reply(&self) -> Value {
        let status = match self {
            Self::DuplicateId { .. } => "duplicate",
            Self::Oversize { .. } | Self::KindNotServed { .. } | Self::NoKind => "error",
        };
        serde_json::json!({ "status": status, "error": self.to_string() })
    }
}

/// A frame the host cannot answer: the stream is unrecoverable.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum ProtocolFault {
    #[error("oversized protocol line: exceeds {max} bytes ({kind} frame)")]
    Oversize { kind: String, max: usize },
    #[error("protocol line is not UTF-8")]
    NotUtf8,
    #[error("{0}")]
    Malformed(String),
}

/// The gate's decision on one frame.
#[derive(Debug, PartialEq)]
pub(crate) enum Admission {
    /// The frame runs: a host request reaches its handler, another event
    /// its routing.
    Serve(Event),
    /// One error reply to `id`; nothing runs.
    Refuse { id: String, refusal: Refusal },
    /// An oversized event that answers nothing (stdout, stderr, display):
    /// nothing runs and nothing waits for it.
    Drop(ProtocolFault),
    /// The stream is unrecoverable.
    Fail(ProtocolFault),
}

/// The accept/serve decision for one kernel's stream: the limit and the
/// ids of the host requests seen so far.
pub(crate) struct Gate {
    max: usize,
    seen: HashSet<String>,
    order: VecDeque<String>,
}

impl Gate {
    pub(crate) fn new(max: usize) -> Self {
        Self {
            max,
            seen: HashSet::new(),
            order: VecDeque::new(),
        }
    }

    /// Record a host-request id; false when it was seen before.
    fn fresh(&mut self, id: &str) -> bool {
        if self.seen.contains(id) {
            return false;
        }
        self.seen.insert(id.to_string());
        self.order.push_back(id.to_string());
        while self.seen.len() > MAX_HANDLED_HOST_REQUEST_IDS {
            let Some(oldest) = self.order.pop_front() else {
                break;
            };
            self.seen.remove(&oldest);
        }
        true
    }

    /// Decide on `frame`; `serves` says whether the host serves a host
    /// request type.
    pub(crate) fn admit(
        &mut self,
        frame: RawFrame<'_>,
        serves: &impl Fn(&str) -> bool,
    ) -> Admission {
        match frame {
            RawFrame::Line(bytes) => {
                let Ok(line) = std::str::from_utf8(bytes) else {
                    return Admission::Fail(ProtocolFault::NotUtf8);
                };
                match parse_event(line) {
                    Ok(Event::HostRequest { id, data }) => {
                        if !self.fresh(&id) {
                            return Admission::Refuse {
                                refusal: Refusal::DuplicateId { id: id.clone() },
                                id,
                            };
                        }
                        let kind = data
                            .as_object()
                            .and_then(|map| map.get("type"))
                            .and_then(Value::as_str)
                            .filter(|kind| !kind.is_empty());
                        match kind {
                            Some(kind) if serves(kind) => {
                                Admission::Serve(Event::HostRequest { id, data })
                            }
                            Some(kind) => Admission::Refuse {
                                refusal: Refusal::KindNotServed {
                                    kind: kind.to_string(),
                                },
                                id,
                            },
                            None => Admission::Refuse {
                                id,
                                refusal: Refusal::NoKind,
                            },
                        }
                    }
                    Ok(event) => Admission::Serve(event),
                    Err(reason) => Admission::Fail(ProtocolFault::Malformed(reason)),
                }
            }
            RawFrame::Oversize(head) => {
                let (kind, id) = frame_header(head);
                match (kind, id) {
                    (Some("host_request"), Some(id)) if self.fresh(id) => Admission::Refuse {
                        id: id.to_string(),
                        refusal: Refusal::Oversize { max: self.max },
                    },
                    (Some("host_request"), Some(id)) => Admission::Refuse {
                        id: id.to_string(),
                        refusal: Refusal::DuplicateId { id: id.to_string() },
                    },
                    (Some(kind @ ("stdout" | "stderr" | "display")), _) => {
                        Admission::Drop(ProtocolFault::Oversize {
                            kind: kind.to_string(),
                            max: self.max,
                        })
                    }
                    (kind, _) => Admission::Fail(ProtocolFault::Oversize {
                        kind: kind.unwrap_or("unknown").to_string(),
                        max: self.max,
                    }),
                }
            }
        }
    }
}

/// The `event` and `id` of a frame from its first bytes: the runtime
/// writes `{"event":"<kind>","id":"<id>",...` (compact separators, keys in
/// insertion order). An id with an escape is not read.
fn frame_header(head: &[u8]) -> (Option<&str>, Option<&str>) {
    // A head cut inside a multi-byte character reads up to the cut.
    let text = match std::str::from_utf8(head) {
        Ok(text) => text,
        Err(error) => std::str::from_utf8(&head[..error.valid_up_to()]).unwrap_or_default(),
    };
    let Some(rest) = text.strip_prefix(r#"{"event":""#) else {
        return (None, None);
    };
    let Some((kind, rest)) = rest.split_once('"') else {
        return (None, None);
    };
    let id = rest
        .strip_prefix(r#","id":""#)
        .and_then(|rest| rest.split_once('"'))
        .map(|(id, _)| id)
        .filter(|id| !id.is_empty() && !id.contains('\\'));
    (Some(kind), id)
}

#[cfg(test)]
mod bridge;

#[cfg(test)]
mod tests {
    use super::*;

    /// Every frame `bytes` makes when fed in `chunk`-byte reads, owned,
    /// with whether it was over the limit.
    fn frames(max: usize, bytes: &[u8], chunk: usize) -> Vec<(Vec<u8>, bool)> {
        let mut splitter = FrameSplitter::new(max);
        let mut out = Vec::new();
        for part in bytes.chunks(chunk) {
            let _ = splitter.feed(part, &mut |frame| {
                out.push(match frame {
                    RawFrame::Line(line) => (line.to_vec(), false),
                    RawFrame::Oversize(head) => (head.to_vec(), true),
                });
                ControlFlow::Continue(())
            });
        }
        out
    }

    #[test]
    fn the_splitter_cuts_lines_the_same_in_any_read_size() {
        let stream = b"a\nbbbbbbbbbbbb\n\n  \ncc\nddddddddddddddd";
        let expected = vec![
            (b"a".to_vec(), false),
            (b"bbbbbbbbbb".to_vec(), true),
            (b"cc".to_vec(), false),
            (b"dddddddddd".to_vec(), true),
        ];
        for chunk in [1, 3, 64] {
            let got = frames(10, stream, chunk);
            // An oversized line is seen when it passes the limit: how much
            // of it was read then depends on the read size.
            let normalized: Vec<_> = got
                .into_iter()
                .map(|(head, oversize)| {
                    if oversize {
                        (head[..10].to_vec(), true)
                    } else {
                        (head, false)
                    }
                })
                .collect();
            assert_eq!(normalized, expected, "read size {chunk}");
        }
    }

    #[test]
    fn an_oversized_host_request_is_refused_by_id_and_the_next_frame_is_served() {
        let pad = "x".repeat(200);
        let stream = format!(
            "{{\"event\":\"host_request\",\"id\":\"h1\",\"data\":{{\"type\":\"a\",\"pad\":\"{pad}\"}}}}\n\
             {{\"event\":\"host_request\",\"id\":\"h2\",\"data\":{{\"type\":\"a\"}}}}\n\
             {{\"event\":\"host_request\",\"id\":\"h3\",\"data\":{{\"type\":\"b\"}}}}\n\
             {{\"event\":\"host_request\",\"id\":\"h2\",\"data\":{{\"type\":\"a\"}}}}\n\
             {{\"event\":\"stdout\",\"id\":null,\"text\":\"{pad}\"}}\n\
             {{\"event\":\"stdout\",\"id\":null,\"text\":\"ok\"}}\n"
        );
        let mut gate = Gate::new(100);
        let mut splitter = FrameSplitter::new(100);
        let mut decided = Vec::new();
        for part in stream.as_bytes().chunks(7) {
            let _ = splitter.feed(part, &mut |frame| {
                decided.push(gate.admit(frame, &|kind| kind == "a"));
                ControlFlow::Continue(())
            });
        }
        assert_eq!(
            decided,
            vec![
                Admission::Refuse {
                    id: "h1".into(),
                    refusal: Refusal::Oversize { max: 100 },
                },
                Admission::Serve(Event::HostRequest {
                    id: "h2".into(),
                    data: serde_json::json!({"type": "a"}),
                }),
                Admission::Refuse {
                    id: "h3".into(),
                    refusal: Refusal::KindNotServed { kind: "b".into() },
                },
                Admission::Refuse {
                    id: "h2".into(),
                    refusal: Refusal::DuplicateId { id: "h2".into() },
                },
                Admission::Drop(ProtocolFault::Oversize {
                    kind: "stdout".into(),
                    max: 100,
                }),
                Admission::Serve(Event::Stdout {
                    id: None,
                    text: "ok".into(),
                }),
            ]
        );
    }

    #[test]
    fn an_oversized_frame_without_a_host_request_header_is_a_fault() {
        let mut gate = Gate::new(4);
        let decided = gate.admit(RawFrame::Oversize(b"xxxxx"), &|_| true);
        assert_eq!(
            decided,
            Admission::Fail(ProtocolFault::Oversize {
                kind: "unknown".into(),
                max: 4,
            })
        );
    }

    /// A frame that repeats the id of a request still in flight never
    /// reaches a handler, and its one reply is `duplicate`, not `error`:
    /// the runtime drops it, so it cannot settle the first request in
    /// place of that request's real reply.
    #[test]
    fn a_repeated_id_of_a_request_in_flight_gets_a_duplicate_reply_and_no_handler() {
        let pad = "x".repeat(200);
        let stream = format!(
            "{{\"event\":\"host_request\",\"id\":\"h1\",\"data\":{{\"type\":\"a\"}}}}\n\
             {{\"event\":\"host_request\",\"id\":\"h1\",\"data\":{{\"type\":\"a\"}}}}\n\
             {{\"event\":\"host_request\",\"id\":\"h1\",\"data\":{{\"type\":\"a\",\"pad\":\"{pad}\"}}}}\n\
             {{\"event\":\"host_request\",\"id\":\"h2\",\"data\":{{\"type\":\"b\"}}}}\n"
        );
        let mut gate = Gate::new(100);
        let mut splitter = FrameSplitter::new(100);
        let mut served = Vec::new();
        let mut replies = Vec::new();
        let _ = splitter.feed(stream.as_bytes(), &mut |frame| {
            match gate.admit(frame, &|kind| kind == "a") {
                Admission::Serve(Event::HostRequest { id, .. }) => served.push(id),
                Admission::Refuse { id, refusal } => replies.push((id, refusal.reply())),
                other => panic!("unexpected admission {other:?}"),
            }
            ControlFlow::Continue(())
        });
        let duplicate = serde_json::json!({
            "status": "duplicate",
            "error": "host request id \"h1\" was already used",
        });
        assert_eq!(
            (served, replies),
            (
                vec!["h1".to_owned()],
                vec![
                    ("h1".to_owned(), duplicate.clone()),
                    ("h1".to_owned(), duplicate),
                    (
                        "h2".to_owned(),
                        serde_json::json!({
                            "status": "error",
                            "error": "host request type \"b\" is not available in this session",
                        })
                    ),
                ]
            )
        );
    }
}
