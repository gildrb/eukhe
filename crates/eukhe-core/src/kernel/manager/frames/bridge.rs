//! The bridge between the kernel frame gate ([`super::FrameSplitter`],
//! [`super::Gate`]) and its Bend model (`bend/sandbox.bend`, `serve`; the
//! laws in `PROOF.bend`): both run the same scenarios and must print the
//! same transcript, byte for byte.
//!
//! A scenario is a size limit, the host-request kinds the host serves,
//! and a stream of host-request frames (`bridge/bridge_sandbox.bend`
//! documents the format). The driver writes each frame as the runtime
//! does, cuts the stream into reads of random sizes, and prints the
//! gate's answer to each frame and the frames it served.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::ops::ControlFlow;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};

use super::{Admission, FrameSplitter, Gate, Refusal};
use crate::kernel::protocol::Event;

/// The kinds of a scenario: host-request types `k0` to `k5`.
const KINDS: u64 = 6;

/// A case the scenarios must reach, so that the bridge checks every rule
/// of the model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Case {
    /// A frame within the limit, of an allowed kind.
    Served,
    /// A frame over the limit.
    Oversize,
    /// A frame within the limit, of a kind the host does not allow.
    KindRefused,
    /// A frame exactly at the limit.
    AtLimit,
}

/// One scenario: its events and the Rust transcript.
fn scenario(rng: &mut Rng, reached: &mut BTreeSet<Case>) -> (String, String) {
    let max = rng.range(80, 300) as usize;
    let allowed: Vec<u64> = (0..KINDS).filter(|_| rng.chance(50)).collect();
    let mut events = format!("m {max}\na");
    for kind in &allowed {
        write!(events, " {kind}").unwrap();
    }
    events.push('\n');
    let mut stream = Vec::new();
    for id in 0..rng.range(1, 12) {
        let kind = rng.below(KINDS);
        let head =
            format!(r#"{{"event":"host_request","id":"{id}","data":{{"type":"k{kind}","pad":""#);
        let tail = r#""}}"#;
        // Mostly near the limit, so that frames land on both sides of it.
        let target = if rng.chance(15) {
            max
        } else {
            (max as u64 + rng.range(0, 120)).saturating_sub(60) as usize
        };
        let pad = target.saturating_sub(head.len() + tail.len());
        let line = format!("{head}{}{tail}", "x".repeat(pad));
        writeln!(events, "f {id} {} {kind}", line.len()).unwrap();
        reached.insert(match (line.len().cmp(&max), allowed.contains(&kind)) {
            (std::cmp::Ordering::Greater, _) => Case::Oversize,
            (std::cmp::Ordering::Equal, _) => Case::AtLimit,
            (std::cmp::Ordering::Less, true) => Case::Served,
            (std::cmp::Ordering::Less, false) => Case::KindRefused,
        });
        stream.extend_from_slice(line.as_bytes());
        stream.push(b'\n');
    }
    let serves = |kind: &str| {
        kind.strip_prefix('k')
            .and_then(|n| n.parse::<u64>().ok())
            .is_some_and(|n| allowed.contains(&n))
    };
    let mut splitter = FrameSplitter::new(max);
    let mut gate = Gate::new(max);
    let (mut transcript, mut ran) = (String::new(), String::new());
    let mut rest = stream.as_slice();
    while !rest.is_empty() {
        let (read, after) = rest.split_at((rng.range(1, 97) as usize).min(rest.len()));
        rest = after;
        let _ = splitter.feed(read, &mut |frame| {
            match gate.admit(frame, &serves) {
                Admission::Serve(Event::HostRequest { id, .. }) => {
                    writeln!(transcript, "r ok {id}").unwrap();
                    write!(ran, " {id}").unwrap();
                }
                Admission::Refuse {
                    id,
                    refusal: Refusal::Oversize { .. } | Refusal::KindNotServed { .. },
                } => writeln!(transcript, "r err {id}").unwrap(),
                unexpected @ (Admission::Serve(
                    Event::Ready { .. }
                    | Event::Stdout { .. }
                    | Event::Stderr { .. }
                    | Event::Result { .. }
                    | Event::Display { .. }
                    | Event::Error { .. }
                    | Event::Done { .. },
                )
                | Admission::Refuse {
                    refusal: Refusal::NoKind | Refusal::DuplicateId { .. },
                    ..
                }
                | Admission::Drop(_)
                | Admission::Fail(_)) => {
                    panic!("the gate answered a host request with {unexpected:?}")
                }
            }
            ControlFlow::Continue(())
        });
    }
    writeln!(transcript, "x{ran}").unwrap();
    (events, transcript)
}

#[test]
fn the_rust_frame_gate_equals_the_bend_model() {
    let mut rng = Rng(0x5eed_5a4d_b0c5_0003);
    let mut reached = BTreeSet::new();
    let scenarios: Vec<Scenario> = (0..200)
        .map(|at| {
            let (events, transcript) = scenario(&mut rng, &mut reached);
            Scenario {
                name: format!("frames {at}"),
                events,
                transcript,
            }
        })
        .collect();
    compare("bridge/bridge_sandbox.bend", scenarios);
    // The scenarios reach every rule of the model.
    assert_eq!(
        reached,
        BTreeSet::from([
            Case::Served,
            Case::Oversize,
            Case::KindRefused,
            Case::AtLimit,
        ])
    );
}
