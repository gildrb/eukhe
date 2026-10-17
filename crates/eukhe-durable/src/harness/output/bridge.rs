//! The bridge between the tool output bounder ([`OutputBuffer`] under a
//! [`Truncation`]) and the cap of its Bend model (`bend/job.bend`, whose
//! laws `PROOF.bend` proves): both run the same scenarios and must print
//! the same transcript, byte for byte.
//!
//! A scenario is a bounder scenario of `bend/bridge_stream.bend` (the file
//! documents the format): the cap (`Truncation::On` with that many bytes,
//! or the opt-out `Truncation::Off`), chunks of output, and the end of the
//! output. After each chunk and the end the driver prints the job as the
//! model does: the bytes the buffer keeps and the bytes it counts as
//! dropped. The chunks hold no newline and the line limit is far away, so
//! the byte cap is the only bound, as in the model; head and tail retention
//! both run.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;

use super::{OutputBuffer, OutputLimits, Truncation};
use crate::harness::types::{OutputRetain, ToolOutputChunk};
use crate::testing::bridge::{compare, Rng, Scenario};

/// One scenario as it runs: the buffer, whether the output ended, and both
/// texts.
struct Run {
    buffer: OutputBuffer,
    ended: bool,
    events: String,
    transcript: String,
}

impl Run {
    /// Print the job: what the buffer keeps and drops now.
    fn print(&mut self) {
        let bounded = self.buffer.snapshot();
        let state = if self.ended { "exited:0" } else { "live" };
        let _infallible = writeln!(
            self.transcript,
            "j {state} {} {}",
            bounded.text.len(),
            bounded.dropped_bytes
        );
    }

    /// `o N`: the bounder takes N bytes; an ended output takes none.
    fn out(&mut self, bytes: usize) {
        let _infallible = writeln!(self.events, "o {bytes}");
        if !self.ended {
            let chunk = "x".repeat(bytes);
            self.buffer
                .push(ToolOutputChunk::Text(&chunk), None)
                .unwrap();
        }
        self.print();
    }

    /// `e`: the output ends with exit code 0.
    fn end(&mut self) {
        self.events.push_str("e\n");
        if !self.ended {
            self.buffer.end();
            self.ended = true;
        }
        self.print();
    }
}

/// One scenario of 1 to 30 events under a cap of 0 to 60 bytes, or the
/// opt-out.
fn scenario(rng: &mut Rng) -> (String, String) {
    let (truncation, cap) = if rng.chance(20) {
        (Truncation::Off, "-".to_owned())
    } else {
        let max_bytes = usize::try_from(rng.range(0, 60)).unwrap();
        let retain = rng.pick(&[OutputRetain::Head, OutputRetain::Tail]).unwrap();
        let limits = OutputLimits {
            max_bytes,
            max_lines: 1_000_000,
            retain,
        };
        (Truncation::On(limits), max_bytes.to_string())
    };
    let mut run = Run {
        buffer: OutputBuffer::new(truncation),
        ended: false,
        events: format!("c {cap}\n"),
        transcript: String::new(),
    };
    for _ in 0..rng.range(1, 30) {
        if rng.chance(8) {
            run.end();
        } else {
            run.out(usize::try_from(rng.range(0, 25)).unwrap());
        }
    }
    (run.events, run.transcript)
}

#[test]
fn the_rust_output_bounder_equals_the_bend_model() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let scenarios: Vec<Scenario> = (0..300)
        .map(|at| {
            let (events, transcript) = scenario(&mut rng);
            Scenario {
                name: format!("bounder {at}"),
                events,
                transcript,
            }
        })
        .collect();
    compare("bend/bridge_stream.bend", scenarios);
}
