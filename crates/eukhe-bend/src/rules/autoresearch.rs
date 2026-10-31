//! Autoresearch's decisions (port of oh-my-pi autoresearch; spec/README.md
//! X1, X2): the model `bend/autoresearch/`, stepper entry
//! `bend/ffi_autoresearch.bend`, laws `laws/autoresearch.bend`.
//!
//! The lab lives in the compiled core: which runs a log may keep (only a
//! passed run whose parsed metric beats every kept run of the segment that
//! is not flagged), what each log does to the tree (keep commits, the
//! others reset), the segment's baseline, best and confidence, and when a
//! segment reached its cap. The host sends each event as it happens and
//! does what the outcome says; a refusal leaves the lab unchanged and its
//! text tells the model what to do instead.

use std::fmt;

use crate::wire::{Reader, WireError, Writer};
use crate::{Entry, Error, Stepper};

/// Which way the primary metric improves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    Lower,
    Higher,
}

/// What a logged run became.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    /// Kept: its changes are committed.
    Keep,
    /// Discarded: the tree goes back to HEAD.
    Discard,
    /// The benchmark failed (non-zero exit or timeout).
    Crash,
    /// The benchmark passed, but the checks failed.
    ChecksFailed,
}

/// Whether the autoresearch loop runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    On,
    Off,
}

/// An exact decimal metric, as a `METRIC <name>=<value>` line printed it,
/// in canonical form (no leading zero digit, no trailing zero after the
/// point, zero not negative); at most 15 significant digits. Only the
/// core makes one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Metric {
    negative: bool,
    digits: u64,
    scale: u32,
}

impl Metric {
    /// Below zero.
    #[must_use]
    pub fn negative(&self) -> bool {
        self.negative
    }

    /// The significant digits as one number: 125 for `-12.5`.
    #[must_use]
    pub fn digits(&self) -> u64 {
        self.digits
    }

    /// How many of the digits follow the point: 1 for `-12.5`.
    #[must_use]
    pub fn scale(&self) -> u32 {
        self.scale
    }
}

impl fmt::Display for Metric {
    /// The canonical text: `0`, `3`, `-12.5`, `0.005`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let digits = self.digits.to_string();
        if self.negative {
            f.write_str("-")?;
        }
        let scale = usize::try_from(self.scale).unwrap_or(usize::MAX);
        if scale == 0 {
            f.write_str(&digits)
        } else if digits.len() > scale {
            let (int, frac) = digits.split_at(digits.len() - scale);
            write!(f, "{int}.{frac}")
        } else {
            write!(f, "0.{}{digits}", "0".repeat(scale - digits.len()))
        }
    }
}

/// The experiment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Config {
    pub name: String,
    pub goal: String,
    /// The primary metric's name, as its `METRIC` lines spell it.
    pub metric: String,
    pub unit: String,
    pub direction: Direction,
    pub secondary: Vec<String>,
    pub scope: Vec<String>,
    pub off_limits: Vec<String>,
    /// The most runs a segment logs; then the step stops the loop.
    pub max_iterations: Option<u32>,
}

/// What happens to the lab.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    /// `autoresearch.init()`: the configuration, whether it opens a new
    /// segment, whether the benchmark harness exists.
    Init {
        config: Config,
        new_segment: bool,
        harness: bool,
    },
    /// A run starts.
    Start { run: u32 },
    /// A line of its output.
    Line { text: String },
    /// It ended.
    Finish { exit_code: i32, timed_out: bool },
    /// `autoresearch.log()`.
    Log {
        status: Status,
        description: String,
        justification: Option<String>,
        /// How many changed paths leave the scope.
        deviations: u32,
    },
    /// A logged run is flagged: its metric no longer counts.
    Flag { run: u32, reason: String },
    /// The user turned the loop on or off.
    SetMode(Mode),
}

/// What the host does to the tree after an accepted event.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Effect {
    Nothing,
    /// Commit the run's changes.
    Commit,
    /// Restore the tree to HEAD.
    Reset,
}

/// An accepted event: its effect, and whether the segment reached its cap
/// (the mode is then Off).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Outcome {
    pub effect: Effect,
    pub stopped: bool,
}

/// A refused event: the lab did not change; the text says what to do
/// instead.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refusal {
    pub text: String,
}

/// A run, as a snapshot shows it.
// Four independent facts the snapshot reports as they are (a run may be
// finished and not passed, logged and flagged, abandoned before it
// finished); an enum would fold facts the host reads one by one.
#[allow(clippy::struct_excessive_bools)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunRow {
    pub id: u32,
    pub segment: u32,
    /// None: pending, or abandoned.
    pub status: Option<Status>,
    pub abandoned: bool,
    pub finished: bool,
    /// The primary metric its output printed (the last value).
    pub metric: Option<Metric>,
    /// The other metrics it printed, in first-seen order, last value each.
    pub metrics: Vec<(String, Metric)>,
    /// Exit 0, no timeout.
    pub passed: bool,
    pub flagged: bool,
    pub description: String,
}

/// The lab's state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Snapshot {
    pub config: Option<Config>,
    pub segment: u32,
    pub mode: Mode,
    /// Every run, oldest first; the pending one last.
    pub runs: Vec<RunRow>,
    pub pending: Option<u32>,
    /// The segment's first kept run that is not flagged.
    pub baseline: Option<Metric>,
    /// The segment's last kept run that is not flagged: every keep beats
    /// all kept runs before it.
    pub best: Option<Metric>,
    /// How many runs the segment logged (flagged ones too).
    pub logged_in_segment: u32,
    /// |best - baseline| / MAD of the segment's metrics, in tenths.
    pub confidence_tenths: Option<u32>,
}

/// The lab, kept in the compiled core.
#[derive(Debug)]
pub struct Lab {
    stepper: Stepper,
}

/// The request tag of a snapshot.
const SNAPSHOT: u32 = 7;

impl Lab {
    /// A lab with no experiment and no run; the host replays its event log
    /// through [`Lab::step`].
    ///
    /// # Errors
    ///
    /// A failure of the compiled core ([`Error`]): only an inconsistent
    /// build.
    pub fn open() -> Result<Lab, Error> {
        let (stepper, reply) = Stepper::open(Entry::Autoresearch, "")?;
        let mut reader = Reader::reply(&reply)?;
        if !reader.bool()? {
            return Err(WireError::Malformed {
                at: 0,
                expected: "an open lab",
            }
            .into());
        }
        reader.end()?;
        Ok(Lab { stepper })
    }

    /// One event: its outcome, or a refusal that leaves the lab as it was.
    ///
    /// # Errors
    ///
    /// A string longer than the wire carries, or a failure of the compiled
    /// core ([`Error`]).
    pub fn step(&mut self, event: &Event) -> Result<Result<Outcome, Refusal>, Error> {
        let mut request = Writer::new();
        put_event(&mut request, event);
        let request = request.finish()?;
        let reply = self.stepper.step(&request)?;
        Ok(read_answer(&reply)?)
    }

    /// The lab's state.
    ///
    /// # Errors
    ///
    /// A failure of the compiled core ([`Error`]): only an inconsistent
    /// build.
    pub fn snapshot(&mut self) -> Result<Snapshot, Error> {
        let request = Writer::new().tag(SNAPSHOT).finish()?;
        let reply = self.stepper.step(&request)?;
        Ok(read_snapshot(&reply)?)
    }
}

fn put_strs(w: &mut Writer, xs: &[String]) {
    w.count(xs.len());
    for x in xs {
        w.str(x);
    }
}

fn put_config(w: &mut Writer, c: &Config) {
    w.str(&c.name).str(&c.goal).str(&c.metric).str(&c.unit);
    w.tag(match c.direction {
        Direction::Lower => 0,
        Direction::Higher => 1,
    });
    put_strs(w, &c.secondary);
    put_strs(w, &c.scope);
    put_strs(w, &c.off_limits);
    match c.max_iterations {
        None => w.none(),
        Some(n) => w.some().u32(n),
    };
}

fn status_tag(s: Status) -> u32 {
    match s {
        Status::Keep => 0,
        Status::Discard => 1,
        Status::Crash => 2,
        Status::ChecksFailed => 3,
    }
}

fn put_event(w: &mut Writer, e: &Event) {
    match e {
        Event::Init {
            config,
            new_segment,
            harness,
        } => {
            w.tag(0);
            put_config(w, config);
            w.bool(*new_segment).bool(*harness);
        }
        Event::Start { run } => {
            w.tag(1).u32(*run);
        }
        Event::Line { text } => {
            w.tag(2).str(text);
        }
        Event::Finish {
            exit_code,
            timed_out,
        } => {
            w.tag(3)
                .bool(*exit_code < 0)
                .u32(exit_code.unsigned_abs())
                .bool(*timed_out);
        }
        Event::Log {
            status,
            description,
            justification,
            deviations,
        } => {
            w.tag(4).tag(status_tag(*status)).str(description);
            match justification {
                None => w.none(),
                Some(text) => w.some().str(text),
            };
            w.u32(*deviations);
        }
        Event::Flag { run, reason } => {
            w.tag(5).u32(*run).str(reason);
        }
        Event::SetMode(mode) => {
            w.tag(6).tag(match mode {
                Mode::On => 0,
                Mode::Off => 1,
            });
        }
    }
}

fn read_answer(reply: &str) -> Result<Result<Outcome, Refusal>, WireError> {
    let mut r = Reader::reply(reply)?;
    let answer = if r.tag_of(2, "an answer: taken or refused")? == 0 {
        let effect = match r.tag_of(3, "an effect")? {
            0 => Effect::Nothing,
            1 => Effect::Commit,
            // `tag_of` answers a tag below 3: this is 2.
            _ => Effect::Reset,
        };
        let stopped = r.bool()?;
        Ok(Outcome { effect, stopped })
    } else {
        Err(Refusal {
            text: r.str()?.to_string(),
        })
    };
    r.end()?;
    Ok(answer)
}

fn get_strs(r: &mut Reader<'_>) -> Result<Vec<String>, WireError> {
    let n = r.count()?;
    (0..n).map(|_| r.str().map(str::to_string)).collect()
}

fn get_config(r: &mut Reader<'_>) -> Result<Config, WireError> {
    let name = r.str()?.to_string();
    let goal = r.str()?.to_string();
    let metric = r.str()?.to_string();
    let unit = r.str()?.to_string();
    let direction = if r.tag_of(2, "a direction")? == 0 {
        Direction::Lower
    } else {
        Direction::Higher
    };
    let secondary = get_strs(r)?;
    let scope = get_strs(r)?;
    let off_limits = get_strs(r)?;
    let max_iterations = if r.maybe()? { Some(r.u32()?) } else { None };
    Ok(Config {
        name,
        goal,
        metric,
        unit,
        direction,
        secondary,
        scope,
        off_limits,
        max_iterations,
    })
}

fn get_status(r: &mut Reader<'_>) -> Result<Status, WireError> {
    Ok(match r.tag_of(4, "a status")? {
        0 => Status::Keep,
        1 => Status::Discard,
        2 => Status::Crash,
        // `tag_of` answers a tag below 4: this is 3.
        _ => Status::ChecksFailed,
    })
}

/// A metric: its sign, its digits (each a `Nat` below 10, at most 15 of
/// them: the core's canonical form), its scale.
fn get_metric(r: &mut Reader<'_>) -> Result<Metric, WireError> {
    let negative = r.bool()?;
    let count = r.count()?;
    if count > 15 {
        return Err(WireError::Malformed {
            at: 0,
            expected: "a metric of at most 15 digits",
        });
    }
    let mut digits: u64 = 0;
    for _ in 0..count {
        let d = r.nat()?;
        if d > 9 {
            return Err(WireError::Malformed {
                at: 0,
                expected: "a decimal digit",
            });
        }
        digits = digits * 10 + d;
    }
    let scale = r.u32()?;
    Ok(Metric {
        negative,
        digits,
        scale,
    })
}

fn get_maybe_metric(r: &mut Reader<'_>) -> Result<Option<Metric>, WireError> {
    if r.maybe()? {
        Ok(Some(get_metric(r)?))
    } else {
        Ok(None)
    }
}

fn get_row(r: &mut Reader<'_>) -> Result<RunRow, WireError> {
    let id = r.u32()?;
    let segment = r.u32()?;
    let status = if r.maybe()? {
        Some(get_status(r)?)
    } else {
        None
    };
    let abandoned = r.bool()?;
    let finished = r.bool()?;
    let metric = get_maybe_metric(r)?;
    let n = r.count()?;
    let metrics = (0..n)
        .map(|_| Ok((r.str()?.to_string(), get_metric(r)?)))
        .collect::<Result<Vec<_>, WireError>>()?;
    let passed = r.bool()?;
    let flagged = r.bool()?;
    let description = r.str()?.to_string();
    Ok(RunRow {
        id,
        segment,
        status,
        abandoned,
        finished,
        metric,
        metrics,
        passed,
        flagged,
        description,
    })
}

fn read_snapshot(reply: &str) -> Result<Snapshot, WireError> {
    let mut r = Reader::reply(reply)?;
    let config = if r.maybe()? {
        Some(get_config(&mut r)?)
    } else {
        None
    };
    let segment = r.u32()?;
    let mode = if r.tag_of(2, "a mode")? == 0 {
        Mode::On
    } else {
        Mode::Off
    };
    let n = r.count()?;
    let runs = (0..n)
        .map(|_| get_row(&mut r))
        .collect::<Result<Vec<_>, WireError>>()?;
    let pending = if r.maybe()? { Some(r.u32()?) } else { None };
    let baseline = get_maybe_metric(&mut r)?;
    let best = get_maybe_metric(&mut r)?;
    let logged_in_segment = r.u32()?;
    let confidence_tenths = if r.maybe()? { Some(r.u32()?) } else { None };
    r.end()?;
    Ok(Snapshot {
        config,
        segment,
        mode,
        runs,
        pending,
        baseline,
        best,
        logged_in_segment,
        confidence_tenths,
    })
}

#[cfg(test)]
mod tests {
    use super::{
        Config, Direction, Effect, Event, Lab, Metric, Mode, Outcome, Refusal, RunRow, Snapshot,
        Status,
    };

    fn config() -> Config {
        Config {
            name: "speed".to_string(),
            goal: "faster parse".to_string(),
            metric: "ms".to_string(),
            unit: "ms".to_string(),
            direction: Direction::Lower,
            secondary: vec!["mem".to_string()],
            scope: vec!["src".to_string()],
            off_limits: Vec::new(),
            max_iterations: Some(4),
        }
    }

    fn metric(negative: bool, digits: u64, scale: u32) -> Metric {
        Metric {
            negative,
            digits,
            scale,
        }
    }

    /// What a step should answer.
    enum Want {
        /// Taken with this effect, not stopped.
        Took(Effect),
        /// Taken with this effect, and the segment reached its cap.
        Stop(Effect),
        /// Refused with this text.
        No(&'static str),
    }

    impl Want {
        fn answer(&self) -> Result<Outcome, Refusal> {
            match self {
                Want::Took(effect) => Ok(Outcome {
                    effect: *effect,
                    stopped: false,
                }),
                Want::Stop(effect) => Ok(Outcome {
                    effect: *effect,
                    stopped: true,
                }),
                Want::No(text) => Err(Refusal {
                    text: (*text).to_string(),
                }),
            }
        }
    }

    fn check(lab: &mut Lab, steps: Vec<(Event, Want)>) {
        for (event, want) in steps {
            assert_eq!(lab.step(&event).unwrap(), want.answer(), "{event:?}");
        }
    }

    fn line(text: &str) -> Event {
        Event::Line {
            text: text.to_string(),
        }
    }

    fn log(status: Status, justification: Option<&str>, deviations: u32) -> Event {
        Event::Log {
            status,
            description: format!("{status:?}"),
            justification: justification.map(str::to_string),
            deviations,
        }
    }

    fn finish(exit_code: i32) -> Event {
        Event::Finish {
            exit_code,
            timed_out: false,
        }
    }

    fn init(new_segment: bool, harness: bool) -> Event {
        Event::Init {
            config: config(),
            new_segment,
            harness,
        }
    }

    fn flag(run: u32) -> Event {
        Event::Flag {
            run,
            reason: "noise".to_string(),
        }
    }

    fn row(id: u32, status: Status, value: Metric, passed: bool) -> RunRow {
        RunRow {
            id,
            segment: 0,
            status: Some(status),
            abandoned: false,
            finished: true,
            metric: Some(value),
            metrics: Vec::new(),
            passed,
            flagged: false,
            description: format!("{status:?}"),
        }
    }

    /// Four runs of a capped segment: refusals, keeps that must beat every
    /// kept run, the cap that stops the loop.
    fn capped_session() -> Vec<(Event, Want)> {
        use Effect::{Commit, Nothing, Reset};
        vec![
            (
                Event::Start { run: 1 },
                Want::No("autoresearch: no experiment yet; call autoresearch.init() first"),
            ),
            (
                init(false, false),
                Want::No("autoresearch.init: build the benchmark harness first (a script that exits 0 and prints METRIC <name>=<value>), run it once, then call autoresearch.init() again"),
            ),
            (init(false, true), Want::Took(Nothing)),
            (
                Event::Start { run: 2 },
                Want::No("autoresearch.run: the next run is 1"),
            ),
            (Event::Start { run: 1 }, Want::Took(Nothing)),
            (line("compiling"), Want::Took(Nothing)),
            (line("METRIC ms=10"), Want::Took(Nothing)),
            (line("METRIC ms=12.50"), Want::Took(Nothing)),
            (line("METRIC\tmem=3 "), Want::Took(Nothing)),
            (finish(0), Want::Took(Nothing)),
            (log(Status::Keep, None, 0), Want::Took(Commit)),
            (Event::Start { run: 2 }, Want::Took(Nothing)),
            (line("METRIC ms=13"), Want::Took(Nothing)),
            (finish(0), Want::Took(Nothing)),
            (
                log(Status::Keep, None, 0),
                Want::No("autoresearch.log: 13 is not better than the best kept 12.5 (lower is better); log discard"),
            ),
            (
                log(Status::Crash, None, 0),
                Want::No("autoresearch.log: the run passed; log keep, discard or checks_failed"),
            ),
            (log(Status::Discard, None, 0), Want::Took(Reset)),
            (Event::Start { run: 3 }, Want::Took(Nothing)),
            (line("METRIC ms=11"), Want::Took(Nothing)),
            (finish(-1), Want::Took(Nothing)),
            (
                log(Status::Keep, None, 0),
                Want::No("autoresearch.log: the run failed (a non-zero exit or a timeout), so it cannot be kept; log crash or discard"),
            ),
            (log(Status::Crash, None, 0), Want::Took(Reset)),
            (Event::Start { run: 4 }, Want::Took(Nothing)),
            (line("METRIC ms=-0.5"), Want::Took(Nothing)),
            (finish(0), Want::Took(Nothing)),
            (
                log(Status::Keep, None, 2),
                Want::No("autoresearch.log: the run changed files outside the scope; a keep needs a justification"),
            ),
            (
                log(Status::Keep, Some("the parser moved"), 2),
                Want::Stop(Commit),
            ),
        ]
    }

    /// A session through the compiled core: the capped segment's snapshot,
    /// a flag that drops a run from the best, a new segment that abandons
    /// the pending run (the rule itself is pinned by
    /// `laws/autoresearch/`).
    #[test]
    fn a_session_runs_in_the_core() {
        let mut lab = Lab::open().unwrap();
        check(&mut lab, capped_session());
        let mut first = row(1, Status::Keep, metric(false, 125, 1), true);
        first.metrics = vec![("mem".to_string(), metric(false, 3, 0))];
        let mut snapshot = Snapshot {
            config: Some(config()),
            segment: 0,
            mode: Mode::Off,
            runs: vec![
                first,
                row(2, Status::Discard, metric(false, 13, 0), true),
                row(3, Status::Crash, metric(false, 11, 0), false),
                row(4, Status::Keep, metric(true, 5, 1), true),
            ],
            pending: None,
            baseline: Some(metric(false, 125, 1)),
            best: Some(metric(true, 5, 1)),
            logged_in_segment: 4,
            // median 11.75, MAD 1, |-0.5 - 12.5| = 13
            confidence_tenths: Some(130),
        };
        assert_eq!(lab.snapshot().unwrap(), snapshot);

        check(
            &mut lab,
            vec![
                (
                    flag(9),
                    Want::No("autoresearch.flag: there is no logged run 9"),
                ),
                (flag(4), Want::Took(Effect::Nothing)),
            ],
        );
        snapshot.runs[3].flagged = true;
        snapshot.best = Some(metric(false, 125, 1));
        snapshot.confidence_tenths = None;
        assert_eq!(lab.snapshot().unwrap(), snapshot);

        check(
            &mut lab,
            vec![
                (Event::Start { run: 5 }, Want::Took(Effect::Nothing)),
                (init(true, true), Want::Took(Effect::Nothing)),
            ],
        );
        snapshot.runs.push(RunRow {
            id: 5,
            segment: 0,
            status: None,
            abandoned: true,
            finished: false,
            metric: None,
            metrics: Vec::new(),
            passed: false,
            flagged: false,
            description: String::new(),
        });
        snapshot.segment = 1;
        snapshot.mode = Mode::On;
        snapshot.baseline = None;
        snapshot.best = None;
        snapshot.logged_in_segment = 0;
        assert_eq!(lab.snapshot().unwrap(), snapshot);
    }

    /// The deviations are measured from the median of all metrics, the
    /// smallest included: keeps of 2, 1 and 0 (median 1, MAD 1) put the
    /// best 2 MADs from the baseline (a running minimum taken against the
    /// baseline once answered none here; `confidence_exact`).
    #[test]
    fn confidence_counts_from_every_metric() {
        let mut lab = Lab::open().unwrap();
        let mut steps = vec![(init(false, true), Want::Took(Effect::Nothing))];
        for (run, value) in [(1, "2"), (2, "1"), (3, "0")] {
            steps.push((Event::Start { run }, Want::Took(Effect::Nothing)));
            steps.push((
                line(&format!("METRIC ms={value}")),
                Want::Took(Effect::Nothing),
            ));
            steps.push((finish(0), Want::Took(Effect::Nothing)));
            steps.push((log(Status::Keep, None, 0), Want::Took(Effect::Commit)));
        }
        check(&mut lab, steps);
        assert_eq!(lab.snapshot().unwrap().confidence_tenths, Some(20));
    }

    /// The text of a metric is the core's: the one its refusals show.
    #[test]
    fn a_metric_prints_as_the_core_prints_it() {
        let shown: Vec<String> = [
            metric(false, 0, 0),
            metric(false, 3, 0),
            metric(true, 125, 1),
            metric(false, 5, 3),
            metric(false, 30, 0),
        ]
        .iter()
        .map(ToString::to_string)
        .collect();
        assert_eq!(shown, ["0", "3", "-12.5", "0.005", "30"]);
        let mut lab = Lab::open().unwrap();
        let mut cfg = config();
        cfg.direction = Direction::Higher;
        for event in [
            Event::Init {
                config: cfg,
                new_segment: false,
                harness: true,
            },
            Event::Start { run: 1 },
            line("METRIC ms=0.0050"),
            finish(0),
            log(Status::Keep, None, 0),
            Event::Start { run: 2 },
            line("METRIC ms=-000.00500"),
            finish(0),
        ] {
            assert!(lab.step(&event).unwrap().is_ok(), "{event:?}");
        }
        let best = metric(false, 5, 3);
        let worse = metric(true, 5, 3);
        assert_eq!(
            lab.step(&log(Status::Keep, None, 0)).unwrap(),
            Err(Refusal {
                text: format!(
                    "autoresearch.log: {worse} is not better than the best kept {best} (higher is better); log discard"
                )
            })
        );
    }
}
