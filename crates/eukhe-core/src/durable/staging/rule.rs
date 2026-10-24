//! The staging rule, decided by the compiled Bend core (`bend/staging.bend`
//! and `bend/listing.bend`, entry `bend/ffi_staging.bend`; laws
//! `laws/staging.bend`, `laws/listing.bend`): the verdict of a publish, what
//! the sweep does with each entry of a directory and with a judged
//! leftover, and how the sessions directory is listed. The callers gather
//! the facts (names, entry types, lock probes, modification times, cwds)
//! and do the steps; each function here spells its request, calls
//! [`Entry::Staging`] and reads the reply.
//!
//! Every request is eukhe's own (each number saturated at the wire's
//! largest Nat), so a failed call can only mean an inconsistent build:
//! [`expect_core`] fails loud.

use std::time::{Duration, SystemTime, UNIX_EPOCH};

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::{call, expect_core, Entry, Error};

/// An entry's type, symlinks not followed (`Sg.Form`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Form {
    /// A directory; `main`: it holds `main.jsonl`, a file.
    Dir { main: bool },
    /// A regular file.
    File,
    /// A symlink or anything else.
    Other,
}

/// An entry of a directory listing: its name (`None`: not UTF-8) and type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Seen<'a> {
    pub(crate) name: Option<&'a str>,
    pub(crate) form: Form,
}

/// What the sweep does with an entry of a directory it lists (`Sg.Met`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Met {
    /// Keep it, do not enter it.
    Keep,
    /// A directory the walk enters.
    Descend,
    /// A staging directory or a tombstone: judge it.
    Leftover,
    /// A staging lock file whose directory is gone: judge it.
    Orphan,
}

/// What the sweep judges (`Sg.Cand`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Cand {
    /// A staging directory or a tombstone, its lock file beside it.
    Dir,
    /// A staging lock file whose directory is gone.
    Lock,
}

/// A lock probe (`Sg.Lock`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Probe {
    /// A live process holds the lock.
    Held,
    /// The sweep holds the lock now: no live process does.
    Free,
    /// No lock file is there.
    Absent,
}

/// What the sweep does with a judged entry (`Sg.Plan`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Plan {
    Keep,
    RemoveDir,
    RemoveDirAndLock,
    RemoveFile,
}

/// What an entry of the sessions directory is to the listing (`Ls.Pick`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Pick {
    Skip,
    /// A storage, listed under its name.
    Store(String),
    /// A legacy file not imported, listed under its stem.
    Legacy(String),
}

/// An entry of the sessions directory with what was read of it (`Ls.Obs`):
/// its cwd (`None`: it does not read) and the modification times of its
/// files.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Obs<'a> {
    pub(crate) seen: Seen<'a>,
    pub(crate) cwd: Option<&'a str>,
    pub(crate) times: Vec<SystemTime>,
}

/// A listed session (`Ls.Row`): the place of its entry in the request,
/// what it is, and its newest time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Row {
    pub(crate) at: usize,
    pub(crate) pick: Pick,
    pub(crate) time: SystemTime,
}

fn put_seen(w: &mut Writer, seen: Seen<'_>) {
    match seen.name {
        Some(name) => w.tag(0).str(name),
        None => w.tag(1),
    };
    match seen.form {
        Form::Dir { main } => w.tag(0).bool(main),
        Form::File => w.tag(1),
        Form::Other => w.tag(2),
    };
}

fn put_seens(w: &mut Writer, seens: &[Seen<'_>]) {
    w.count(seens.len());
    for seen in seens {
        put_seen(w, *seen);
    }
}

/// A time as seconds and nanoseconds after the epoch; a time before it is
/// the epoch, seconds saturate at the wire's largest Nat.
fn put_time(w: &mut Writer, time: SystemTime) {
    let since = time.duration_since(UNIX_EPOCH).unwrap_or(Duration::ZERO);
    w.nat(since.as_secs().min(NAT_MAX))
        .nat(u64::from(since.subsec_nanos()));
}

fn put_times(w: &mut Writer, times: &[SystemTime]) {
    w.count(times.len());
    for time in times {
        put_time(w, *time);
    }
}

fn read_time(r: &mut Reader<'_>) -> Result<SystemTime, WireError> {
    let secs = r.nat()?;
    let nanos = r.u32()?;
    Ok(UNIX_EPOCH + Duration::new(secs, nanos))
}

fn read_pick(r: &mut Reader<'_>) -> Result<Pick, WireError> {
    Ok(match r.tag_of(3, "a pick")? {
        0 => Pick::Skip,
        1 => Pick::Store(r.str()?.to_owned()),
        _ => Pick::Legacy(r.str()?.to_owned()),
    })
}

/// The reply of the entry to the request `w` spelled, read by `read`.
fn ask<T>(w: &mut Writer, read: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>) -> T {
    let answered = (|| -> Result<T, Error> {
        let reply = call(Entry::Staging, &w.finish()?)?;
        let mut reply = Reader::reply(&reply)?;
        let value = read(&mut reply)?;
        reply.end()?;
        Ok(value)
    })();
    expect_core(Entry::Staging, answered)
}

/// Whether a publish moved its storage: its rename without replacement met
/// an entry at the target (`taken`) or not (`Sg.settle`).
pub(crate) fn moved(taken: bool) -> bool {
    let mut w = Writer::new();
    w.tag(0).bool(taken);
    ask(&mut w, |r| Ok(r.tag_of(2, "a publish verdict")? == 0))
}

/// What the sweep does with each entry of a directory listing, in order
/// (`Sg.meet`).
pub(crate) fn meet(seens: &[Seen<'_>]) -> Vec<Met> {
    let mut w = Writer::new();
    w.tag(1);
    put_seens(&mut w, seens);
    ask(&mut w, |r| {
        (0..r.count()?)
            .map(|_| {
                Ok(match r.tag_of(4, "a sweep class")? {
                    0 => Met::Keep,
                    1 => Met::Descend,
                    2 => Met::Leftover,
                    _ => Met::Orphan,
                })
            })
            .collect()
    })
}

/// The plan for a judged entry: its lock probe, the time now, its own
/// modification time and those of its direct entries (`Sg.judge`).
pub(crate) fn judge(
    cand: Cand,
    probe: Probe,
    now: SystemTime,
    own: SystemTime,
    inner: &[SystemTime],
) -> Plan {
    let mut w = Writer::new();
    w.tag(2)
        .tag(match cand {
            Cand::Dir => 0,
            Cand::Lock => 1,
        })
        .tag(match probe {
            Probe::Held => 0,
            Probe::Free => 1,
            Probe::Absent => 2,
        });
    put_time(&mut w, now);
    put_time(&mut w, own);
    put_times(&mut w, inner);
    ask(&mut w, |r| {
        Ok(match r.tag_of(4, "a sweep plan")? {
            0 => Plan::Keep,
            1 => Plan::RemoveDir,
            2 => Plan::RemoveDirAndLock,
            _ => Plan::RemoveFile,
        })
    })
}

/// What each entry of the sessions directory is to the listing, in order
/// (`Ls.scan`).
pub(crate) fn scan(seens: &[Seen<'_>]) -> Vec<Pick> {
    let mut w = Writer::new();
    w.tag(3);
    put_seens(&mut w, seens);
    ask(&mut w, |r| (0..r.count()?).map(|_| read_pick(r)).collect())
}

/// The listed sessions, newest first, then by id, then by place
/// (`Ls.rows`).
pub(crate) fn rows(obs: &[Obs<'_>]) -> Vec<Row> {
    let mut w = Writer::new();
    w.tag(4).count(obs.len());
    for entry in obs {
        put_seen(&mut w, entry.seen);
        match entry.cwd {
            Some(cwd) => w.tag(1).str(cwd),
            None => w.tag(0),
        };
        put_times(&mut w, &entry.times);
    }
    ask(&mut w, |r| {
        (0..r.count()?)
            .map(|_| {
                Ok(Row {
                    at: r.count()?,
                    pick: read_pick(r)?,
                    time: read_time(r)?,
                })
            })
            .collect()
    })
}

#[cfg(test)]
mod tests {
    use std::time::{Duration, UNIX_EPOCH};

    use super::{
        judge, meet, moved, rows, scan, Cand, Form, Met, Obs, Pick, Plan, Probe, Row, Seen,
    };

    /// Each call reaches the compiled rule and reads back its exact answer.
    #[test]
    fn the_staging_rule_runs_as_the_compiled_core() {
        assert!(moved(false));
        assert!(!moved(true));
        let leftover = ".s1.import-0123456789abcdef0123456789abcdef";
        let seens = [
            Seen {
                name: Some(leftover),
                form: Form::Dir { main: false },
            },
            Seen {
                name: Some("session-1"),
                form: Form::Dir { main: false },
            },
            Seen {
                name: Some("s2"),
                form: Form::Dir { main: true },
            },
        ];
        assert_eq!(meet(&seens), [Met::Leftover, Met::Descend, Met::Keep]);
        let time = |secs| UNIX_EPOCH + Duration::from_secs(secs);
        assert_eq!(
            judge(
                Cand::Dir,
                Probe::Free,
                time(200_000),
                time(113_600),
                &[time(50_000)]
            ),
            Plan::RemoveDirAndLock
        );
        assert_eq!(
            scan(&[
                Seen {
                    name: Some("durable-1"),
                    form: Form::Dir { main: true },
                },
                Seen {
                    name: Some("legacy-1.jsonl"),
                    form: Form::File,
                },
            ]),
            [
                Pick::Store("durable-1".to_owned()),
                Pick::Legacy("legacy-1".to_owned())
            ]
        );
        let newer = UNIX_EPOCH + Duration::new(30, 5);
        assert_eq!(
            rows(&[Obs {
                seen: Seen {
                    name: Some("a"),
                    form: Form::Dir { main: true },
                },
                cwd: Some("/p"),
                times: vec![time(10), newer],
            }]),
            [Row {
                at: 0,
                pick: Pick::Store("a".to_owned()),
                time: newer,
            }]
        );
    }
}
