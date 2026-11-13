//! The limits of a run (`bend/limits.bend`, entry `bend/ffi_limits.bend`;
//! `laws/limits.bend`, spec `spec/budget/limits.bend`). A run is what one
//! request of the principal starts; each of its dimensions (money, tokens,
//! time, tool calls, model requests) holds a number or `unlimited`, and
//! the source it came from. [`fill`] gives a run its limits; [`profile`]
//! and [`preset`] are the limits profile and the shipped presets of a kind;
//! [`plan_wraps`] and [`plan_notice`] read a plan's quota windows;
//! [`floor`] says whether a run's limits hold its first request; [`renew`]
//! sets an account to a run's limits; [`prefix`] reads the `/b` words at
//! the start of a message. Rust gathers the facts; it decides nothing.
//!
//! Every number crosses the wire, so each stays within
//! [`NAT_MAX`](crate::wire::NAT_MAX); a number past it is an [`Error`].

use crate::rules::budget::{get_acct, put_acct, put_amt, put_ask, Acct, Amt, Ask, Dim};
use crate::wire::{Reader, WireError, Writer};
use crate::{call, Entry, Error};

/// The kind of a run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// One message sent while the session is idle.
    Interactive,
    /// One `-p` prompt.
    Headless,
    /// One prompt of an SDK session.
    Sdk,
    /// One cron fire.
    Scheduled,
    /// A whole `/loop`.
    Loop,
    /// A whole autoresearch run.
    Autoresearch,
}

/// How the run's model is paid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Auth {
    /// A subscription login.
    Plan,
    /// An API key.
    ApiKey,
    /// A local model (a provider with no price).
    Local,
}

/// Whether unset dimensions fill from the profiles (`budget.limits`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Toggle {
    Off,
    On,
}

/// One dimension's limit.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Val {
    /// Not given.
    #[default]
    Unset,
    At(u64),
    /// Unlimited, as the principal gave it (or until finished, after
    /// [`fill`]).
    Unlimited,
}

/// A limit per dimension: money (micro-dollars), tokens, time (ms), tool
/// calls, model requests.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Lims {
    pub cost: Val,
    pub tok: Val,
    pub ms: Val,
    pub calls: Val,
    pub reqs: Val,
}

/// Where a dimension's limit came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Src {
    /// Nothing set it: until finished (the default).
    UntilFinished,
    /// The principal set it for this run.
    Set,
    /// The limits profile (limits on).
    LimitsProfile,
    /// The principal's profile for the kind (limits on).
    Profile,
    /// The preset at this place among the presets given to [`fill`].
    Preset(usize),
}

/// A source per dimension, in the order of [`Lims`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Srcs {
    pub cost: Src,
    pub tok: Src,
    pub ms: Src,
    pub calls: Src,
    pub reqs: Src,
}

/// A run's limits (no dimension [`Val::Unset`]) and their sources.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Filled {
    pub lims: Lims,
    pub srcs: Srcs,
}

/// A shipped preset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scale {
    /// A quarter of the limits profile.
    Quick,
    /// Four times the limits profile.
    Deep,
}

/// A plan quota window's last reading.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Window {
    pub label: String,
    /// Used, in permille (may pass 1000).
    pub used_permille: u64,
}

/// The windows to tell of now and the labels told of since.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Told {
    /// Places in the windows given, in order.
    pub now: Vec<usize>,
    /// The labels told of: the next call's `told`.
    pub told: Vec<String>,
}

/// A key of a `/b` pair.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Key {
    Cost,
    Tokens,
    Time,
    Calls,
    Requests,
}

/// The `/b` prefix of a message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Prefix {
    /// The presets named (places in the names given, in order), the
    /// `key=value` pairs (each value with its full-width chars read as
    /// ASCII and `,` as `.`), and the rest of the message verbatim. A
    /// message with no `/b` prefix is all `rest`.
    Read {
        presets: Vec<usize>,
        pairs: Vec<(Key, String)>,
        rest: String,
    },
    /// A pair with an empty value or a key given twice: the word as typed.
    Refused { word: String },
}

fn put_kind(w: &mut Writer, kind: Kind) {
    w.tag(match kind {
        Kind::Interactive => 0,
        Kind::Headless => 1,
        Kind::Sdk => 2,
        Kind::Scheduled => 3,
        Kind::Loop => 4,
        Kind::Autoresearch => 5,
    });
}

fn put_auth(w: &mut Writer, auth: Auth) {
    w.tag(match auth {
        Auth::Plan => 0,
        Auth::ApiKey => 1,
        Auth::Local => 2,
    });
}

fn put_val(w: &mut Writer, val: Val) {
    match val {
        Val::Unset => w.tag(0),
        Val::At(n) => w.tag(1).nat(n),
        Val::Unlimited => w.tag(2),
    };
}

fn put_lims(w: &mut Writer, lims: &Lims) {
    for val in [lims.cost, lims.tok, lims.ms, lims.calls, lims.reqs] {
        put_val(w, val);
    }
}

fn get_val(r: &mut Reader<'_>) -> Result<Val, WireError> {
    Ok(match r.tag_of(3, "a limit")? {
        0 => Val::Unset,
        1 => Val::At(r.nat()?),
        // `tag_of` answers a tag below 3: this is 2.
        _ => Val::Unlimited,
    })
}

fn get_lims(r: &mut Reader<'_>) -> Result<Lims, WireError> {
    Ok(Lims {
        cost: get_val(r)?,
        tok: get_val(r)?,
        ms: get_val(r)?,
        calls: get_val(r)?,
        reqs: get_val(r)?,
    })
}

fn get_src(r: &mut Reader<'_>) -> Result<Src, WireError> {
    Ok(match r.tag_of(5, "a limit source")? {
        0 => Src::UntilFinished,
        1 => Src::Set,
        2 => Src::LimitsProfile,
        3 => Src::Profile,
        // `tag_of` answers a tag below 5: this is 4.
        _ => Src::Preset(r.count()?),
    })
}

fn get_strs(r: &mut Reader<'_>) -> Result<Vec<String>, WireError> {
    let n = r.count()?;
    let mut strs = Vec::with_capacity(n);
    for _ in 0..n {
        strs.push(r.str()?.to_string());
    }
    Ok(strs)
}

fn get_places(r: &mut Reader<'_>) -> Result<Vec<usize>, WireError> {
    let n = r.count()?;
    let mut places = Vec::with_capacity(n);
    for _ in 0..n {
        places.push(r.count()?);
    }
    Ok(places)
}

fn ask<T>(
    write: impl FnOnce(&mut Writer),
    read: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>,
) -> Result<T, Error> {
    let mut request = Writer::new();
    write(&mut request);
    let reply = call(Entry::Limits, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let value = read(&mut reader)?;
    reader.end()?;
    Ok(value)
}

/// The limits of a run of `kind` paid by `auth`: per dimension `set` (the
/// principal's limits for this run), else the last of `presets` (in the
/// order typed) that gives it, else with `toggle` on `own` (the
/// principal's profile for the kind), else the limits profile, else
/// unlimited until finished.
///
/// # Errors
///
/// A number past the wire, or a failure of the compiled core.
pub fn fill(
    toggle: Toggle,
    kind: Kind,
    auth: Auth,
    set: &Lims,
    presets: &[Lims],
    own: &Lims,
) -> Result<Filled, Error> {
    ask(
        |w| {
            w.tag(0).bool(toggle == Toggle::On);
            put_kind(w, kind);
            put_auth(w, auth);
            put_lims(w, set);
            w.count(presets.len());
            for preset in presets {
                put_lims(w, preset);
            }
            put_lims(w, own);
        },
        |r| {
            let lims = get_lims(r)?;
            Ok(Filled {
                lims,
                srcs: Srcs {
                    cost: get_src(r)?,
                    tok: get_src(r)?,
                    ms: get_src(r)?,
                    calls: get_src(r)?,
                    reqs: get_src(r)?,
                },
            })
        },
    )
}

/// The limits profile of `kind` paid by `auth`: time, tool calls (unset
/// for a local model) and model requests; money and tokens unset.
///
/// # Errors
///
/// A failure of the compiled core.
pub fn profile(kind: Kind, auth: Auth) -> Result<Lims, Error> {
    ask(
        |w| {
            w.tag(1);
            put_kind(w, kind);
            put_auth(w, auth);
        },
        get_lims,
    )
}

/// The shipped preset `scale` of `kind` paid by `auth`.
///
/// # Errors
///
/// A failure of the compiled core.
pub fn preset(scale: Scale, kind: Kind, auth: Auth) -> Result<Lims, Error> {
    ask(
        |w| {
            w.tag(2).tag(match scale {
                Scale::Quick => 0,
                Scale::Deep => 1,
            });
            put_kind(w, kind);
            put_auth(w, auth);
        },
        get_lims,
    )
}

/// The place of the first window whose used permille is at or past
/// `1000 - reserve_permille`, if any.
///
/// # Errors
///
/// A number past the wire, or a failure of the compiled core.
pub fn plan_wraps(used_permille: &[u64], reserve_permille: u64) -> Result<Option<usize>, Error> {
    ask(
        |w| {
            w.tag(3).count(used_permille.len());
            for used in used_permille {
                w.nat(*used);
            }
            w.nat(reserve_permille);
        },
        |r| {
            if r.maybe()? {
                r.count().map(Some)
            } else {
                Ok(None)
            }
        },
    )
}

/// The windows to tell of: each reading at or past `1000 -
/// reserve_permille` whose label is not in `told`; a reading below it
/// takes its label out of `told`.
///
/// # Errors
///
/// A number or string past the wire, or a failure of the compiled core.
pub fn plan_notice(
    windows: &[Window],
    reserve_permille: u64,
    told: &[String],
) -> Result<Told, Error> {
    ask(
        |w| {
            w.tag(4).count(windows.len());
            for window in windows {
                w.str(&window.label).nat(window.used_permille);
            }
            w.nat(reserve_permille).count(told.len());
            for label in told {
                w.str(label);
            }
        },
        |r| {
            Ok(Told {
                now: get_places(r)?,
                told: get_strs(r)?,
            })
        },
    )
}

/// The first dimension in which `lims` cannot hold the run's first work
/// request `first` with its final-answer reserve `keep`, if any; an
/// unbounded dimension holds anything.
///
/// # Errors
///
/// A number past the wire, or a failure of the compiled core.
pub fn floor(lims: &Lims, first: Ask, keep: Ask) -> Result<Option<Dim>, Error> {
    ask(
        |w| {
            w.tag(5);
            put_lims(w, lims);
            put_ask(w, first);
            put_ask(w, keep);
        },
        |r| {
            if !r.maybe()? {
                return Ok(None);
            }
            Ok(Some(match r.tag_of(5, "a budget dimension")? {
                0 => Dim::Cost,
                1 => Dim::Tokens,
                2 => Dim::Time,
                3 => Dim::Calls,
                // `tag_of` answers a tag below 5: this is 4.
                _ => Dim::Reqs,
            }))
        },
    )
}

/// `acct` set to `lims`: free in each bounded dimension becomes its limit
/// less what the run used (spent since `mark`, the account's spent when
/// the run started; held; lent), a time limit puts the deadline at `now`
/// (Unix ms) plus it; spent, lent, the overrun and the holds stay.
///
/// # Errors
///
/// A number past the wire, or a failure of the compiled core.
pub fn renew(lims: &Lims, mark: Amt, now: u64, acct: &Acct) -> Result<Acct, Error> {
    ask(
        |w| {
            w.tag(6);
            put_lims(w, lims);
            put_amt(w, mark);
            w.nat(now);
            put_acct(w, acct);
        },
        get_acct,
    )
}

/// The `/b` prefix of `text`, with `names` the preset names.
///
/// # Errors
///
/// A string past the wire, or a failure of the compiled core.
pub fn prefix(text: &str, names: &[&str]) -> Result<Prefix, Error> {
    ask(
        |w| {
            w.tag(7).str(text).count(names.len());
            for name in names {
                w.str(name);
            }
        },
        |r| {
            if r.tag_of(2, "a prefix")? == 1 {
                return Ok(Prefix::Refused {
                    word: r.str()?.to_string(),
                });
            }
            let presets = get_places(r)?;
            let n = r.count()?;
            let mut pairs = Vec::with_capacity(n);
            for _ in 0..n {
                let key = match r.tag_of(5, "a limit key")? {
                    0 => Key::Cost,
                    1 => Key::Tokens,
                    2 => Key::Time,
                    3 => Key::Calls,
                    // `tag_of` answers a tag below 5: this is 4.
                    _ => Key::Requests,
                };
                pairs.push((key, r.str()?.to_string()));
            }
            Ok(Prefix::Read {
                presets,
                pairs,
                rest: r.str()?.to_string(),
            })
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    const UNSET: Lims = Lims {
        cost: Val::Unset,
        tok: Val::Unset,
        ms: Val::Unset,
        calls: Val::Unset,
        reqs: Val::Unset,
    };

    /// With limits off a run is until finished unless the principal sets
    /// a limit; with limits on the limits profile fills time, tool calls
    /// and requests, money and tokens stay until finished.
    #[test]
    fn a_run_fills_from_set_presets_and_the_profiles() {
        let set = Lims {
            cost: Val::At(2_000_000),
            ..UNSET
        };
        let quick = preset(Scale::Quick, Kind::Interactive, Auth::ApiKey).unwrap();
        assert_eq!(
            [
                fill(
                    Toggle::Off,
                    Kind::Interactive,
                    Auth::ApiKey,
                    &set,
                    &[],
                    &UNSET
                )
                .unwrap(),
                fill(Toggle::On, Kind::Loop, Auth::Local, &UNSET, &[], &UNSET).unwrap(),
                fill(
                    Toggle::Off,
                    Kind::Interactive,
                    Auth::ApiKey,
                    &UNSET,
                    &[quick],
                    &UNSET
                )
                .unwrap(),
            ],
            [
                Filled {
                    lims: Lims {
                        cost: Val::At(2_000_000),
                        tok: Val::Unlimited,
                        ms: Val::Unlimited,
                        calls: Val::Unlimited,
                        reqs: Val::Unlimited,
                    },
                    srcs: Srcs {
                        cost: Src::Set,
                        tok: Src::UntilFinished,
                        ms: Src::UntilFinished,
                        calls: Src::UntilFinished,
                        reqs: Src::UntilFinished,
                    },
                },
                Filled {
                    lims: Lims {
                        cost: Val::Unlimited,
                        tok: Val::Unlimited,
                        ms: Val::At(28_800_000),
                        calls: Val::Unlimited,
                        reqs: Val::At(6400),
                    },
                    srcs: Srcs {
                        cost: Src::UntilFinished,
                        tok: Src::UntilFinished,
                        ms: Src::LimitsProfile,
                        calls: Src::UntilFinished,
                        reqs: Src::LimitsProfile,
                    },
                },
                Filled {
                    lims: Lims {
                        cost: Val::Unlimited,
                        tok: Val::Unlimited,
                        ms: Val::At(3_600_000),
                        calls: Val::At(1000),
                        reqs: Val::At(800),
                    },
                    srcs: Srcs {
                        cost: Src::UntilFinished,
                        tok: Src::UntilFinished,
                        ms: Src::Preset(0),
                        calls: Src::Preset(0),
                        reqs: Src::Preset(0),
                    },
                },
            ]
        );
    }

    /// A plan window at 80 % wraps the run and is told of once until a
    /// reading below 80 %.
    #[test]
    fn plan_windows_wrap_and_are_told_of_once() {
        let windows = [
            Window {
                label: "5h".into(),
                used_permille: 850,
            },
            Window {
                label: "7d".into(),
                used_permille: 100,
            },
        ];
        let first = plan_notice(&windows, 200, &[]).unwrap();
        assert_eq!(
            (
                plan_wraps(&[100, 800], 200).unwrap(),
                first.clone(),
                plan_notice(&windows, 200, &first.told).unwrap().now,
            ),
            (
                Some(1),
                Told {
                    now: vec![0],
                    told: vec!["5h".into()],
                },
                vec![],
            )
        );
    }

    /// Limits that cannot hold the first request name the short
    /// dimension; renewal counts what the run holds.
    #[test]
    fn floor_and_renewal() {
        let lims = Lims {
            reqs: Val::At(1),
            ms: Val::At(60_000),
            ..UNSET
        };
        let one = Ask {
            amt: Amt {
                reqs: 1,
                ..Amt::default()
            },
            ms: 10_000,
        };
        let acct = Acct {
            spent: Amt {
                reqs: 5,
                ..Amt::default()
            },
            until: 7,
            ..Acct::default()
        };
        assert_eq!(
            (
                floor(&lims, one, Ask::default()).unwrap(),
                floor(&lims, one, one).unwrap(),
                renew(
                    &lims,
                    Amt {
                        reqs: 4,
                        ..Amt::default()
                    },
                    1000,
                    &acct
                )
                .unwrap(),
            ),
            (
                None,
                Some(Dim::Reqs),
                Acct {
                    free: Amt::default(),
                    until: 61_000,
                    ..acct.clone()
                },
            )
        );
    }

    /// `/b` reads presets and pairs, full-width digits and a decimal
    /// comma; the first other word starts the message.
    #[test]
    fn the_prefix_ends_at_the_first_other_word() {
        assert_eq!(
            [
                prefix("/b quick 2h after lunch", &["quick"]).unwrap(),
                prefix("/b cost=1,5 time=２h  hi  there", &["quick"]).unwrap(),
                prefix("/b cost=1 cost=2 x", &[]).unwrap(),
                prefix("/bob hi", &[]).unwrap(),
            ],
            [
                Prefix::Read {
                    presets: vec![0],
                    pairs: vec![],
                    rest: "2h after lunch".into(),
                },
                Prefix::Read {
                    presets: vec![],
                    pairs: vec![(Key::Cost, "1.5".into()), (Key::Time, "2h".into())],
                    rest: "hi  there".into(),
                },
                Prefix::Refused {
                    word: "cost=2".into(),
                },
                Prefix::Read {
                    presets: vec![],
                    pairs: vec![],
                    rest: "/bob hi".into(),
                },
            ]
        );
    }
}
