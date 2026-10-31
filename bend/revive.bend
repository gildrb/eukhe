# revive: the model of the busy evidence of a long run and of the boot
# revival's vetoes. The busy refresh is the worker's
# (crates/eukhe-daemon/src/worker.rs, every `timeouts::BUSY_REFRESH_MS`);
# the veto runs compiled as the Rust rule: `revival_gate::revival_veto`
# gathers the facts and calls `veto` through bend/ffi_revive.bend.
#
# A run records busy evidence at its start and again every h ms while it
# runs (a refresh). The worker crashes c ms into the run; a boot follows d
# ms after the crash. The evidence is fresh at the boot when its age is at
# most the max age m. A run may take any time: the age counts from the
# last refresh.

import Base

def tick.put(at: Bool, r: Nat) -> Nat:
  match at:
    case True{}:
      0n
    case False{}:
      1n+r

# one ms of the run: r ms since the last record become r + 1, or 0 when
# the refresh is due (a refresh every h ms)
def tick(+h: Nat, +r: Nat) -> Nat:
  tick.put(Nat.is_eq(1n+r, h), r)

# the ms since the last record, c ms into a run whose last record was r
# ms ago
def since(c: Nat, +h: Nat, r: Nat) -> Nat:
  match c:
    case 0n:
      r
    case 1n+p:
      since(p, h, tick(h, r))

# the evidence's age at a boot d ms after a crash c ms into a run
def age(+h: Nat, c: Nat, d: Nat) -> Nat:
  Nat.add(since(c, h, 0n), d)

# the evidence of age a revives, with the max age m
def fresh(m: Nat, a: Nat) -> Bool:
  Nat.is_le(a, m)

# The veto
# --------
# A boot at `now` may relaunch a dead worker unless, in this order: the
# supervisor gave it up, its session is archived (stopped), a live worker
# holds its session lease, no busy record has a time stamp, or the newest
# busy record is not fresh. A record is fresh when it is dated at most
# `skew` ms after `now` (two daemons on one store may disagree a little; a
# later stamp is a clock rollback or a bad write) and its age is at most
# the max age. A stamp that cannot be read proves nothing.

# the newest busy record: none, one whose stamp cannot be read, or one
# recorded at `at` (ms)
type Busy is Data:
  NoBusy{}
  Unread{}
  Stamp{at: Nat}

# what the boot found: the give-up verdict, the archived belt, the live
# lease holder's pid, the busy record, the time, the max age and the skew
type Facts is Data:
  Facts{failed: Bool, archived: Bool, lease: Maybe<&2, Nat>, busy: Busy, now: Nat, max: Nat, skew: Nat}

# what the boot does with the worker: revive it, or the veto
type Veto is Data:
  Revive{}
  GaveUp{}
  Archived{}
  Leased{pid: Nat}
  NoEvidence{}
  Stale{}

# a record dated at `at` is fresh at `now`: not past the skew, and its age
# (0 for a stamp after now) at most the max age
def fresh_at(+at: Nat, +now: Nat, m: Nat, skew: Nat) -> Bool:
  Bool.and(Nat.is_le(at, Nat.add(now, skew)), fresh(m, Nat.sub(now, at)))

def veto.fresh(ok: Bool) -> Veto:
  match ok:
    case True{}:
      Revive{}
    case False{}:
      Stale{}

def veto.busy(b: Busy, now: Nat, m: Nat, skew: Nat) -> Veto:
  match b:
    case NoBusy{}:
      NoEvidence{}
    case Unread{}:
      Stale{}
    case Stamp{at}:
      veto.fresh(fresh_at(at, now, m, skew))

def veto.lease(l: Maybe<&2, Nat>, b: Busy, now: Nat, m: Nat, skew: Nat) -> Veto:
  match l:
    case Some{pid}:
      Leased{pid}
    case None{}:
      veto.busy(b, now, m, skew)

def veto.archived(a: Bool, l: Maybe<&2, Nat>, b: Busy, now: Nat, m: Nat, skew: Nat) -> Veto:
  match a:
    case True{}:
      Archived{}
    case False{}:
      veto.lease(l, b, now, m, skew)

# the boot's decision on the facts f
def veto(f: Facts) -> Veto:
  match f:
    case Facts{failed, a, l, b, now, m, skew}:
      match failed:
        case True{}:
          GaveUp{}
        case False{}:
          veto.archived(a, l, b, now, m, skew)
