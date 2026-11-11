# supervise: the model of the supervisor's restart budget and of its
# timeouts. The restart budget runs compiled as the
# Rust rule: `restart_budget::decide`
# (crates/eukhe-daemon/src/supervisor/restart_budget.rs) calls `decide`
# through bend/ffi_supervise.bend. The timeouts run compiled too:
# `eukhe_daemon::timeouts::derived` writes the base values (the constants
# of crates/eukhe-daemon/src/timeouts.rs, eukhe-types daemon/timing.rs and
# eukhe-core kernel/shared.rs) to bend/ffi_timeouts.bend and reads the
# derived values (the base values: section Timeouts).
#
# A worker fails again and again. Each failure comes g ms after the one
# before it (a gap; the monotonic clock never runs back, so a gap is a
# Nat). The budget keeps the ages of the failures inside the window of w
# ms; a failure with more than k failures in the window (itself included)
# gives the worker up, any other relaunches it after a pause that doubles
# with each failure in the window.

import Base

# Restarts
# --------

# k: the failures the window allows, w: the window, base: the first
# pause, max: the longest pause
type Cfg is Data:
  Cfg{k: Nat, w: Nat, base: Nat, max: Nat}

def Cfg.k(c: Cfg) -> Nat:
  match c:
    case Cfg{k, w, b, m}:
      k

def Cfg.w(c: Cfg) -> Nat:
  match c:
    case Cfg{k, w, b, m}:
      w

type Verdict is Data:
  Relaunch{failure: Nat, backoff: Nat}
  GiveUp{failures: Nat}

# the ages of the failures in the window, newest first, and the failures
# in the window at the last failure
type St is Data:
  St{ages: List<&2, Nat>, n: Nat}

def St.n(s: St) -> Nat:
  match s:
    case St{a, n}:
      n

def St.ages(s: St) -> List<&2, Nat>:
  match s:
    case St{a, n}:
      a

def St.empty() -> St:
  St{Nil{}, 0n}

# every age, g ms older
def older(+g: Nat, ages: List<&2, Nat>) -> List<&2, Nat>:
  match ages:
    case Nil{}:
      Nil{}
    case a <> t:
      Nat.add(g, a) <> older(g, t)

def keep.put(b: Bool, a: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      a <> r
    case False{}:
      r

# the ages still inside the window of w ms
def keep(+w: Nat, ages: List<&2, Nat>) -> List<&2, Nat>:
  match ages:
    case Nil{}:
      Nil{}
    case +a <> t:
      keep.put(Nat.is_lt(a, w), a, keep(w, t))

# the failures in the window g ms after the last one, before the new one
def kept(+c: Cfg, +g: Nat, ages: List<&2, Nat>) -> List<&2, Nat>:
  keep(Cfg.w(c), older(g, ages))

def step.put(+k: List<&2, Nat>) -> St:
  St{0n <> k, 1n+List.length(&2, Nat, k)}

# a failure g ms after the last one
def step(+c: Cfg, s: St, +g: Nat) -> St:
  match s:
    case St{a, n}:
      step.put(kept(c, g, a))

# the state after the failures with the gaps gs, from s
def go(+c: Cfg, gs: List<&2, Nat>, s: St) -> St:
  match gs:
    case Nil{}:
      s
    case +g <> rest:
      go(c, rest, step(c, s, g))

# the failures in the window at the last failure of gs
def failures(+c: Cfg, gs: List<&2, Nat>) -> Nat:
  St.n(go(c, gs, St.empty()))

# x, or the longest pause m when x passes it
def backoff.cap(le: Bool, x: Nat, m: Nat) -> Nat:
  match le:
    case True{}:
      x
    case False{}:
      m

# a pause x (at most m) doubled e times, capped at m after each doubling:
# no value passes m + m, so none passes the runtime's Nat range when m
# fits the wire
def backoff.go(e: Nat, +m: Nat, +x: Nat) -> Nat:
  match e:
    case 0n:
      x
    case 1n+p:
      +d = Nat.add(x, x)
      backoff.go(p, m, backoff.cap(Nat.is_le(d, m), d, m))

# base * 2^min(n - 1, 7), at most max (computed capped at every doubling)
def backoff(+c: Cfg, n: Nat) -> Nat:
  match c:
    case Cfg{k, w, +b, +m}:
      backoff.go(Nat.min(Nat.sub(n, 1n), 7n), m, backoff.cap(Nat.is_le(b, m), b, m))

def verdict.put(over: Bool, +c: Cfg, +n: Nat) -> Verdict:
  match over:
    case True{}:
      GiveUp{n}
    case False{}:
      Relaunch{n, backoff(c, n)}

# the verdict on a failure with n failures in the window
def verdict(+c: Cfg, +n: Nat) -> Verdict:
  verdict.put(Nat.is_lt(Cfg.k(c), n), c, n)

def gives_up(v: Verdict) -> Bool:
  match v:
    case Relaunch{f, b}:
      False{}
    case GiveUp{f}:
      True{}

# the budget after a failure and what follows it: the call the Rust
# `restart_budget::decide` makes (bend/ffi_supervise.bend). The Rust
# keeps the state (the ages in ms, newest first, relative to the last
# failure) and passes the gap in ms since the last failure.
type Decision is Data:
  Decision{st: St, verdict: Verdict}

def decide.put(+c: Cfg, +s: St) -> Decision:
  Decision{s, verdict(c, St.n(s))}

# a failure g ms after the last one, from s
def decide(+c: Cfg, s: St, +g: Nat) -> Decision:
  decide.put(c, step(c, s, g))

def Decision.st(d: Decision) -> St:
  match d:
    case Decision{s, v}:
      s

def Decision.verdict(d: Decision) -> Verdict:
  match d:
    case Decision{s, v}:
      v

def span.go(gs: List<&2, Nat>, c: Nat) -> Nat:
  match gs:
    case Nil{}:
      c
    case g <> rest:
      span.go(rest, Nat.add(g, c))

def span(gs: List<&2, Nat>) -> Nat:
  span.go(gs, 0n)

# Timeouts
# --------
# The base values every timeout derives from (ms, but k); the entry
# bend/ffi_timeouts.bend derives the timeouts from them (laws/timeouts.bend):
#   snap host kstep kterm kverify   the kernel teardown's phases (the
#                                   shutdown step runs three times)
#   harness                         the Harness close
#   wterm wverify                   SIGTERM, then SIGKILL, of a worker
#   margin                          the launcher's margin after the drain
#   refresh boot                    the busy refresh, the boot window
#   relaunch startup check slack    the client relaunch, the supervisor
#                                   start, the worker's check, the slack
#   k bmax loop                     the give-up count, the longest pause,
#                                   the crash-loop period
#   qanswer                         the wait for a quiesce answer

type Tm is Data:
  Tm{snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, slack: Nat, k: Nat, bmax: Nat, loop: Nat, qanswer: Nat}
