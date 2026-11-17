# strength: whether the checks that passed were shown to catch broken
# code. A check is only as good as what it catches: before a passed claim
# counts as done, the verifier breaks the code the task changed on
# purpose (mutants: a flipped comparison, a dropped line), runs the check
# on each broken copy in a scratch copy of the workspace, and counts the
# breaks the check caught. A check its owner gauges (a command or an
# until-condition) must catch at least the owner's share of the breaks
# (`--strength`, percent; default 80); a judge and the intent check have
# no code to break (exempt); a share of 0 is the owner waiving it. Done
# is certified only when no gauged check is weak or unshown and at least
# one check was shown to catch broken code; else a passed claim ends "not
# certified", and a headless run whose checks all pass exits 3 (the code
# of bend/headless_task.bend's unjudged answer: neither done nor a
# failure of the run).
#
# A mark is what the verifier measured for one check on one state: the
# breaks caught, the breaks run, the breaks planned (the sample of the
# mutants of the changed lines), and the state. A measurement cut short
# (the budget or the time ran out first) shows nothing. Only the verifier
# records a mark; the owner's share is part of the check, which only the
# owner sets (bend/verify.bend act).
#
# Rust (eukhe-core durable/acceptance/strength) makes the mutants, runs
# them and asks this model for every decision: the strength of a check
# (strength), the verifier's step after verify's End (settle), the label
# (label), who may record a mark (record) and the exit code of a headless
# run (exit). Entry: bend/ffi_strength.bend. Laws: laws/strength.bend.
# Spec: spec/verified/strength.bend. Pure: no IO, no @unsafe.

import Base
import ./verify.bend as V
import ./headless_task.bend as Ht

# Types
# -----

# what the owner asks of a check: nothing (a judge, the intent check: no
# code to break), nothing because the owner waived it (`--strength 0`),
# or that it catch at least `pct` percent of the breaks
type Bar is Data:
  Exempt{}
  Waived{}
  Needs{pct: Nat}

# what the verifier measured for a check: nothing yet, or the breaks
# caught, run and planned on the state `at`
type Mark is Data:
  Unmeasured{}
  Measured{caught: Nat, ran: Nat, planned: Nat, at: Nat}

# one check: the owner's bar and the verifier's mark
type Gauge is Data:
  Gauge{bar: Bar, mark: Mark}

# the strength of a check on a state: shown to catch the owner's share of
# the breaks, weak (it let more through, or there was nothing to break),
# unshown (not measured on this state, or the measurement was cut short),
# free (exempt or waived)
type Strength is Data:
  Strong{}
  Weak{}
  Unshown{}
  Free{}

# the label of a result: verify's four, and not certified (every check
# confirmed, but not shown to catch broken code)
type Label is Data:
  Verified{}
  Failed{}
  Unverified{}
  Passed{}
  Uncertified{}

# the verifier's step after verify ended a claim: measure the check at
# `index`, or end the claim with the label
type Step is Data:
  Measure{index: Nat}
  End{label: Label}

# The strength of one check
# -------------------------

# the share caught reaches the bar: pct * ran <= 100 * caught
def enough(pct: Nat, caught: Nat, ran: Nat) -> Bool:
  Nat.is_le(Nat.mul(pct, ran), Nat.mul(100n, caught))

def strength.caught(enough: Bool) -> Strength:
  match enough:
    case True{}:
      Strong{}
    case False{}:
      Weak{}

def strength.ran(some: Bool, pct: Nat, caught: Nat, ran: Nat) -> Strength:
  match some:
    case True{}:
      strength.caught(enough(pct, caught, ran))
    case False{}:
      Weak{}

def strength.full(full: Bool, pct: Nat, caught: Nat, +ran: Nat) -> Strength:
  match full:
    case True{}:
      strength.ran(Bool.not(Nat.is_eq(ran, 0n)), pct, caught, ran)
    case False{}:
      Unshown{}

def strength.on(same: Bool, pct: Nat, caught: Nat, +ran: Nat, planned: Nat) -> Strength:
  match same:
    case True{}:
      strength.full(Nat.is_le(planned, ran), pct, caught, ran)
    case False{}:
      Unshown{}

def strength.mark(pct: Nat, now: Nat, m: Mark) -> Strength:
  match m:
    case Unmeasured{}:
      Unshown{}
    case Measured{caught, ran, planned, at}:
      strength.on(Nat.is_eq(at, now), pct, caught, ran, planned)

# the strength of a check on the state `now`: a gauged check is strong
# when its mark, taken on `now` and not cut short, ran at least one break
# and caught at least its share; weak when it caught less, or nothing was
# there to break; unshown without a whole mark on `now`
def strength(now: Nat, g: Gauge) -> Strength:
  match g:
    case Gauge{b, m}:
      match b:
        case Exempt{}:
          Free{}
        case Waived{}:
          Free{}
        case Needs{pct}:
          strength.mark(pct, now, m)

def is_strong(s: Strength) -> Bool:
  match s:
    case Strong{}:
      True{}
    case Weak{}:
      False{}
    case Unshown{}:
      False{}
    case Free{}:
      False{}

# a strength that keeps done from being certified: weak or unshown
def blocks(s: Strength) -> Bool:
  match s:
    case Strong{}:
      False{}
    case Weak{}:
      True{}
    case Unshown{}:
      True{}
    case Free{}:
      False{}

# some check is strong on `now`
def shown(+now: Nat, gs: List<&2, Gauge>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case Con{g, t}:
      Bool.or(is_strong(strength(now, g)), shown(now, t))

# no check is weak or unshown on `now`
def clear(+now: Nat, gs: List<&2, Gauge>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case Con{g, t}:
      Bool.and(Bool.not(blocks(strength(now, g))), clear(now, t))

# done is certified on `now`: some check was shown to catch broken code,
# and none is weak or unshown
def certified(+now: Nat, +gs: List<&2, Gauge>) -> Bool:
  Bool.and(shown(now, gs), clear(now, gs))

# The label
# ---------

# verify's label as this model's
def lift(l: V.Label) -> Label:
  match l:
    case V.Verified{}:
      Verified{}
    case V.Failed{}:
      Failed{}
    case V.Unverified{}:
      Unverified{}
    case V.Passed{}:
      Passed{}

# verify's label says every check is confirmed
def passes(l: V.Label) -> Bool:
  match l:
    case V.Verified{}:
      True{}
    case V.Failed{}:
      False{}
    case V.Unverified{}:
      False{}
    case V.Passed{}:
      True{}

def label.cert(ok: Bool, l: V.Label) -> Label:
  match ok:
    case True{}:
      lift(l)
    case False{}:
      Uncertified{}

def label.pass(p: Bool, ok: Bool, l: V.Label) -> Label:
  match p:
    case True{}:
      label.cert(ok, l)
    case False{}:
      lift(l)

# the label of a result whose verify label is `l`: a passing one stays
# only when done is certified on `now`, else it is not certified; every
# other stays
def label(+l: V.Label, now: Nat, gs: List<&2, Gauge>) -> Label:
  label.pass(passes(l), certified(now, gs), l)

# The verifier's step
# -------------------

# the check is gauged and has no mark taken on `now`
def unmeasured(now: Nat, g: Gauge) -> Bool:
  match g:
    case Gauge{b, m}:
      match b:
        case Exempt{}:
          False{}
        case Waived{}:
          False{}
        case Needs{pct}:
          match m:
            case Unmeasured{}:
              True{}
            case Measured{caught, ran, planned, at}:
              Bool.not(Nat.is_eq(at, now))

def due.pick(open: Bool, i: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match open:
    case True{}:
      Some{i}
    case False{}:
      rest

# the index, counted from i, of the first gauged check with no mark on
# `now`; None when there is none
def due(+now: Nat, gs: List<&2, Gauge>, +i: Nat) -> Maybe<&2, Nat>:
  match gs:
    case Nil{}:
      None{}
    case Con{g, t}:
      due.pick(unmeasured(now, g), i, due(now, t, 1n+i))

def settle.due(d: Maybe<&2, Nat>, l: V.Label, now: Nat, gs: List<&2, Gauge>) -> Step:
  match d:
    case None{}:
      End{label(l, now, gs)}
    case Some{i}:
      Measure{i}

def settle.pass(p: Bool, l: V.Label, +now: Nat, +gs: List<&2, Gauge>) -> Step:
  match p:
    case True{}:
      settle.due(due(now, gs, 0n), l, now, gs)
    case False{}:
      End{lift(l)}

# the step after verify ended a claim with `l` on `now`: a passing claim
# measures each gauged check with no mark on `now`, first first, then ends
# with the label; a claim that did not pass ends with its label at once
# (no breaks are run for it)
def settle(+l: V.Label, now: Nat, gs: List<&2, Gauge>) -> Step:
  settle.pass(passes(l), l, now, gs)

# Who records a mark
# ------------------

def put.mark(m: Mark, g: Gauge) -> Gauge:
  match g:
    case Gauge{b, old}:
      Gauge{b, m}

def put.cons(h: Gauge, r: Maybe<&2, List<&2, Gauge>>) -> Maybe<&2, List<&2, Gauge>>:
  match r:
    case None{}:
      None{}
    case Some{t}:
      Some{h <> t}

# `gs` with the mark of check i replaced by m (its bar kept); None when
# there is no check i
def put(i: Nat, m: Mark, gs: List<&2, Gauge>) -> Maybe<&2, List<&2, Gauge>>:
  match i:
    case 0n:
      match gs:
        case Nil{}:
          None{}
        case Con{h, t}:
          Some{put.mark(m, h) <> t}
    case 1n+p:
      match gs:
        case Nil{}:
          None{}
        case Con{h, t}:
          put.cons(h, put(p, m, t))

def record.put(r: Maybe<&2, List<&2, Gauge>>, old: List<&2, Gauge>) -> Bool & List<&2, Gauge>:
  match r:
    case None{}:
      (False{}, old)
    case Some{gs}:
      (True{}, gs)

# only the verifier records a mark, only for a check that exists: whether
# it is admitted, and the checks after it (`gs` itself when refused)
def record(who: V.Actor, i: Nat, m: Mark, +gs: List<&2, Gauge>) -> Bool & List<&2, Gauge>:
  match who:
    case V.Owner{}:
      (False{}, gs)
    case V.Worker{}:
      (False{}, gs)
    case V.Verifier{}:
      record.put(put(i, m, gs), gs)

# The exit code of a headless run
# -------------------------------

def exit.cert(ok: Bool, base: Nat) -> Nat:
  match ok:
    case True{}:
      base
    case False{}:
      match base:
        case 0n:
          Ht.unjudged_code()
        case 1n+p:
          1n+p

def exit.held(held: Bool, base: Nat, now: Nat, slots: List<&2, V.Slot>, gs: List<&2, Gauge>) -> Nat:
  match held:
    case True{}:
      exit.cert(Bool.or(Bool.not(V.some(slots)), certified(now, gs)), base)
    case False{}:
      V.exit.code(False{}, base)

# the exit code of a headless run whose own code is `base`: verify's exit
# (bend/verify.bend exit), and, when every check is confirmed on `now`
# and there is one, 3 instead of 0 when done is not certified; a nonzero
# code of the run itself is kept
def exit(base: Nat, +now: Nat, +slots: List<&2, V.Slot>, gs: List<&2, Gauge>) -> Nat:
  exit.held(V.holds(now, slots), base, now, slots, gs)
