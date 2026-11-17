# verified (spec): what the laws of area strength (laws/strength.bend)
# speak of, over the types of bend/strength.bend: when a claim whose
# checks all passed is certified done. A spec: the shipped code never
# calls it.
#
# K1: a gauged check (its owner asks it to catch a share of the breaks:
#     a command or an until-condition) is strong on a state exactly when
#     its mark was taken on that state, every planned break ran, at least
#     one ran, and the breaks it caught are at least its share of those
#     run (caught * 100 >= share * ran); weak when every planned break
#     ran on that state and it caught less, or none was there to run;
#     unshown otherwise (never measured, measured on another state, cut
#     short). A judge, the intent check and a check whose owner waived
#     its share are free: they neither show nor block.
# K2: done is certified on a state exactly when at least one check is
#     strong on it and none is weak or unshown.
# K3: the label of a result whose checks all passed (verify's verified or
#     passed) is that label when done is certified, else not certified;
#     every other label (failed, unverified) stays.
# K4: after verify ended a claim, a passing claim measures, in order,
#     each gauged check with no mark taken on the state now; once none is
#     left it ends with the label of K3. A claim that did not pass ends
#     with its label at once: no break runs for it.
# K5: only the verifier records a mark, only for a check that exists: it
#     replaces that check's mark and nothing else; any other act changes
#     nothing.
# K6: a headless run exits as verify says (bend/verify.bend exit), except
#     that when every check is confirmed on the final state, there is a
#     check, done is not certified and the run's own code is 0, it exits
#     3 (bend/headless_task.bend's unjudged code); a nonzero code of the
#     run itself is kept.
# K7: the observers the laws read.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ./verify.bend as S

# K1: the strength of a measured gauged check: `whole` its mark is on the
# state now and every planned break ran, `none` no break ran, `enough` it
# caught its share
def grade(whole: Bool, none: Bool, enough: Bool) -> St.Strength:
  match whole:
    case False{}:
      St.Unshown{}
    case True{}:
      match none:
        case True{}:
          St.Weak{}
        case False{}:
          match enough:
            case True{}:
              St.Strong{}
            case False{}:
              St.Weak{}

# K1: the strength of a check on the state now
def strength(+now: Nat, g: St.Gauge) -> St.Strength:
  match g:
    case St.Gauge{b, m}:
      match b:
        case St.Exempt{}:
          St.Free{}
        case St.Waived{}:
          St.Free{}
        case St.Needs{pct}:
          match m:
            case St.Unmeasured{}:
              St.Unshown{}
            case St.Measured{c, +r, p, at}:
              grade(Bool.and(Nat.is_eq(at, now), Nat.is_le(p, r)), Nat.is_eq(r, 0n), Nat.is_le(Nat.mul(pct, r), Nat.mul(100n, c)))

# 1 for true, 0 for false
def bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# K2: the strength is strong
def strong(s: St.Strength) -> Bool:
  match s:
    case St.Strong{}:
      True{}
    case St.Weak{}:
      False{}
    case St.Unshown{}:
      False{}
    case St.Free{}:
      False{}

# K2: the strength is weak or unshown
def blocking(s: St.Strength) -> Bool:
  match s:
    case St.Strong{}:
      False{}
    case St.Weak{}:
      True{}
    case St.Unshown{}:
      True{}
    case St.Free{}:
      False{}

# K2: how many checks are strong on the state now
def strongs(+now: Nat, gs: List<&2, St.Gauge>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{g, t}:
      Nat.add(bit(strong(strength(now, g))), strongs(now, t))

# K2: how many checks are weak or unshown on the state now
def blockers(+now: Nat, gs: List<&2, St.Gauge>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{g, t}:
      Nat.add(bit(blocking(strength(now, g))), blockers(now, t))

# K2: done is certified on the state now
def certified(+now: Nat, +gs: List<&2, St.Gauge>) -> Bool:
  Bool.and(Bool.not(Nat.is_eq(strongs(now, gs), 0n)), Nat.is_eq(blockers(now, gs), 0n))

# K3: the label of a result whose verify label is l
def label.ok(ok: Bool, good: St.Label) -> St.Label:
  match ok:
    case True{}:
      good
    case False{}:
      St.Uncertified{}

def label(l: V.Label, +now: Nat, +gs: List<&2, St.Gauge>) -> St.Label:
  match l:
    case V.Verified{}:
      label.ok(certified(now, gs), St.Verified{})
    case V.Failed{}:
      St.Failed{}
    case V.Unverified{}:
      St.Unverified{}
    case V.Passed{}:
      label.ok(certified(now, gs), St.Passed{})

# K4: the check is gauged and its mark was not taken on the state now
def due_here(+now: Nat, g: St.Gauge) -> Bool:
  match g:
    case St.Gauge{b, m}:
      match b:
        case St.Exempt{}:
          False{}
        case St.Waived{}:
          False{}
        case St.Needs{pct}:
          match m:
            case St.Unmeasured{}:
              True{}
            case St.Measured{c, r, p, at}:
              Bool.not(Nat.is_eq(at, now))

def lead.step(here: Bool, rest: Nat) -> Nat:
  match here:
    case True{}:
      0n
    case False{}:
      1n+rest

# K4: how many checks come before the first one due on the state now (the
# count of the checks when none is due)
def lead(+now: Nat, gs: List<&2, St.Gauge>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{g, t}:
      lead.step(due_here(now, g), lead(now, t))

# K4: how many checks are due on the state now
def dues(+now: Nat, gs: List<&2, St.Gauge>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{g, t}:
      Nat.add(bit(due_here(now, g)), dues(now, t))

# K3, K4: verify's label says every check is confirmed
def passing(l: V.Label) -> Bool:
  match l:
    case V.Verified{}:
      True{}
    case V.Failed{}:
      False{}
    case V.Unverified{}:
      False{}
    case V.Passed{}:
      True{}

def settle.of(due: Bool, l: V.Label, +now: Nat, +gs: List<&2, St.Gauge>) -> St.Step:
  match due:
    case True{}:
      St.Measure{lead(now, gs)}
    case False{}:
      St.End{label(l, now, gs)}

def settle.pass(p: Bool, +l: V.Label, +now: Nat, +gs: List<&2, St.Gauge>) -> St.Step:
  match p:
    case True{}:
      settle.of(Bool.not(Nat.is_eq(dues(now, gs), 0n)), l, now, gs)
    case False{}:
      St.End{label(l, now, gs)}

# K4: the verifier's step after verify ended a claim with l on the state
# now
def settle(+l: V.Label, now: Nat, gs: List<&2, St.Gauge>) -> St.Step:
  settle.pass(passing(l), l, now, gs)

# K5: the bar of a gauge
def bar(g: St.Gauge) -> St.Bar:
  match g:
    case St.Gauge{b, m}:
      b

# K5: the mark of a gauge
def mark(g: St.Gauge) -> St.Mark:
  match g:
    case St.Gauge{b, m}:
      m

# K5: the gauge at index i, if any
def nth(i: Nat, gs: List<&2, St.Gauge>) -> Maybe<&2, St.Gauge>:
  match i:
    case 0n:
      match gs:
        case Nil{}:
          None{}
        case Con{g, t}:
          Some{g}
    case 1n+p:
      match gs:
        case Nil{}:
          None{}
        case Con{g, t}:
          nth(p, t)

# K5: the actor is the verifier
def is_verifier(who: V.Actor) -> Bool:
  match who:
    case V.Owner{}:
      False{}
    case V.Worker{}:
      False{}
    case V.Verifier{}:
      True{}

# K5, K7: whether an act was admitted
def admitted(r: Bool & List<&2, St.Gauge>) -> Bool:
  (ok, gs) = r
  ok

# K5, K7: the checks after an act
def after(r: Bool & List<&2, St.Gauge>) -> List<&2, St.Gauge>:
  (ok, gs) = r
  gs

# K6: the run exits nonzero unless every check is confirmed
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

def exit.all(all: Bool, base: Nat, now: Nat, slots: List<&2, V.Slot>, gs: List<&2, St.Gauge>) -> Nat:
  match all:
    case True{}:
      exit.cert(Bool.or(Nat.is_eq(List.length(&2, V.Slot, slots), 0n), certified(now, gs)), base)
    case False{}:
      Nat.max(base, 1n)

# K6: the exit code of a headless run whose own code is base
def exit(base: Nat, +now: Nat, +slots: List<&2, V.Slot>, gs: List<&2, St.Gauge>) -> Nat:
  exit.all(S.all_confirmed(now, slots), base, now, slots, gs)

# K5: the gauge x with its mark replaced by m (its bar kept)
def remark(m: St.Mark, x: Maybe<&2, St.Gauge>) -> Maybe<&2, St.Gauge>:
  match x:
    case None{}:
      None{}
    case Some{g}:
      match g:
        case St.Gauge{b, old}:
          Some{St.Gauge{b, m}}

# K5: the gauge at an index after a record of m: remarked where `here`,
# else as it was
def remark_if(here: Bool, m: St.Mark, x: Maybe<&2, St.Gauge>) -> Maybe<&2, St.Gauge>:
  match here:
    case True{}:
      remark(m, x)
    case False{}:
      x

# K3, K7: the label is not certified
def is_uncertified(l: St.Label) -> Bool:
  match l:
    case St.Verified{}:
      False{}
    case St.Failed{}:
      False{}
    case St.Unverified{}:
      False{}
    case St.Passed{}:
      False{}
    case St.Uncertified{}:
      True{}

# K3, K7: the label says done (verified, or checks passed, unconfined)
def is_done(l: St.Label) -> Bool:
  match l:
    case St.Verified{}:
      True{}
    case St.Failed{}:
      False{}
    case St.Unverified{}:
      False{}
    case St.Passed{}:
      True{}
    case St.Uncertified{}:
      False{}

# K4, K7: the step ends with a label that says done
def ends_done(x: St.Step) -> Bool:
  match x:
    case St.Measure{i}:
      False{}
    case St.End{l}:
      is_done(l)
