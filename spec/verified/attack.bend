# verified (spec): what the laws of area attack (laws/attack.bend) speak
# of, over the types of bend/attack.bend: when done is certified with the
# attacks' outcomes, the label and the exit. A spec: the shipped code
# never calls it. The outcome of one attack (B1) is stated outcome by
# outcome by the laws of A1 in laws/attack.bend.
#
# B2: done is certified on a state with some outcomes exactly when no
#     attack survived, no check is weak or unshown on that state
#     (spec/verified/strength.bend K2), and either at least one check is
#     strong on it or two or more attacks ran clean.
# B3: the label of a result whose checks all passed (verify's verified or
#     passed) is that label when done is certified (B2), else not
#     certified; every other label (failed, unverified) stays.
# B4: a headless run exits as spec/verified/strength.bend K6 says, with
#     done certified as B2 says.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/attack.bend as At
import ./verify.bend as SV
import ./strength.bend as S

# B2: the outcome is a survivor
def survives(o: At.Outcome) -> Bool:
  match o:
    case At.Survived{}:
      True{}
    case At.Clean{}:
      False{}
    case At.Unrun{}:
      False{}

# B2: the outcome is clean
def clean(o: At.Outcome) -> Bool:
  match o:
    case At.Survived{}:
      False{}
    case At.Clean{}:
      True{}
    case At.Unrun{}:
      False{}

# B2: how many attacks survived
def survivors(os: List<&2, At.Outcome>) -> Nat:
  match os:
    case Nil{}:
      0n
    case Con{o, t}:
      Nat.add(S.bit(survives(o)), survivors(t))

# B2: how many attacks ran clean
def cleans(os: List<&2, At.Outcome>) -> Nat:
  match os:
    case Nil{}:
      0n
    case Con{o, t}:
      Nat.add(S.bit(clean(o)), cleans(t))

# B2: done is certified on the state now with the outcomes os
def certified(+now: Nat, +gs: List<&2, St.Gauge>, +os: List<&2, At.Outcome>) -> Bool:
  Bool.and(Nat.is_eq(survivors(os), 0n), Bool.and(Nat.is_eq(S.blockers(now, gs), 0n), Bool.or(Bool.not(Nat.is_eq(S.strongs(now, gs), 0n)), Nat.is_le(2n, cleans(os)))))

# B3: the label of a result whose verify label is l
def label(l: V.Label, +now: Nat, +gs: List<&2, St.Gauge>, +os: List<&2, At.Outcome>) -> St.Label:
  match l:
    case V.Verified{}:
      S.label.ok(certified(now, gs, os), St.Verified{})
    case V.Failed{}:
      St.Failed{}
    case V.Unverified{}:
      St.Unverified{}
    case V.Passed{}:
      S.label.ok(certified(now, gs, os), St.Passed{})

def exit.all(all: Bool, base: Nat, now: Nat, slots: List<&2, V.Slot>, gs: List<&2, St.Gauge>, os: List<&2, At.Outcome>) -> Nat:
  match all:
    case True{}:
      S.exit.cert(Bool.or(Nat.is_eq(List.length(&2, V.Slot, slots), 0n), certified(now, gs, os)), base)
    case False{}:
      Nat.max(base, 1n)

# B4: the exit code of a headless run whose own code is base
def exit(base: Nat, +now: Nat, +slots: List<&2, V.Slot>, gs: List<&2, St.Gauge>, os: List<&2, At.Outcome>) -> Nat:
  exit.all(SV.all_confirmed(now, slots), base, now, slots, gs, os)
