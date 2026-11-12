# verified (spec): what the laws of area verify (laws/verify.bend) speak
# of, over the types of bend/verify.bend: when a claim of "done" is
# reported as success. A spec: the shipped code never calls it.
#
# S1: a check counts for a state only by a verdict taken on that state: a
#     slot never judged, or judged on another state, says nothing of it.
# S2: the result on a state is failed when at least one check is refuted
#     on it; verified when there is at least one check and each one is
#     confirmed on it; else unverified. So no checks is unverified.
# S3: a headless run keeps its own exit code when every check is confirmed
#     on the final state (also with no checks); else it exits nonzero: 1
#     when its own code is 0, its own code otherwise.
# S4: the verifier runs the checks in order: the next one is the first
#     that did not judge the state now. Once every check judged it, a
#     claim that is not verified but has a check (one refuted, or one
#     broken or unjudged) goes back to the worker while fewer than the cap
#     went back in a row, one count for both, then ends failed or
#     unverified; a claim with no checks ends unverified at once. A
#     return for a broken or unjudged check opens again each check whose
#     verdict on the state now is neither a confirmation nor a
#     refutation, so the next claim runs it again; every other slot stays.
# S5: the observers of a verdict, an act's reply and a step's reply the
#     laws read.

import Base
import ../../bend/verify.bend as V

# S5: the verdict is a confirmation
def passes(v: V.Verdict) -> Bool:
  match v:
    case V.Confirmed{}:
      True{}
    case V.Refuted{}:
      False{}
    case V.Broken{}:
      False{}
    case V.Unjudged{}:
      False{}

# S5: the verdict is a refutation
def fails(v: V.Verdict) -> Bool:
  match v:
    case V.Confirmed{}:
      False{}
    case V.Refuted{}:
      True{}
    case V.Broken{}:
      False{}
    case V.Unjudged{}:
      False{}

# S1: the slot judged the state now
def took(now: Nat, s: V.Slot) -> Bool:
  match s:
    case V.Open{}:
      False{}
    case V.Judged{v, at}:
      Nat.is_eq(at, now)

# S1: the slot is a confirmation taken on the state now
def confirms(now: Nat, s: V.Slot) -> Bool:
  match s:
    case V.Open{}:
      False{}
    case V.Judged{v, at}:
      Bool.and(passes(v), Nat.is_eq(at, now))

# S1: the slot is a refutation taken on the state now
def refutes(now: Nat, s: V.Slot) -> Bool:
  match s:
    case V.Open{}:
      False{}
    case V.Judged{v, at}:
      Bool.and(fails(v), Nat.is_eq(at, now))

# 1 for true, 0 for false
def bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# S2: how many checks are confirmed on the state now
def confirmed(+now: Nat, slots: List<&2, V.Slot>) -> Nat:
  match slots:
    case Nil{}:
      0n
    case Con{s, t}:
      Nat.add(bit(confirms(now, s)), confirmed(now, t))

# S2: how many checks are refuted on the state now
def refuted(+now: Nat, slots: List<&2, V.Slot>) -> Nat:
  match slots:
    case Nil{}:
      0n
    case Con{s, t}:
      Nat.add(bit(refutes(now, s)), refuted(now, t))

def label.all(all: Bool) -> V.Label:
  match all:
    case True{}:
      V.Verified{}
    case False{}:
      V.Unverified{}

# S2: the label of `bad` refuted and `good` confirmed checks out of n
def label.of(bad: Nat, good: Nat, n: Nat) -> V.Label:
  match bad:
    case 0n:
      match n:
        case 0n:
          V.Unverified{}
        case 1n+m:
          label.all(Nat.is_eq(good, 1n+m))
    case 1n+p:
      V.Failed{}

# S2: the label of the result on the state now
def label(+now: Nat, +slots: List<&2, V.Slot>) -> V.Label:
  label.of(refuted(now, slots), confirmed(now, slots), List.length(&2, V.Slot, slots))

# S3: every check is confirmed on the state now
def all_confirmed(+now: Nat, +slots: List<&2, V.Slot>) -> Bool:
  Nat.is_eq(confirmed(now, slots), List.length(&2, V.Slot, slots))

def exit.of(all: Bool, base: Nat) -> Nat:
  match all:
    case True{}:
      base
    case False{}:
      Nat.max(base, 1n)

# S3: the exit code of a headless run whose own code is base
def exit(base: Nat, now: Nat, slots: List<&2, V.Slot>) -> Nat:
  exit.of(all_confirmed(now, slots), base)

def lead.step(j: Bool, rest: Nat) -> Nat:
  match j:
    case True{}:
      1n+rest
    case False{}:
      0n

# S4: how many slots, from the first on, judged the state now with no gap:
# the index of the next check to run, when one is left
def lead(+now: Nat, slots: List<&2, V.Slot>) -> Nat:
  match slots:
    case Nil{}:
      0n
    case Con{s, t}:
      lead.step(took(now, s), lead(now, t))

# S4: the slot holds a verdict taken on the state now that is neither a
# confirmation nor a refutation
def reruns(+now: Nat, +s: V.Slot) -> Bool:
  Bool.and(took(now, s), Bool.not(Bool.or(confirms(now, s), refutes(now, s))))

def rerun.pick(open: Bool, s: V.Slot) -> V.Slot:
  match open:
    case True{}:
      V.Open{}
    case False{}:
      s

# S4: the slot at an index after a return for a broken or unjudged check,
# from the slot there before: opened when it reruns, else the same
def rerun(+now: Nat, m: Maybe<&2, V.Slot>) -> Maybe<&2, V.Slot>:
  match m:
    case None{}:
      None{}
    case Some{+s}:
      Some{rerun.pick(reruns(now, s), s)}

def undo_open.of(before: Maybe<&2, V.Slot>) -> Maybe<&2, V.Slot>:
  match before:
    case None{}:
      Some{V.Open{}}
    case Some{s}:
      Some{s}

# S5: the slot at an index after a step, with an opened slot put back as
# it was before (an opened slot where there was none stays opened): equal
# to the slot before exactly when the step kept that slot or opened it
def undo_open(after: Maybe<&2, V.Slot>, before: Maybe<&2, V.Slot>) -> Maybe<&2, V.Slot>:
  match after:
    case None{}:
      None{}
    case Some{s}:
      match s:
        case V.Open{}:
          undo_open.of(before)
        case V.Judged{v, at}:
          Some{V.Judged{v, at}}

# how many slots are open
def opens(slots: List<&2, V.Slot>) -> Nat:
  match slots:
    case Nil{}:
      0n
    case Con{s, t}:
      match s:
        case V.Open{}:
          1n+opens(t)
        case V.Judged{v, at}:
          opens(t)

# the slot at index i, if any
def nth(i: Nat, slots: List<&2, V.Slot>) -> Maybe<&2, V.Slot>:
  match i:
    case 0n:
      match slots:
        case Nil{}:
          None{}
        case Con{s, t}:
          Some{s}
    case 1n+p:
      match slots:
        case Nil{}:
          None{}
        case Con{s, t}:
          nth(p, t)

# x where `here`, else what was there
def pick(here: Bool, x: V.Slot, was: Maybe<&2, V.Slot>) -> Maybe<&2, V.Slot>:
  match here:
    case True{}:
      Some{x}
    case False{}:
      was

# S5: the slots of an acceptance
def slots(a: V.Acc) -> List<&2, V.Slot>:
  match a:
    case V.Acc{rev, slots, claimed, tries}:
      slots

# S5: the revision of an acceptance
def rev(a: V.Acc) -> Nat:
  match a:
    case V.Acc{rev, slots, claimed, tries}:
      rev

# S5: whether a claim waits
def claimed(a: V.Acc) -> Bool:
  match a:
    case V.Acc{rev, slots, claimed, tries}:
      claimed

# S5: the tries of an acceptance
def tries(a: V.Acc) -> Nat:
  match a:
    case V.Acc{rev, slots, claimed, tries}:
      tries

# S5: whether an act was admitted
def admitted(r: Bool & V.Acc) -> Bool:
  (ok, a) = r
  ok

# S5: the acceptance after an act
def after(r: Bool & V.Acc) -> V.Acc:
  (ok, a) = r
  a

# S5: the action of a verifier's step
def action(r: V.Action & V.Acc) -> V.Action:
  (x, a) = r
  x

# S5: the acceptance after a verifier's step
def stepped(r: V.Action & V.Acc) -> V.Acc:
  (x, a) = r
  a

# S5: the actor is the task's owner
def is_owner(who: V.Actor) -> Bool:
  match who:
    case V.Owner{}:
      True{}
    case V.Worker{}:
      False{}
    case V.Verifier{}:
      False{}

# S5: the actor is the harness's verifier
def is_verifier(who: V.Actor) -> Bool:
  match who:
    case V.Owner{}:
      False{}
    case V.Worker{}:
      False{}
    case V.Verifier{}:
      True{}
