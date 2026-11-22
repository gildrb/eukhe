# attack: blind attackers on the checks (layer 2 of the strength gate).
# After every check passed and the breaks of bend/strength.bend were
# measured, fresh attackers that never saw the worker's transcript each
# write wrong code for the task that the checks may still pass, with a
# witness: a command and the output the task requires of it. An attack
# survives when the wrong code passes every gauged check, the witness
# shows it wrong (its output differs from the required one), and a judge
# that reads only the task's words agrees the required output is what the
# task asks; it is clean when it fails a check, its witness does not show
# it wrong, or the judge rejects it; it is unrun when it could not run
# (the budget, the time, a crash, no judge verdict).
#
# Survivors count like breaks: done is certified only when no attack
# survived. With a strong gauged check, attacks can only take
# certification away (an unrun attack takes nothing); a task whose checks
# are judges only (or waived) is certified only when two or more attacks
# ran clean and none survived.
#
# The outcomes `os` the model reads are those of the attacks made on the
# state now (Rust keeps each attack's state and passes only those).
#
# Rust (eukhe-core durable/acceptance/attack) asks the attackers, runs
# the attacks in scratch copies and asks this model for the outcome of
# each attack, the label and the exit code of a headless run, which
# replace bend/strength.bend's: with no attack they are its (laws
# attack_label_none_is_strength, attack_exit_none_is_strength). Entry:
# bend/ffi_attack.bend. Laws: laws/attack.bend. Pure: no IO, no @unsafe.

import Base
import ./verify.bend as V
import ./strength.bend as St

# Types
# -----

# how one attack ended
type Outcome is Data:
  Survived{}
  Clean{}
  Unrun{}

# what running one attack showed: whether it ran at all, whether the
# wrong code passed every gauged check, whether the witness's output on it
# differs from the required output, and the judge's verdict on the
# required output (None: no verdict)
type Run is Data:
  Run{ran: Bool, passes: Bool, differs: Bool, agrees: Maybe<&2, Bool>}

# The outcome of one attack
# -------------------------

def outcome.verdict(survives: Bool) -> Outcome:
  match survives:
    case True{}:
      Survived{}
    case False{}:
      Clean{}

def outcome.judged(agrees: Maybe<&2, Bool>) -> Outcome:
  match agrees:
    case None{}:
      Unrun{}
    case Some{yes}:
      outcome.verdict(yes)

def outcome.wrong(wrong: Bool, agrees: Maybe<&2, Bool>) -> Outcome:
  match wrong:
    case True{}:
      outcome.judged(agrees)
    case False{}:
      Clean{}

def outcome.ran(passes: Bool, differs: Bool, agrees: Maybe<&2, Bool>) -> Outcome:
  outcome.wrong(Bool.and(passes, differs), agrees)

# the outcome of an attack: unrun when it did not run or the judge gave
# no verdict on a wrong code that passed; survived exactly when the wrong
# code passed every gauged check, the witness shows it wrong and the judge
# agrees; clean otherwise
def outcome(r: Run) -> Outcome:
  match r:
    case Run{ran, passes, differs, agrees}:
      match ran:
        case True{}:
          outcome.ran(passes, differs, agrees)
        case False{}:
          Unrun{}

# Certified
# ---------

def is_survived(o: Outcome) -> Bool:
  match o:
    case Survived{}:
      True{}
    case Clean{}:
      False{}
    case Unrun{}:
      False{}

def is_clean(o: Outcome) -> Bool:
  match o:
    case Survived{}:
      False{}
    case Clean{}:
      True{}
    case Unrun{}:
      False{}

# some attack survived
def survived(os: List<&2, Outcome>) -> Bool:
  match os:
    case Nil{}:
      False{}
    case Con{o, t}:
      Bool.or(is_survived(o), survived(t))

def cleans.add(clean: Bool, rest: Nat) -> Nat:
  match clean:
    case True{}:
      1n+rest
    case False{}:
      rest

# the attacks that ran clean
def cleans(os: List<&2, Outcome>) -> Nat:
  match os:
    case Nil{}:
      0n
    case Con{o, t}:
      cleans.add(is_clean(o), cleans(t))

# the clean attacks a task needs when no check was shown to catch broken
# code
def needed() -> Nat:
  2n

# done is certified on `now` with the attacks' outcomes `os`: no attack
# survived, and either some check was shown to catch broken code with
# none weak or unshown (bend/strength.bend certified), or none is weak or
# unshown and enough attacks ran clean
def certified(+now: Nat, +gs: List<&2, St.Gauge>, +os: List<&2, Outcome>) -> Bool:
  Bool.and(
    Bool.not(survived(os)),
    Bool.or(
      St.certified(now, gs),
      Bool.and(St.clear(now, gs), Nat.is_le(needed(), cleans(os)))))

# The label and the exit
# ----------------------

# the label of a result whose verify label is `l`: bend/strength.bend's,
# with done certified as above
def label(+l: V.Label, +now: Nat, +gs: List<&2, St.Gauge>, +os: List<&2, Outcome>) -> St.Label:
  St.label.pass(St.passes(l), certified(now, gs, os), l)

def exit.held(held: Bool, base: Nat, +now: Nat, +slots: List<&2, V.Slot>, +gs: List<&2, St.Gauge>, +os: List<&2, Outcome>) -> Nat:
  match held:
    case True{}:
      St.exit.cert(Bool.or(Bool.not(V.some(slots)), certified(now, gs, os)), base)
    case False{}:
      V.exit.code(False{}, base)

# the exit code of a headless run whose own code is `base`:
# bend/strength.bend's, with done certified as above
def exit(base: Nat, +now: Nat, +slots: List<&2, V.Slot>, +gs: List<&2, St.Gauge>, +os: List<&2, Outcome>) -> Nat:
  exit.held(V.holds(now, slots), base, now, slots, gs, os)
