# verify: verified completion. "Done" is a claim; the harness reports it as
# success only when an independent check confirmed it on the final state.
# A task carries acceptance checks its owner set (a command with an
# expected exit code, a condition a judge decides on evidence, a loop's
# until-condition). Each check has a slot: its last verdict and the state
# it judged. The state is a number that changes with every effect of the
# worker, every new message of the user and every change of the
# workspace (Rust: the newest tool result and the newest user message of
# the conversation, and a fingerprint of the workspace: git HEAD, the
# diff, the hashes of the untracked files), so a verdict taken before the
# last change no longer counts.
#
# Rust (eukhe-core durable/acceptance) keeps the acceptance in the session
# (the `eukhe.acceptance` document), gathers the evidence (runs the
# command, asks the judge) and asks this model for every decision: the
# verdict of a piece of evidence (grade_command, grade_until, grade_judge),
# who may change what (act), whether a final answer is a claim (claims),
# what the verifier does next (advance), the label of the result (label)
# and the exit code of a headless run (exit). Whether programs run
# confined (confined) decides between the two labels of a result whose
# every check is confirmed: no confinement exists yet, so no result is
# labelled verified.
# Entry: bend/ffi_verify.bend. Laws: laws/verify.bend. Spec:
# spec/verified/verify.bend. Pure: no IO, no @unsafe.

import Base

# Types
# -----

# the verdict of one check on one state: confirmed, refuted, broken (the
# check itself failed to judge: never read as true or false), unjudged
# (nothing learned). The loop pillar's until-check uses the same four
# verdicts with the same wire tags 0..3.
type Verdict is Data:
  Confirmed{}
  Refuted{}
  Broken{}
  Unjudged{}

# what the harness saw of a check's command: it exited with a code, ended
# with no status (a signal), ran past its time limit, could not start, or
# was cancelled
type Evidence is Data:
  Exited{code: Nat}
  NoStatus{}
  TimedOut{}
  SpawnFailed{}
  Cancelled{}

# what the judge answered: an explicit yes or no, a reply with neither, no
# reply at all (the request failed or was refused), or a cancelled request
type Answer is Data:
  Yes{}
  No{}
  Unreadable{}
  Unavailable{}
  Stopped{}

# the slot of one check: never judged, or its last verdict and the state it
# judged
type Slot is Data:
  Open{}
  Judged{verdict: Verdict, at: Nat}

# who acts: the task's owner (the user, an SDK client, the CLI, the parent
# that assigned the task), the worker that does the task, the harness's
# verifier
type Actor is Data:
  Owner{}
  Worker{}
  Verifier{}

# an act: set the task's checks (n of them), claim the task done, record
# the verdict of check `index` of the checks of revision `rev` on state
# `at`
type Op is Data:
  Assign{n: Nat}
  Claim{}
  Record{rev: Nat, index: Nat, verdict: Verdict, at: Nat}

# the acceptance of one task: the revision of its checks (it grows with
# every Assign), one slot per check, whether a claim waits for its
# verdict, how many times in a row a claim went back to the worker (a
# refuted one, or one with a broken or unjudged check)
type Acc is Data:
  Acc{rev: Nat, slots: List<&2, Slot>, claimed: Bool, tries: Nat}

# the label of a result: verified (every check confirmed, programs run
# confined), failed, unverified, or passed (every check confirmed,
# programs run unconfined: "checks passed, unconfined")
type Label is Data:
  Verified{}
  Failed{}
  Unverified{}
  Passed{}

# what the verifier does next: nothing (no claim waits), run the check at
# `index`, give the evidence back to the worker, end the claim with a label
type Action is Data:
  Rest{}
  Run{index: Nat}
  Return{}
  End{label: Label}

# The verdict of a piece of evidence
# ----------------------------------

def grade_exit(same: Bool) -> Verdict:
  match same:
    case True{}:
      Confirmed{}
    case False{}:
      Refuted{}

# the verdict of a command whose protected files are intact
def grade_run(expect: Nat, ev: Evidence) -> Verdict:
  match ev:
    case Exited{code}:
      grade_exit(Nat.is_eq(code, expect))
    case NoStatus{}:
      Broken{}
    case TimedOut{}:
      Broken{}
    case SpawnFailed{}:
      Broken{}
    case Cancelled{}:
      Unjudged{}

# the verdict of a command check: `expect` is the exit code its owner
# expects, `intact` whether every file the check protects is as the owner
# left it. A changed protected file refutes the check whatever the command
# did.
def grade_command(expect: Nat, intact: Bool, ev: Evidence) -> Verdict:
  match intact:
    case True{}:
      grade_run(expect, ev)
    case False{}:
      Refuted{}

# exit 126 (found, not executable) or 127 (not found): the shell could not
# run the command
def cannot_run(+code: Nat) -> Bool:
  Bool.or(Nat.is_eq(code, 126n), Nat.is_eq(code, 127n))

def grade_until.nonzero(broke: Bool) -> Verdict:
  match broke:
    case True{}:
      Broken{}
    case False{}:
      Refuted{}

def grade_until.code(code: Nat) -> Verdict:
  match code:
    case 0n:
      Confirmed{}
    case 1n+p:
      grade_until.nonzero(cannot_run(1n+p))

# the verdict of a loop's until-condition (a shell command): exit 0 holds,
# any other exit does not hold yet, except 126 and 127 (the shell could
# not run it), which, like no status, a timeout or a failed start, are
# the condition breaking
def grade_until(ev: Evidence) -> Verdict:
  match ev:
    case Exited{code}:
      grade_until.code(code)
    case NoStatus{}:
      Broken{}
    case TimedOut{}:
      Broken{}
    case SpawnFailed{}:
      Broken{}
    case Cancelled{}:
      Unjudged{}

# the verdict of a judge's answer
def grade_judge(ans: Answer) -> Verdict:
  match ans:
    case Yes{}:
      Confirmed{}
    case No{}:
      Refuted{}
    case Unreadable{}:
      Broken{}
    case Unavailable{}:
      Broken{}
    case Stopped{}:
      Unjudged{}

# The label of a result
# ---------------------

def seen.at(same: Bool, v: Verdict) -> Verdict:
  match same:
    case True{}:
      v
    case False{}:
      Unjudged{}

# what a slot says of the state `now`: its verdict when it judged that
# state; nothing (Unjudged) when it never judged or judged another state
def seen(now: Nat, s: Slot) -> Verdict:
  match s:
    case Open{}:
      Unjudged{}
    case Judged{v, at}:
      seen.at(Nat.is_eq(at, now), v)

def is_confirmed(v: Verdict) -> Bool:
  match v:
    case Confirmed{}:
      True{}
    case Refuted{}:
      False{}
    case Broken{}:
      False{}
    case Unjudged{}:
      False{}

def is_refuted(v: Verdict) -> Bool:
  match v:
    case Confirmed{}:
      False{}
    case Refuted{}:
      True{}
    case Broken{}:
      False{}
    case Unjudged{}:
      False{}

# every check is confirmed on the state `now` (true of no checks)
def holds(+now: Nat, slots: List<&2, Slot>) -> Bool:
  match slots:
    case Nil{}:
      True{}
    case Con{s, t}:
      Bool.and(is_confirmed(seen(now, s)), holds(now, t))

# some check is refuted on the state `now`
def refuted(+now: Nat, slots: List<&2, Slot>) -> Bool:
  match slots:
    case Nil{}:
      False{}
    case Con{s, t}:
      Bool.or(is_refuted(seen(now, s)), refuted(now, t))

# there is a check
def some(slots: List<&2, Slot>) -> Bool:
  match slots:
    case Nil{}:
      False{}
    case Con{s, t}:
      True{}

# whether the programs a run starts (its tools, its checks) run confined:
# no confinement mechanism exists (spec/security C9), so they never do
def confined() -> Bool:
  False{}

# the label of a result whose every check is confirmed: verified only
# when programs run confined
def label.good(conf: Bool) -> Label:
  match conf:
    case True{}:
      Verified{}
    case False{}:
      Passed{}

def label.of(conf: Bool, bad: Bool, good: Bool) -> Label:
  match bad:
    case True{}:
      Failed{}
    case False{}:
      match good:
        case True{}:
          label.good(conf)
        case False{}:
          Unverified{}

# the label of the result on the state `now`, programs run confined when
# `conf`: failed when a check is refuted on it; when there is a check and
# every check is confirmed on it, verified when `conf` and passed (checks
# passed, unconfined) when not; else unverified
def label(+conf: Bool, +now: Nat, +slots: List<&2, Slot>) -> Label:
  label.of(conf, refuted(now, slots), Bool.and(some(slots), holds(now, slots)))

def exit.code(ok: Bool, base: Nat) -> Nat:
  match ok:
    case True{}:
      base
    case False{}:
      match base:
        case 0n:
          1n
        case 1n+p:
          1n+p

# the exit code of a headless run whose own code is `base`: `base` when
# every check is confirmed on the final state (also with no checks), else
# nonzero
def exit(base: Nat, now: Nat, slots: List<&2, Slot>) -> Nat:
  exit.code(holds(now, slots), base)

# Who may change what
# -------------------

# n open slots
def opens(n: Nat) -> List<&2, Slot>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Open{} <> opens(p)

def put.cons(h: Slot, r: Maybe<&2, List<&2, Slot>>) -> Maybe<&2, List<&2, Slot>>:
  match r:
    case None{}:
      None{}
    case Some{t}:
      Some{h <> t}

# `slots` with the slot at index i replaced by s; None when there is none
def put(i: Nat, s: Slot, slots: List<&2, Slot>) -> Maybe<&2, List<&2, Slot>>:
  match i:
    case 0n:
      match slots:
        case Nil{}:
          None{}
        case Con{h, t}:
          Some{s <> t}
    case 1n+p:
      match slots:
        case Nil{}:
          None{}
        case Con{h, t}:
          put.cons(h, put(p, s, t))

# the most checks a task may carry
def max_checks() -> Nat:
  64n

def act.assign.fits(few: Bool, n: Nat, a: Acc) -> Bool & Acc:
  match few:
    case True{}:
      match a:
        case Acc{rev, slots, claimed, tries}:
          (True{}, Acc{1n+rev, opens(n), False{}, 0n})
    case False{}:
      (False{}, a)

# only the owner sets the checks, at most max_checks of them: the new
# revision starts with every slot open, no claim, no tries
def act.assign(who: Actor, +n: Nat, a: Acc) -> Bool & Acc:
  match who:
    case Owner{}:
      act.assign.fits(Nat.is_le(n, max_checks()), n, a)
    case Worker{}:
      (False{}, a)
    case Verifier{}:
      (False{}, a)

# anyone may claim the task done: the claim waits for its verdict
def act.claim(a: Acc) -> Bool & Acc:
  match a:
    case Acc{rev, slots, claimed, tries}:
      (True{}, Acc{rev, slots, True{}, tries})

def act.put(r: Maybe<&2, List<&2, Slot>>, rev: Nat, old: List<&2, Slot>, claimed: Bool, tries: Nat) -> Bool & Acc:
  match r:
    case None{}:
      (False{}, Acc{rev, old, claimed, tries})
    case Some{slots}:
      (True{}, Acc{rev, slots, claimed, tries})

def act.stamp(same: Bool, i: Nat, s: Slot, rev: Nat, +slots: List<&2, Slot>, claimed: Bool, tries: Nat) -> Bool & Acc:
  match same:
    case True{}:
      act.put(put(i, s, slots), rev, slots, claimed, tries)
    case False{}:
      (False{}, Acc{rev, slots, claimed, tries})

# only the verifier records a verdict, only for a check of the current
# revision
def act.record(who: Actor, of: Nat, i: Nat, s: Slot, a: Acc) -> Bool & Acc:
  match who:
    case Owner{}:
      (False{}, a)
    case Worker{}:
      (False{}, a)
    case Verifier{}:
      match a:
        case Acc{+rev, slots, claimed, tries}:
          act.stamp(Nat.is_eq(of, rev), i, s, rev, slots, claimed, tries)

# one act of `who` on the acceptance `a`: whether it is admitted, and the
# acceptance after it (`a` itself when refused)
def act(who: Actor, op: Op, a: Acc) -> Bool & Acc:
  match op:
    case Assign{n}:
      act.assign(who, n, a)
    case Claim{}:
      act.claim(a)
    case Record{of, i, v, at}:
      act.record(who, of, i, Judged{v, at}, a)

# What the verifier does next
# ---------------------------

# the slot judged the state `now`
def judged(now: Nat, s: Slot) -> Bool:
  match s:
    case Open{}:
      False{}
    case Judged{v, at}:
      Nat.is_eq(at, now)

def due.pick(done: Bool, i: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match done:
    case True{}:
      rest
    case False{}:
      Some{i}

# the index, counted from i, of the first slot that did not judge the
# state `now`; None when every slot did
def due(+now: Nat, slots: List<&2, Slot>, +i: Nat) -> Maybe<&2, Nat>:
  match slots:
    case Nil{}:
      None{}
    case Con{s, t}:
      due.pick(judged(now, s), i, due(now, t, 1n+i))

def settle.failed(room: Bool, rev: Nat, slots: List<&2, Slot>, tries: Nat) -> Action & Acc:
  match room:
    case True{}:
      (Return{}, Acc{rev, slots, False{}, 1n+tries})
    case False{}:
      (End{Failed{}}, Acc{rev, slots, False{}, 0n})

# a verdict that says nothing of the work: broken or unjudged
def retry(v: Verdict) -> Bool:
  match v:
    case Confirmed{}:
      False{}
    case Refuted{}:
      False{}
    case Broken{}:
      True{}
    case Unjudged{}:
      True{}

# the slot holds a broken or unjudged verdict on the state now
def again(now: Nat, s: Slot) -> Bool:
  match s:
    case Open{}:
      False{}
    case Judged{v, at}:
      Bool.and(retry(v), Nat.is_eq(at, now))

def reopen.pick(open: Bool, s: Slot) -> Slot:
  match open:
    case True{}:
      Open{}
    case False{}:
      s

# the slots with every check broken or unjudged on the state now open
# again, so the next claim runs it again even on the same state; every
# other slot stays
def reopen(+now: Nat, slots: List<&2, Slot>) -> List<&2, Slot>:
  match slots:
    case Nil{}:
      Nil{}
    case Con{+s, t}:
      reopen.pick(again(now, s), s) <> reopen(now, t)

def settle.broken(room: Bool, now: Nat, rev: Nat, slots: List<&2, Slot>, tries: Nat) -> Action & Acc:
  match room:
    case True{}:
      (Return{}, Acc{rev, reopen(now, slots), False{}, 1n+tries})
    case False{}:
      (End{Unverified{}}, Acc{rev, slots, False{}, 0n})

# an unverified claim: with a check (one is broken or unjudged on the
# final state) it goes back to the worker like a refuted one; with none it
# ends at once
def settle.open(any: Bool, room: Bool, now: Nat, rev: Nat, slots: List<&2, Slot>, tries: Nat) -> Action & Acc:
  match any:
    case True{}:
      settle.broken(room, now, rev, slots, tries)
    case False{}:
      (End{Unverified{}}, Acc{rev, slots, False{}, 0n})

# the end of a claim whose every check judged the final state `now`: a
# verified claim ends verified, a passed one passed; a refuted one, or one
# with a broken or unjudged check, goes back to the worker while fewer
# than `cap` went back in a row (one count for both), then ends failed or
# unverified; a claim with no checks ends unverified at once. A return for
# a broken or unjudged check opens those checks again; a return for a
# refuted one keeps every slot. An end clears the tries.
def settle(l: Label, now: Nat, cap: Nat, rev: Nat, +slots: List<&2, Slot>, +tries: Nat) -> Action & Acc:
  match l:
    case Verified{}:
      (End{Verified{}}, Acc{rev, slots, False{}, 0n})
    case Failed{}:
      settle.failed(Nat.is_lt(tries, cap), rev, slots, tries)
    case Unverified{}:
      settle.open(some(slots), Nat.is_lt(tries, cap), now, rev, slots, tries)
    case Passed{}:
      (End{Passed{}}, Acc{rev, slots, False{}, 0n})

def advance.go(conf: Bool, d: Maybe<&2, Nat>, +now: Nat, cap: Nat, rev: Nat, +slots: List<&2, Slot>, tries: Nat) -> Action & Acc:
  match d:
    case Some{i}:
      (Run{i}, Acc{rev, slots, True{}, tries})
    case None{}:
      settle(label(conf, now, slots), now, cap, rev, slots, tries)

# one step of the verifier on the state `now`, programs run confined when
# `conf`: without a claim it rests; with one it runs the first check that
# did not judge `now`, and once every check did, it settles the claim
def advance(conf: Bool, +now: Nat, cap: Nat, a: Acc) -> Action & Acc:
  match a:
    case Acc{rev, +slots, claimed, tries}:
      match claimed:
        case False{}:
          (Rest{}, Acc{rev, slots, False{}, tries})
        case True{}:
          advance.go(conf, due(now, slots, 0n), now, cap, rev, slots, tries)

# Whether a final answer is a claim
# ---------------------------------

def claims.fresh(ended: Bool) -> Bool:
  match ended:
    case True{}:
      False{}
    case False{}:
      True{}

def claims.own(goal: Bool, ended: Bool) -> Bool:
  match goal:
    case True{}:
      False{}
    case False{}:
      claims.fresh(ended)

def claims.open(checked: Bool, goal: Bool, ended: Bool) -> Bool:
  match checked:
    case True{}:
      claims.own(goal, ended)
    case False{}:
      False{}

def claims.free(claimed: Bool, checked: Bool, goal: Bool, ended: Bool) -> Bool:
  match claimed:
    case True{}:
      True{}
    case False{}:
      claims.open(checked, goal, ended)

# whether the verifier judges a claim at a final answer. `held`: queued
# input or running work owns the next boundary (the run it starts reaches
# its own final answer). `checked`: the task has a check. `goal`: an active
# goal drives the run (it claims with goal.complete(), not by answering).
# `claimed`: a claim already waits. `ended`: the last claim ended on the
# state now (that verdict stands until the state or the checks change).
def claims(held: Bool, checked: Bool, goal: Bool, claimed: Bool, ended: Bool) -> Bool:
  match held:
    case True{}:
      False{}
    case False{}:
      claims.free(claimed, checked, goal, ended)
