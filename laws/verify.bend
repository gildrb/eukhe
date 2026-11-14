# eukhe: the laws of area verify

import Base
import ../bend/verify.bend as V
import ../bend/ffi_verify.bend as FV
import ../bend/wire.bend as Wr
import ../spec/verified/verify.bend as S
import ../spec/verified/verify_wire.bend as SW
import ./base.bend as LawsBase

# (V1-V10) "Done" is a claim an independent check must confirm
# ------------------------------------------------------------
# spec/README.md V1-V10. bend/verify.bend: a task carries acceptance
# checks its owner set; each check has a slot (its last verdict and the
# state it judged); the worker claims the task done; the harness's
# verifier gathers the evidence of each check on the final state and
# records its verdict; the result is reported as success only when every
# check is confirmed on that state. The state is a number that changes
# with every effect of the worker, every new message of the user and
# every change of the workspace (Rust: the newest tool result, the newest
# user message and a fingerprint of the workspace). The model runs as the compiled core by
# bend/ffi_verify.bend (eukhe-bend rules/verify.rs), asked by eukhe-core
# durable/acceptance for every decision and by eukhe-cli print_runtime for
# the exit code. spec/verified/verify.bend restates the rules (S1-S5).
# Every input is free unless a law names a premise.
#
# R1 (V2): the verdict of a piece of evidence. A command check is
#     confirmed exactly when its protected files are intact and the
#     command exited with the expected code; refuted when a protected file
#     changed or the command exited with another code; broken when the
#     command gave no exit code (no status, a timeout, it could not
#     start); unjudged when it was cancelled. A loop's until-condition is
#     confirmed by exit 0, refuted by exit 1, broken by any other end,
#     unjudged when cancelled. A judge confirms only by an explicit yes
#     and refutes only by an explicit no; an unreadable or missing answer
#     is broken, a stopped request unjudged.
# R2 (V3, V4): the label of a result on a state, the programs of the run
#     run confined or not: failed exactly when a check is refuted on that
#     state; else, when there is at least one check and every check is
#     confirmed on it, verified when programs run confined and passed
#     ("checks passed, unconfined") when they run unconfined; else
#     unverified. The label never exceeds the evidence: a check never
#     judged, judged on an earlier state, broken or unjudged never counts
#     as confirmed; with no checks the label is unverified; verified needs
#     confinement; the unconfined qualifier is there exactly when programs
#     run unconfined.
# R3 (V5): who may change what. Only the owner sets the checks, at most
#     64 of them, and a set starts a new revision with every slot open, no
#     claim and no tries.
#     Only the verifier records a verdict, only for a check of the current
#     revision that exists, and it changes that one slot only. A claim
#     changes no verdict. No act of the worker changes a verdict or the
#     revision. A refused act changes nothing.
# R4 (V3, V7): the verifier's step. Without a claim it rests. With one it
#     runs the first check that did not judge the state now. Once every
#     check did: a verified claim ends verified and a passed one passed; a
#     refuted one goes back to the worker while fewer than `cap` did in a
#     row (the tries grow by one), then ends failed; one with a broken or
#     unjudged check and none refuted goes back the same way (the same
#     tries) with every check broken or unjudged on the state now open
#     again (so the next claim runs it again), then ends unverified; a
#     claim with no checks ends unverified at once. Every end clears the
#     claim and the tries. It says verified only when the label is
#     verified and passed only when the label is passed, and it never
#     writes a verdict: every slot after a step is the slot before or that
#     check opened again.
# R5 (V10): the exit code of a headless run: its own code when every
#     check is confirmed on the final state (also with no checks), else
#     nonzero; a nonzero own code is kept.
# R7 (V3): when a final answer is a claim the verifier judges. Never
#     while queued input or running work owns the next boundary. Else a
#     claim that already waits is always judged; without one, a task
#     with no check, an active goal (it claims with `goal.complete()`)
#     and a state the last claim ended on are no claim; any other final
#     answer of a task with checks is one.
# R6: the entry answers each request Rust writes with the model's
#     decision, reads exactly the request and nothing after it, and
#     answers any other input with the exact error form
#     `E verify: malformed request`.
# R8 (V4): no confinement exists: until it does, programs never run
#     confined, so no label and no end of a claim the entry gives says
#     verified.
#
# Not pinned here: how Rust gathers the evidence (runs the command, hashes
# the protected files, asks the judge and reads its first word), that the
# judge's request holds the evidence and not the worker's words, that the
# intent judge reads the user's own messages, that the state number
# changes with the worker's effects, the user's messages and the
# workspace, that the goal is what the conversation currently asks for
# (V11) and that a parent sets its child's checks and reads its verdict
# (V12): the Rust tests (durable/acceptance/tests.rs,
# durable/children/tests.rs, acceptance_e2e) cover them.

# Spec helpers
# ------------

# the label is verified
def sp_is_verified(l: V.Label) -> Bool:
  match l:
    case V.Verified{}:
      True{}
    case V.Failed{}:
      False{}
    case V.Unverified{}:
      False{}
    case V.Passed{}:
      False{}

# the label is failed
def sp_is_failed(l: V.Label) -> Bool:
  match l:
    case V.Verified{}:
      False{}
    case V.Failed{}:
      True{}
    case V.Unverified{}:
      False{}
    case V.Passed{}:
      False{}

# the label is passed: checks passed, unconfined
def sp_is_passed(l: V.Label) -> Bool:
  match l:
    case V.Verified{}:
      False{}
    case V.Failed{}:
      False{}
    case V.Unverified{}:
      False{}
    case V.Passed{}:
      True{}

# the label reports every check confirmed: verified or passed
def sp_succeeds(l: V.Label) -> Bool:
  match l:
    case V.Verified{}:
      True{}
    case V.Failed{}:
      False{}
    case V.Unverified{}:
      False{}
    case V.Passed{}:
      True{}

# the action ends a claim verified
def sp_ends_verified(x: V.Action) -> Bool:
  match x:
    case V.Rest{}:
      False{}
    case V.Run{i}:
      False{}
    case V.Return{}:
      False{}
    case V.End{l}:
      sp_is_verified(l)

# `pre`, then the slot s, then `post`
def sp_around(pre: List<&2, V.Slot>, s: V.Slot, post: List<&2, V.Slot>) -> List<&2, V.Slot>:
  List.append(&2, V.Slot, pre, s <> post)

# n slots, each a confirmation taken on the state now
def sp_all_pass(n: Nat, +now: Nat) -> List<&2, V.Slot>:
  List.replicate(V.Slot, n, V.Judged{V.Confirmed{}, now})

# Laws: the verdict of a piece of evidence (R1)
# ---------------------------------------------

# LAW verify_command_expected_exit_confirms (R1): a command whose
# protected files are intact and that exits with the expected code is
# confirmed, for every expected code
# EXCLUDES: a check that only passes on exit 0 whatever its owner expects,
#   a check that never passes
law verify_command_expected_exit_confirms:
  for +e: Nat
  {V.grade_command(e, True{}, V.Exited{e}) == V.Confirmed{} : V.Verdict}

# LAW verify_command_other_exit_refutes (R1): a command that exits with
# any code but the expected one is refuted
# EXCLUDES: a failed test run (exit 1, exit 101) read as passed or as
#   broken, an expected code ignored
law verify_command_other_exit_refutes:
  for +e: Nat
  for +c: Nat
  for other: {Nat.is_eq(c, e) == False{} : Bool}
  {V.grade_command(e, True{}, V.Exited{c}) == V.Refuted{} : V.Verdict}

# LAW verify_command_tampered_refutes (R1): a check whose protected file
# changed is refuted whatever its command did, for every expected code and
# every evidence
# EXCLUDES: a worker that edits the test file until the command passes, a
#   tampered check read as broken or unjudged
law verify_command_tampered_refutes:
  for e: Nat
  for ev: V.Evidence
  {V.grade_command(e, False{}, ev) == V.Refuted{} : V.Verdict}

# LAW verify_command_no_exit_table (R1): the rows of a command that gave
# no exit code, protected files intact, for every expected code; each row
# cites spec/README.md V2
# EXCLUDES: a timeout or a spawn failure read as passed or as failed, a
#   cancelled check read as anything learned
law verify_command_no_exit_table:
  for e: Nat
  {V.grade_command(e, True{}, V.NoStatus{}) == V.Broken{} : V.Verdict} &    # V2: no exit status: broken
  {V.grade_command(e, True{}, V.TimedOut{}) == V.Broken{} : V.Verdict} &    # V2: a timeout: broken
  {V.grade_command(e, True{}, V.SpawnFailed{}) == V.Broken{} : V.Verdict} & # V2: could not start: broken
  {V.grade_command(e, True{}, V.Cancelled{}) == V.Unjudged{} : V.Verdict}   # V2: cancelled: unjudged

# LAW verify_until_table (R1): the rows of a loop's until-condition; each
# row cites spec/README.md V2
# EXCLUDES: exit 2 (a broken condition) read as "not yet", a timeout read
#   as satisfied, a cancelled condition read as an answer
law verify_until_table:
  for p: Nat
  {V.grade_until(V.Exited{0n}) == V.Confirmed{} : V.Verdict} &   # V2: exit 0: the condition holds
  {V.grade_until(V.Exited{1n}) == V.Refuted{} : V.Verdict} &     # V2: exit 1: not yet, the loop goes on
  {V.grade_until(V.Exited{2n+p}) == V.Broken{} : V.Verdict} &    # V2: exit above 1: the condition broke
  {V.grade_until(V.NoStatus{}) == V.Broken{} : V.Verdict} &      # V2: no exit status: broken
  {V.grade_until(V.TimedOut{}) == V.Broken{} : V.Verdict} &      # V2: a timeout: broken
  {V.grade_until(V.SpawnFailed{}) == V.Broken{} : V.Verdict} &   # V2: could not start: broken
  {V.grade_until(V.Cancelled{}) == V.Unjudged{} : V.Verdict}     # V2: cancelled: unjudged

# LAW verify_judge_table (R1): the rows of a judge's answer; each row
# cites spec/README.md V2
# EXCLUDES: a judge reply with no verdict read as a pass, a failed judge
#   request read as a pass or as a fail
law verify_judge_table:
  {V.grade_judge(V.Yes{}) == V.Confirmed{} : V.Verdict} &       # V2: an explicit yes confirms
  {V.grade_judge(V.No{}) == V.Refuted{} : V.Verdict} &          # V2: an explicit no refutes
  {V.grade_judge(V.Unreadable{}) == V.Broken{} : V.Verdict} &   # V2: neither yes nor no: broken
  {V.grade_judge(V.Unavailable{}) == V.Broken{} : V.Verdict} &  # V2: no reply: broken
  {V.grade_judge(V.Stopped{}) == V.Unjudged{} : V.Verdict}      # V2: a cancelled request: unjudged

# Laws: the label of a result (R2)
# --------------------------------

# LAW verify_label_is_spec (R2): the label of every list of slots on
# every state, programs run confined or not, is the spec's: by the counts
# of the checks confirmed and refuted on that state and by confinement
# (spec/verified/verify.bend S2)
# EXCLUDES: a label that reads a verdict of another state, a broken or
#   unjudged check counted as confirmed or as refuted, verified with no
#   checks, failed and verified mixed up, verified while programs run
#   unconfined, passed while they run confined
law verify_label_is_spec:
  for +conf: Bool
  for +now: Nat
  for +slots: List<&2, V.Slot>
  {V.label(conf, now, slots) == S.label(conf, now, slots) : V.Label}

# LAW verify_no_checks_unverified (R2): with no checks the label is
# unverified on every state, programs run confined or not
# EXCLUDES: a task with no acceptance checks reported as verified or as
#   passed
law verify_no_checks_unverified:
  for conf: Bool
  for now: Nat
  {V.label(conf, now, Nil{}) == V.Unverified{} : V.Label}

# LAW verify_unconfirmed_check_never_verified (R2): one check that is not
# a confirmation taken on the state now (never judged, judged on another
# state, refuted, broken, unjudged), anywhere among the checks, keeps the
# label from verified and from passed, programs run confined or not
# EXCLUDES: a pass on an earlier state counted after the worker's later
#   effect, a skipped check, a majority of passes read as verified or as
#   passed
law verify_unconfirmed_check_never_verified:
  for conf: Bool
  for +now: Nat
  for +pre: List<&2, V.Slot>
  for +s: V.Slot
  for post: List<&2, V.Slot>
  for un: {S.confirms(now, s) == False{} : Bool}
  {sp_succeeds(V.label(conf, now, sp_around(pre, s, post))) == False{} : Bool}

# LAW verify_all_confirmed_verifies (R2): one or more checks, each
# confirmed on the state now, of a run whose programs run confined, are
# verified
# EXCLUDES: a label that never says verified, a label that wants more
#   than every check confirmed on the final state and confinement
law verify_all_confirmed_verifies:
  for +now: Nat
  for +n: Nat
  {V.label(True{}, now, sp_all_pass(1n+n, now)) == V.Verified{} : V.Label}

# LAW verify_all_confirmed_unconfined_passes (R2): one or more checks,
# each confirmed on the state now, of a run whose programs run
# unconfined, are passed (checks passed, unconfined)
# EXCLUDES: a run whose checks all passed while unconfined reported as
#   verified, as unverified or as failed
law verify_all_confirmed_unconfined_passes:
  for +now: Nat
  for +n: Nat
  {V.label(False{}, now, sp_all_pass(1n+n, now)) == V.Passed{} : V.Label}

# LAW verify_unconfined_qualifier_exact (R2): on every list of slots and
# state, the label is passed exactly when programs run unconfined and the
# label reports every check confirmed, and verified exactly when they run
# confined and it does: the unconfined qualifier is there exactly when
# confinement is not in force, and verified needs confinement
# EXCLUDES: verified while programs run unconfined, the qualifier on a
#   confined run, a label that ignores confinement
law verify_unconfined_qualifier_exact:
  for +conf: Bool
  for +now: Nat
  for +slots: List<&2, V.Slot>
  {sp_is_passed(V.label(conf, now, slots)) == Bool.and(Bool.not(conf), sp_succeeds(V.label(conf, now, slots))) : Bool} &
  {sp_is_verified(V.label(conf, now, slots)) == Bool.and(conf, sp_succeeds(V.label(conf, now, slots))) : Bool}

# LAW verify_refuted_check_fails (R2): one check refuted on the state
# now, anywhere among the checks, makes the label failed, programs run
# confined or not
# EXCLUDES: a refuted check hidden by the passes around it, a refuted
#   check read as unverified
law verify_refuted_check_fails:
  for conf: Bool
  for +now: Nat
  for +pre: List<&2, V.Slot>
  for post: List<&2, V.Slot>
  {V.label(conf, now, sp_around(pre, V.Judged{V.Refuted{}, now}, post)) == V.Failed{} : V.Label}

# LAW verify_failed_needs_refuted (R2): with no check refuted on the
# state now the label is not failed, programs run confined or not
# EXCLUDES: a broken or unjudged check read as a failure, a stale
#   refutation that still fails the result
law verify_failed_needs_refuted:
  for conf: Bool
  for +now: Nat
  for +slots: List<&2, V.Slot>
  for none: {S.refuted(now, slots) == 0n : Nat}
  {sp_is_failed(V.label(conf, now, slots)) == False{} : Bool}

# Laws: no confinement yet (R8)
# -----------------------------

# LAW verify_unconfined_never_verified (R8): while no confinement exists,
# no label of any slots on any state is verified, and no step of the
# verifier ends a claim verified
# EXCLUDES: a core that declares confinement in force with no mechanism,
#   a step that ends a claim verified whatever confinement says
law verify_unconfined_never_verified:
  for +now: Nat
  for +slots: List<&2, V.Slot>
  for cap: Nat
  for a: V.Acc
  {sp_is_verified(V.label(V.confined(), now, slots)) == False{} : Bool} &
  {sp_ends_verified(S.action(V.advance(V.confined(), now, cap, a))) == False{} : Bool}

# Laws: who may change what (R3)
# ------------------------------

# LAW verify_assign_needs_owner (R3): an Assign of anyone but the owner
# is refused and changes nothing
# EXCLUDES: a worker that drops, replaces or empties its own checks
law verify_assign_needs_owner:
  for who: V.Actor
  for n: Nat
  for +a: V.Acc
  for other: {S.is_owner(who) == False{} : Bool}
  {V.act(who, V.Assign{n}, a) == (False{}, a) : Bool & V.Acc}

# LAW verify_assign_too_many_refused (R3): the owner's Assign of more
# than 64 checks, the most a task may carry (spec/README.md V1), is
# refused and changes nothing
# EXCLUDES: a set of checks too large to run that replaces the checks, a
#   refused set that still clears the verdicts
law verify_assign_too_many_refused:
  for +n: Nat
  for +a: V.Acc
  for many: {Nat.is_le(n, 64n) == False{} : Bool}
  {V.act(V.Owner{}, V.Assign{n}, a) == (False{}, a) : Bool & V.Acc}

# LAW verify_assign_resets (R3): the owner's Assign of n checks, at most
# 64 (spec/README.md V1), is admitted and starts the next revision: n
# slots, all open, no claim, no tries
# EXCLUDES: checks changed after a pass that keep the old pass, a claim
#   or tries carried into the new checks, the old revision kept (a late
#   verdict of an old check would land on a new one)
law verify_assign_resets:
  for +n: Nat
  for rev: Nat
  for slots: List<&2, V.Slot>
  for claimed: Bool
  for tries: Nat
  for few: {Nat.is_le(n, 64n) == True{} : Bool}
  {S.admitted(V.act(V.Owner{}, V.Assign{n}, V.Acc{rev, slots, claimed, tries})) == True{} : Bool} &
  {List.length(&2, V.Slot, S.slots(S.after(V.act(V.Owner{}, V.Assign{n}, V.Acc{rev, slots, claimed, tries})))) == n : Nat} &
  {S.opens(S.slots(S.after(V.act(V.Owner{}, V.Assign{n}, V.Acc{rev, slots, claimed, tries})))) == n : Nat} &
  {S.rev(S.after(V.act(V.Owner{}, V.Assign{n}, V.Acc{rev, slots, claimed, tries}))) == 1n+rev : Nat} &
  {S.claimed(S.after(V.act(V.Owner{}, V.Assign{n}, V.Acc{rev, slots, claimed, tries}))) == False{} : Bool} &
  {S.tries(S.after(V.act(V.Owner{}, V.Assign{n}, V.Acc{rev, slots, claimed, tries}))) == 0n : Nat}

# LAW verify_claim_keeps_verdicts (R3): a Claim of anyone is admitted and
# only makes the claim wait: the revision, every slot and the tries stay
# EXCLUDES: a claim that marks a check passed, clears a failure or resets
#   the tries
law verify_claim_keeps_verdicts:
  for who: V.Actor
  for rev: Nat
  for slots: List<&2, V.Slot>
  for claimed: Bool
  for tries: Nat
  {V.act(who, V.Claim{}, V.Acc{rev, slots, claimed, tries}) == (True{}, V.Acc{rev, slots, True{}, tries}) : Bool & V.Acc}

# LAW verify_record_needs_verifier (R3): a Record of anyone but the
# verifier is refused and changes nothing
# EXCLUDES: a worker that marks its own claim verified, an owner that
#   writes a verdict by hand
law verify_record_needs_verifier:
  for who: V.Actor
  for of: Nat
  for i: Nat
  for v: V.Verdict
  for at: Nat
  for +a: V.Acc
  for other: {S.is_verifier(who) == False{} : Bool}
  {V.act(who, V.Record{of, i, v, at}, a) == (False{}, a) : Bool & V.Acc}

# LAW verify_record_old_revision_refused (R3): the verifier's Record for
# another revision than the current one is refused and changes nothing
# EXCLUDES: the verdict of a check the owner replaced meanwhile landing
#   on the new check at the same index
law verify_record_old_revision_refused:
  for +of: Nat
  for i: Nat
  for v: V.Verdict
  for at: Nat
  for +rev: Nat
  for slots: List<&2, V.Slot>
  for claimed: Bool
  for tries: Nat
  for old: {Nat.is_eq(of, rev) == False{} : Bool}
  {V.act(V.Verifier{}, V.Record{of, i, v, at}, V.Acc{rev, slots, claimed, tries}) == (False{}, V.Acc{rev, slots, claimed, tries}) : Bool & V.Acc}

# LAW verify_record_missing_refused (R3): the verifier's Record for an
# index with no check is refused and changes nothing
# EXCLUDES: a verdict appended as a new check, a verdict written on the
#   last check instead
law verify_record_missing_refused:
  for +i: Nat
  for v: V.Verdict
  for at: Nat
  for +rev: Nat
  for +slots: List<&2, V.Slot>
  for claimed: Bool
  for tries: Nat
  for none: {S.nth(i, slots) == None{} : Maybe<&2, V.Slot>}
  {V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries}) == (False{}, V.Acc{rev, slots, claimed, tries}) : Bool & V.Acc}

# LAW verify_record_writes_one (R3): the verifier's Record for a check
# of the current revision that exists is admitted; afterwards the slot at
# every index j is the recorded verdict with its state when j is the
# check's index, and the slot that was there otherwise; the revision, the
# claim and the tries stay
# EXCLUDES: a verdict written on another check, every check stamped at
#   once, a slot added or lost, the state of the verdict dropped or
#   replaced
law verify_record_writes_one:
  for +i: Nat
  for v: V.Verdict
  for at: Nat
  for +rev: Nat
  for +slots: List<&2, V.Slot>
  for claimed: Bool
  for tries: Nat
  for +j: Nat
  for has: {Nat.is_lt(i, List.length(&2, V.Slot, slots)) == True{} : Bool}
  {S.admitted(V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries})) == True{} : Bool} &
  {S.nth(j, S.slots(S.after(V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries})))) == S.pick(Nat.is_eq(j, i), V.Judged{v, at}, S.nth(j, slots)) : Maybe<&2, V.Slot>} &
  {S.rev(S.after(V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries}))) == rev : Nat} &
  {S.claimed(S.after(V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries}))) == claimed : Bool} &
  {S.tries(S.after(V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries}))) == tries : Nat}

# LAW verify_worker_changes_no_verdict (R3): after any act of the worker
# every slot and the revision are what they were
# EXCLUDES: any path by which the worker's own act confirms, clears or
#   replaces a check
law verify_worker_changes_no_verdict:
  for op: V.Op
  for +a: V.Acc
  {S.slots(S.after(V.act(V.Worker{}, op, a))) == S.slots(a) : List<&2, V.Slot>} &
  {S.rev(S.after(V.act(V.Worker{}, op, a))) == S.rev(a) : Nat}

# Laws: the verifier's step (R4)
# ------------------------------

# LAW verify_advance_rests_unclaimed (R4): without a claim the verifier
# rests and changes nothing
# EXCLUDES: a verdict or an end with no claim to judge
law verify_advance_rests_unclaimed:
  for conf: Bool
  for now: Nat
  for cap: Nat
  for rev: Nat
  for slots: List<&2, V.Slot>
  for tries: Nat
  {V.advance(conf, now, cap, V.Acc{rev, slots, False{}, tries}) == (V.Rest{}, V.Acc{rev, slots, False{}, tries}) : V.Action & V.Acc}

# LAW verify_advance_runs_first_due (R4): with a claim, while a check did
# not judge the state now, the verifier runs the first such check (the
# spec's lead, S4) and changes nothing
# EXCLUDES: a claim settled before every check judged the final state, a
#   check skipped, a check that judged the final state run again while
#   another is due before it
law verify_advance_runs_first_due:
  for conf: Bool
  for +now: Nat
  for cap: Nat
  for rev: Nat
  for +slots: List<&2, V.Slot>
  for tries: Nat
  for left: {Nat.is_lt(S.lead(now, slots), List.length(&2, V.Slot, slots)) == True{} : Bool}
  {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == (V.Run{S.lead(now, slots)}, V.Acc{rev, slots, True{}, tries}) : V.Action & V.Acc}

# LAW verify_success_needs_every_check (R4): whenever the verifier's step
# ends a claim verified or passed, the spec's label of the slots on the
# state now, programs run confined or not, is that label: there is a
# check, every check is confirmed on that state, and verified only when
# programs run confined
# EXCLUDES: success reported on a stale, refuted, broken, unjudged or
#   missing check, on no checks, or because the tries ran out; a claim
#   ended verified while programs run unconfined
law verify_success_needs_every_check:
  for +conf: Bool
  for +now: Nat
  for cap: Nat
  for +a: V.Acc
  for +l: V.Label
  for ok: {sp_succeeds(l) == True{} : Bool}
  for said: {S.action(V.advance(conf, now, cap, a)) == V.End{l} : V.Action}
  {S.label(conf, now, S.slots(a)) == l : V.Label}

# LAW verify_advance_verified_ends (R4): a claim whose label on the state
# now is verified or passed ends with that label: the claim and the tries
# are cleared
# EXCLUDES: a verified or passed claim sent back to the worker or left
#   waiting, a passed claim ended verified
law verify_advance_verified_ends:
  for +conf: Bool
  for +now: Nat
  for cap: Nat
  for rev: Nat
  for +slots: List<&2, V.Slot>
  for tries: Nat
  for +l: V.Label
  for ok: {sp_succeeds(l) == True{} : Bool}
  for all: {S.label(conf, now, slots) == l : V.Label}
  {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == (V.End{l}, V.Acc{rev, slots, False{}, 0n}) : V.Action & V.Acc}

# LAW verify_advance_refuted_returns (R4): a claim whose every check
# judged the state now and whose label is failed goes back to the worker
# while fewer than cap did in a row: the claim is cleared and the tries
# grow by one
# EXCLUDES: a refuted claim that ends at once though tries remain, a
#   return that does not count
law verify_advance_refuted_returns:
  for conf: Bool
  for +now: Nat
  for +cap: Nat
  for rev: Nat
  for +slots: List<&2, V.Slot>
  for +tries: Nat
  for done: {S.lead(now, slots) == List.length(&2, V.Slot, slots) : Nat}
  for bad: {S.label(conf, now, slots) == V.Failed{} : V.Label}
  for room: {Nat.is_lt(tries, cap) == True{} : Bool}
  {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == (V.Return{}, V.Acc{rev, slots, False{}, 1n+tries}) : V.Action & V.Acc}

# LAW verify_advance_refuted_ends_at_cap (R4): a claim whose every check
# judged the state now and whose label is failed ends failed once cap
# returns in a row were made: the claim and the tries are cleared
# EXCLUDES: a worker sent back for ever, a refuted claim that ends as
#   anything but failed
law verify_advance_refuted_ends_at_cap:
  for conf: Bool
  for +now: Nat
  for +cap: Nat
  for rev: Nat
  for +slots: List<&2, V.Slot>
  for +tries: Nat
  for done: {S.lead(now, slots) == List.length(&2, V.Slot, slots) : Nat}
  for bad: {S.label(conf, now, slots) == V.Failed{} : V.Label}
  for full: {Nat.is_lt(tries, cap) == False{} : Bool}
  {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == (V.End{V.Failed{}}, V.Acc{rev, slots, False{}, 0n}) : V.Action & V.Acc}

# LAW verify_advance_broken_returns (R4): a claim with at least one check
# (s, then t), whose every check judged the state now and whose label is
# unverified (a check broken or unjudged on that state, none refuted),
# goes back to the worker with the evidence while fewer than cap did in a
# row: the revision stays; the slot at every index j is opened when its
# verdict on the state now is neither a confirmation nor a refutation
# (spec/verified/verify.bend S4), else it stays; the claim is cleared and
# the tries grow by one, the same tries a refuted claim counts
# EXCLUDES: a timed-out command or a judge that is down ending the task
#   at once though tries remain, a broken check read as done, a broken
#   verdict kept so the next claim on the same state never asks again, a
#   confirmation or a refutation dropped, a return that does not count, a
#   count of its own that lets refuted and broken returns alternate for
#   ever
law verify_advance_broken_returns:
  for +conf: Bool
  for +now: Nat
  for +cap: Nat
  for +rev: Nat
  for +s: V.Slot
  for +t: List<&2, V.Slot>
  for +tries: Nat
  for j: Nat
  for done: {S.lead(now, s <> t) == List.length(&2, V.Slot, s <> t) : Nat}
  for un: {S.label(conf, now, s <> t) == V.Unverified{} : V.Label}
  for room: {Nat.is_lt(tries, cap) == True{} : Bool}
  {S.action(V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries})) == V.Return{} : V.Action} &
  {S.rev(S.stepped(V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries}))) == rev : Nat} &
  {S.nth(j, S.slots(S.stepped(V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries})))) == S.rerun(now, S.nth(j, s <> t)) : Maybe<&2, V.Slot>} &
  {S.claimed(S.stepped(V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries}))) == False{} : Bool} &
  {S.tries(S.stepped(V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries}))) == 1n+tries : Nat}

# LAW verify_advance_broken_ends_at_cap (R4): a claim with at least one
# check, whose every check judged the state now and whose label is
# unverified, ends unverified once cap returns in a row were made: the
# claim and the tries are cleared
# EXCLUDES: a worker sent back for ever for a check that stays broken, a
#   broken claim that ends failed, verified or passed at the cap
law verify_advance_broken_ends_at_cap:
  for conf: Bool
  for +now: Nat
  for +cap: Nat
  for rev: Nat
  for +s: V.Slot
  for +t: List<&2, V.Slot>
  for +tries: Nat
  for done: {S.lead(now, s <> t) == List.length(&2, V.Slot, s <> t) : Nat}
  for un: {S.label(conf, now, s <> t) == V.Unverified{} : V.Label}
  for full: {Nat.is_lt(tries, cap) == False{} : Bool}
  {V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries}) == (V.End{V.Unverified{}}, V.Acc{rev, s <> t, False{}, 0n}) : V.Action & V.Acc}

# LAW verify_advance_no_checks_ends (R4): a claim of a task with no checks
# ends unverified at once, whatever the state, the cap and the tries: the
# claim and the tries are cleared
# EXCLUDES: a task with no checks sent back to the worker (nothing it
#   does can confirm it), a claim with no checks left waiting, verified or
#   passed
law verify_advance_no_checks_ends:
  for conf: Bool
  for now: Nat
  for cap: Nat
  for rev: Nat
  for tries: Nat
  {V.advance(conf, now, cap, V.Acc{rev, Nil{}, True{}, tries}) == (V.End{V.Unverified{}}, V.Acc{rev, Nil{}, False{}, 0n}) : V.Action & V.Acc}

# LAW verify_advance_keeps_verdicts (R4): the verifier's step writes no
# verdict and keeps the revision, on every acceptance: the slot at every
# index j after the step is the slot there before, or that check opened
# again (spec/verified/verify.bend S5: putting an opened slot back gives
# the slot before); a verdict comes only from a Record, so a restart that
# repeats the step invents none
# EXCLUDES: a step that stamps a check it did not run, a restart that
#   turns a waiting claim into a pass, a step that adds or drops a check
law verify_advance_keeps_verdicts:
  for +conf: Bool
  for +now: Nat
  for cap: Nat
  for +a: V.Acc
  for +j: Nat
  {S.undo_open(S.nth(j, S.slots(S.stepped(V.advance(conf, now, cap, a)))), S.nth(j, S.slots(a))) == S.nth(j, S.slots(a)) : Maybe<&2, V.Slot>} &
  {S.rev(S.stepped(V.advance(conf, now, cap, a))) == S.rev(a) : Nat}

# LAW verify_advance_example (R4): anchor (examples, not the requirement):
# one claim on the state 7 with a cap of 3 returns, programs run
# unconfined unless named: a check left to run; every check confirmed
# (passed, and verified when programs run confined); one refuted with a
# try left; one refuted at the cap; one broken with a try left (it opens
# the broken check again); one unjudged at the cap; no checks. They
# witness the premises of the laws above
# EXCLUDES: laws of R4 that no acceptance meets
law verify_advance_example:
  {V.advance(False{}, 7n, 3n, V.Acc{1n, [V.Judged{V.Confirmed{}, 7n}, V.Open{}], True{}, 0n}) == (V.Run{1n}, V.Acc{1n, [V.Judged{V.Confirmed{}, 7n}, V.Open{}], True{}, 0n}) : V.Action & V.Acc} &
  {V.advance(False{}, 7n, 3n, V.Acc{1n, [V.Judged{V.Confirmed{}, 7n}, V.Judged{V.Confirmed{}, 7n}], True{}, 2n}) == (V.End{V.Passed{}}, V.Acc{1n, [V.Judged{V.Confirmed{}, 7n}, V.Judged{V.Confirmed{}, 7n}], False{}, 0n}) : V.Action & V.Acc} &
  {V.advance(True{}, 7n, 3n, V.Acc{1n, [V.Judged{V.Confirmed{}, 7n}, V.Judged{V.Confirmed{}, 7n}], True{}, 2n}) == (V.End{V.Verified{}}, V.Acc{1n, [V.Judged{V.Confirmed{}, 7n}, V.Judged{V.Confirmed{}, 7n}], False{}, 0n}) : V.Action & V.Acc} &
  {V.advance(False{}, 7n, 3n, V.Acc{1n, [V.Judged{V.Confirmed{}, 7n}, V.Judged{V.Refuted{}, 7n}], True{}, 2n}) == (V.Return{}, V.Acc{1n, [V.Judged{V.Confirmed{}, 7n}, V.Judged{V.Refuted{}, 7n}], False{}, 3n}) : V.Action & V.Acc} &
  {V.advance(False{}, 7n, 3n, V.Acc{1n, [V.Judged{V.Confirmed{}, 7n}, V.Judged{V.Refuted{}, 7n}], True{}, 3n}) == (V.End{V.Failed{}}, V.Acc{1n, [V.Judged{V.Confirmed{}, 7n}, V.Judged{V.Refuted{}, 7n}], False{}, 0n}) : V.Action & V.Acc} &
  {V.advance(False{}, 7n, 3n, V.Acc{1n, [V.Judged{V.Confirmed{}, 7n}, V.Judged{V.Broken{}, 7n}], True{}, 1n}) == (V.Return{}, V.Acc{1n, [V.Judged{V.Confirmed{}, 7n}, V.Open{}], False{}, 2n}) : V.Action & V.Acc} &
  {V.advance(False{}, 7n, 3n, V.Acc{1n, [V.Judged{V.Unjudged{}, 7n}, V.Judged{V.Confirmed{}, 7n}], True{}, 3n}) == (V.End{V.Unverified{}}, V.Acc{1n, [V.Judged{V.Unjudged{}, 7n}, V.Judged{V.Confirmed{}, 7n}], False{}, 0n}) : V.Action & V.Acc} &
  {V.advance(False{}, 7n, 3n, V.Acc{1n, [], True{}, 2n}) == (V.End{V.Unverified{}}, V.Acc{1n, [], False{}, 0n}) : V.Action & V.Acc}

# Laws: the exit code (R5)
# ------------------------

# LAW verify_exit_is_spec (R5): the exit code of every run is the spec's
# (spec/verified/verify.bend S3)
# EXCLUDES: a run with a failed, stale or broken check that exits 0
law verify_exit_is_spec:
  for +base: Nat
  for +now: Nat
  for +slots: List<&2, V.Slot>
  {V.exit(base, now, slots) == S.exit(base, now, slots) : Nat}

# LAW verify_exit_zero_needs_every_check (R5): one check that is not a
# confirmation taken on the state now, anywhere among the checks, makes
# the exit code nonzero whatever the run's own code
# EXCLUDES: a script that reads exit 0 as done while a check failed, was
#   skipped or passed only on an earlier state
law verify_exit_zero_needs_every_check:
  for base: Nat
  for +now: Nat
  for +pre: List<&2, V.Slot>
  for +s: V.Slot
  for post: List<&2, V.Slot>
  for un: {S.confirms(now, s) == False{} : Bool}
  {Nat.is_eq(V.exit(base, now, sp_around(pre, s, post)), 0n) == False{} : Bool}

# LAW verify_exit_keeps_code_when_confirmed (R5): with every check
# confirmed on the state now (n of them, also none) the run keeps its own
# exit code
# EXCLUDES: a run with no acceptance checks that starts to exit nonzero,
#   a verified run whose failure code is lost
law verify_exit_keeps_code_when_confirmed:
  for base: Nat
  for +now: Nat
  for +n: Nat
  {V.exit(base, now, sp_all_pass(n, now)) == base : Nat}

# Laws: whether a final answer is a claim (R7)
# ---------------------------------------------

# LAW verify_claims_held_never (R7): while queued input or running work
# owns the next boundary, a final answer is no claim, whatever else holds
# EXCLUDES: a verdict on a state a running job or a subagent still
#   changes, checks run while the user's next input waits
law verify_claims_held_never:
  for checked: Bool
  for goal: Bool
  for claimed: Bool
  for ended: Bool
  {V.claims(True{}, checked, goal, claimed, ended) == False{} : Bool}

# LAW verify_claims_waiting_claim_judged (R7): with nothing holding it, a
# claim that already waits is judged at the final answer, whatever else
# holds
# EXCLUDES: a goal's `goal.complete()` claim that is never judged, a claim
#   dropped because the goal is active or the last claim ended here
law verify_claims_waiting_claim_judged:
  for checked: Bool
  for goal: Bool
  for ended: Bool
  {V.claims(False{}, checked, goal, True{}, ended) == True{} : Bool}

# LAW verify_claims_unchecked_never (R7): a final answer of a task with no
# check and no waiting claim is no claim
# EXCLUDES: a verdict row at every answer of a session with no acceptance
#   checks
law verify_claims_unchecked_never:
  for goal: Bool
  for ended: Bool
  {V.claims(False{}, False{}, goal, False{}, ended) == False{} : Bool}

# LAW verify_claims_goal_claims_itself (R7): under an active goal a final
# answer with no waiting claim is no claim
# EXCLUDES: the checks run at every step of a goal, a goal sent back
#   before it said it was done
law verify_claims_goal_claims_itself:
  for checked: Bool
  for ended: Bool
  {V.claims(False{}, checked, True{}, False{}, ended) == False{} : Bool}

# LAW verify_claims_ended_state_stands (R7): a final answer on the state
# the last claim ended on, with no waiting claim, is no new claim
# EXCLUDES: a failed task sent back to the worker again and again by
#   answers that change nothing
law verify_claims_ended_state_stands:
  for checked: Bool
  for goal: Bool
  {V.claims(False{}, checked, goal, False{}, True{}) == False{} : Bool}

# LAW verify_claims_answer_is_claim (R7): with checks, nothing holding it,
# no active goal and a state no claim ended on, a final answer is a claim
# EXCLUDES: a verifier that never judges, a session with checks whose
#   runs end unjudged
law verify_claims_answer_is_claim:
  {V.claims(False{}, True{}, False{}, False{}, False{}) == True{} : Bool}

# Laws: the entry (R6)
# --------------------

# LAW verify_entry_answers (R6): the entry answers every request Rust
# spells, every number within the wire, with the model's decision spelled
# as Rust reads it
# EXCLUDES: a field misread or swapped (now and cap, the revision and the
#   index, a verdict and a state), a tag of another actor, act, verdict,
#   evidence or answer, a reply spelled otherwise, a default
law verify_entry_answers:
  for +q: FV.Req
  for fit: {SW.fit_req(q) == True{} : Bool}
  {FV.ffi(SW.w_req(q, "")) == SW.w_reply(q) : String}

# LAW verify_entry_reads (R6): the laws' reader reads every spelled
# request that fits the wire back whole, so verify_entry_malformed_exact
# refuses only what Rust never writes
# EXCLUDES: a reader (and so an entry) that refuses a request Rust writes
law verify_entry_reads:
  for +q: FV.Req
  for fit: {SW.fit_req(q) == True{} : Bool}
  {SW.read(SW.w_req(q, "")) == Some{q} : Maybe<&2, FV.Req>}

# LAW verify_entry_read_answers (R6): every input the laws' reader reads
# as exactly one request is answered with the model's decision on that
# request, spelled as Rust reads it; with verify_entry_malformed_exact
# this fixes the entry's answer to every input
# EXCLUDES: an input the entry reads otherwise than the wire's grammar (a
#   field skipped or read into another, a tag of another request), a
#   reply other than the model's decision, an answer that depends on more
#   than the request read
law verify_entry_read_answers:
  for +s: String
  for +q: FV.Req
  for got: {SW.read(s) == Some{q} : Maybe<&2, FV.Req>}
  {FV.ffi(s) == SW.w_reply(q) : String}

# LAW verify_entry_malformed_exact (R6): every input that is not exactly
# one request (an unknown tag, a malformed field, input left over) gets
# exactly the error form 'E ', then "verify: malformed request"
# EXCLUDES: a decision made on input that is no request, another error
#   text, a default
law verify_entry_malformed_exact:
  for +s: String
  for no: {SW.read(s) == None{} : Maybe<&2, FV.Req>}
  {FV.ffi(s) == Wr.err("verify: malformed request") : String}

# LAW verify_entry_leftover_refused (R6): a request Rust spells (every
# number within the wire), followed by any input (a character c, then r),
# gets exactly the error form 'E ', then "verify: malformed request":
# the entry reads nothing after the request
# EXCLUDES: an entry that answers a request and ignores what follows it,
#   a decision made on a request glued to other input
law verify_entry_leftover_refused:
  for +q: FV.Req
  for c: Char
  for r: String
  for fit: {SW.fit_req(q) == True{} : Bool}
  {FV.ffi(SW.w_req(q, SCon{c, r})) == Wr.err("verify: malformed request") : String}

# LAW verify_entry_unknown_tag_refused (R6): a request tag past the known
# ones (8 or more, within the wire), spelled as Rust spells a number and
# followed by any input, gets exactly the error form
# EXCLUDES: an unknown request read as a known one, a default answer, an
#   error text of another form
law verify_entry_unknown_tag_refused:
  for +n: Nat
  for +s: String
  for fit: {LawsBase.wire_fits(8n+n) == True{} : Bool}
  {FV.ffi(Wr.put_nat(8n+n, s)) == Wr.err("verify: malformed request") : String}

# LAW verify_entry_example (R1-R6): anchor: the strings Rust sends and the
# replies it reads: the owner's and the worker's Assign, a claim, a
# record, the verifier's steps (run, end passed, return, end failed at
# the cap, end unverified with no checks), a stale label, a passed label,
# the exit codes, the verdicts of evidence, whether an answer is a claim;
# an unknown tag and input left over
# EXCLUDES: another spelling of a request or a reply
law verify_entry_example:
  {[FV.ffi("0,0,0,2,0,0,F0,"), FV.ffi("0,1,0,2,0,0,F0,"), FV.ffi("0,1,1,1,2,0,0,F0,"), FV.ffi("0,2,2,1,0,0,7,1,2,0,0,T0,"), FV.ffi("1,7,3,1,2,1,0,7,0,T0,"), FV.ffi("1,7,3,1,2,1,0,7,1,0,7,T0,"), FV.ffi("1,7,3,1,2,1,0,7,1,1,7,T0,"), FV.ffi("1,7,1,1,2,1,0,7,1,1,7,T1,"), FV.ffi("1,7,3,1,0,T2,"), FV.ffi("2,7,2,1,0,7,1,0,6,"), FV.ffi("2,7,1,1,0,7,"), FV.ffi("3,0,7,1,1,0,7,"), FV.ffi("3,0,7,1,1,0,6,"), FV.ffi("3,0,7,0,"), FV.ffi("4,0,T0,0,"), FV.ffi("4,0,T0,101,"), FV.ffi("4,0,F0,0,"), FV.ffi("4,0,T2,"), FV.ffi("4,0,T4,"), FV.ffi("5,0,1,"), FV.ffi("5,0,2,"), FV.ffi("6,0,"), FV.ffi("6,3,"), FV.ffi("7,FTFFF"), FV.ffi("7,FTTFF"), FV.ffi("7,FTTTF"), FV.ffi("7,TTFTF"), FV.ffi("8,"), FV.ffi("6,0,x")] == ["T1,2,0,0,F0,", "F0,0,F0,", "T1,2,0,0,T0,", "T1,2,1,0,7,0,T0,", "1,1,1,2,1,0,7,0,T0,", "3,3,1,2,1,0,7,1,0,7,F0,", "2,1,2,1,0,7,1,1,7,F1,", "3,1,1,2,1,0,7,1,1,7,F0,", "3,2,1,0,F0,", "2,", "3,", "0,", "1,", "0,", "0,", "1,", "1,", "2,", "3,", "1,", "2,", "0,", "2,", "T", "F", "T", "F", Wr.err("verify: malformed request"), Wr.err("verify: malformed request")] : List<&2, String>}
