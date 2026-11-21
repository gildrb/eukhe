# eukhe: the laws of area strength

import Base
import ../bend/verify.bend as V
import ../bend/strength.bend as St
import ../bend/ffi_strength.bend as FS
import ../bend/headless_task.bend as Ht
import ../bend/wire.bend as Wr
import ../spec/verified/verify.bend as SV
import ../spec/verified/strength.bend as S
import ../spec/verified/strength_wire.bend as SW
import ./base.bend as LawsBase

# (S1-S6) A check certifies done only when it was shown to catch broken
# code
# ----------------------------------------------------------------------
# spec/README.md S1-S6. bend/strength.bend: before a claim whose checks
# all passed counts as done, the verifier breaks the code the task
# changed on purpose (mutants, in a scratch copy of the workspace), runs
# each gauged check on the broken copies and records a mark: the breaks
# caught, run and planned, and the state. The model runs as the compiled
# core by bend/ffi_strength.bend (eukhe-bend rules/strength.rs), asked by
# eukhe-core durable/acceptance after verify ended a claim and for the
# label, and by eukhe-cli print_runtime for the exit code.
# spec/verified/strength.bend restates the rules (K1-K7). Every input is
# free unless a law names a premise.
#
# R1 (S1): the strength of a check. A gauged check is strong on a state
#     exactly when its mark was taken on that state, every planned break
#     ran, one or more ran, and it caught at least its share of them;
#     weak when it caught less or nothing was there to break; unshown
#     with no whole mark on that state. A judge, the intent check and a
#     waived check (`--strength 0`: a share of 0) are free.
# R2 (S2): done is certified exactly when some check is strong and none
#     is weak or unshown: a trivial check (`true`, a test that asserts
#     nothing) catches no break and keeps done from being certified, and
#     checks that cannot be gauged certify nothing by themselves.
# R3 (S3): the label: a result whose checks all passed keeps its label
#     (verified; checks passed, unconfined) only when done is certified,
#     else it is not certified; failed and unverified stay.
# R4 (S4): the verifier's step after verify ended a claim: a passing claim
#     measures, first first, each gauged check without a mark on the state
#     now, then ends with the label of R3; a claim that did not pass ends
#     at once with its label, and no break runs for it. A claim ends done
#     only when done is certified.
# R5 (S5): only the verifier records a mark, only for a check that
#     exists, and it changes that check's mark only (its bar stays);
#     every other act changes nothing.
# R6 (S6): the exit code of a headless run: verify's, except that a run
#     whose checks (one or more) all passed on the final state while done
#     is not certified exits 3, the code of an unjudged answer
#     (bend/headless_task.bend), instead of 0; a nonzero own code is kept.
# R7: the entry answers each request Rust writes with the model's
#     decision; every input it does not answer with the error form is
#     such a request read whole, and every error it answers is exactly
#     "strength: malformed request".
# The rest of S3-S7 is Rust, tested there (crates/eukhe-core/src/durable
# unless named):
# - S3, the texts of the label, the `/accept` status and the verdict row
#   with each check's strength: acceptance/tests.rs
#   a_claim_whose_checks_pass_on_the_final_state_is_verified,
#   a_passing_check_that_catches_no_break_ends_not_certified.
# - S4, the breaks and the scratch copies: acceptance/strength/mod.rs
#   the_check_s_files_are_never_broken,
#   a_break_replaces_its_line_and_keeps_the_endings,
#   a_break_runs_at_most_the_check_s_limit; strength/mutants.rs
#   each_language_breaks_its_code_and_never_its_strings_or_comments,
#   a_sample_takes_one_break_of_each_line_in_turn; strength/scratch.rs
#   a_scratch_copy_holds_the_sources_and_the_dependencies_and_goes_away;
#   strength/changes.rs a_diff_gives_the_new_lines_of_each_changed_file,
#   the_task_s_lines_are_those_since_the_baseline_and_the_untracked_files.
# - S5, a write to a file a check protects refused: path_policy/tests.rs
#   a_write_to_a_file_a_check_protects_is_refused.
# - S6, the headless stderr and exit code end to end:
#   crates/eukhe-cli/tests/mutation_gate_e2e.rs
#   a_check_that_catches_nothing_is_weak_and_exits_three,
#   a_real_test_that_catches_the_breaks_certifies_done,
#   a_lookup_table_of_the_tested_inputs_never_ends_done.
# - S7, `/accept bend`: acceptance/command.rs
#   the_bend_check_runs_the_proofs_and_protects_every_law_and_the_lock;
#   mutation_gate_e2e.rs a_write_to_a_law_file_under_accept_bend_is_refused.

# helpers of the laws
# -------------------

# the checks pre, then g, then post
def sp_around(pre: List<&2, St.Gauge>, g: St.Gauge, post: List<&2, St.Gauge>) -> List<&2, St.Gauge>:
  List.append(&2, St.Gauge, pre, g <> post)

# Laws: the strength of one check (R1)
# ------------------------------------

# LAW strength_share_met_strong (R1): a whole measurement on the state
# now (every planned break ran) that ran one or more breaks and caught
# at least the owner's share of them (caught / ran >= pct / 100, the
# share 1 percent or more) is strong
# EXCLUDES: a check that catches 20 of 24 breaks under an 80 percent bar
#   reported weak; a share read the other way round (ran over caught); a
#   check that catches exactly its share read as short of it; a good
#   check never shown strong, so no claim is ever certified
law strength_share_met_strong:
  for +pct: Nat
  for +c: Nat
  for +n: Nat
  for +p: Nat
  for +now: Nat
  for whole: {Nat.is_le(p, n) == True{} : Bool}
  for ran: {Nat.is_eq(n, 0n) == False{} : Bool}
  for met: {Nat.is_le(Nat.mul(1n+pct, n), Nat.mul(100n, c)) == True{} : Bool}
  {St.strength(now, St.Gauge{St.Needs{1n+pct}, St.Measured{c, n, p, now}}) == St.Strong{} : St.Strength}

# LAW strength_nothing_to_break_weak (R1): a whole measurement on the
# state now that planned and ran no break (nothing there to break) is
# weak, whatever its share and its count
# EXCLUDES: a check on code with nothing to break counted strong because
#   0 of 0 meets any share; such a measurement read as never taken, so
#   the verifier measures it again forever
law strength_nothing_to_break_weak:
  for pct: Nat
  for c: Nat
  for +now: Nat
  {St.strength(now, St.Gauge{St.Needs{1n+pct}, St.Measured{c, 0n, 0n, now}}) == St.Weak{} : St.Strength}

# LAW strength_unmeasured_unshown (R1): a gauged check never measured
# shows nothing
# EXCLUDES: a check that only passed, never broken, counted strong or
#   free
law strength_unmeasured_unshown:
  for pct: Nat
  for now: Nat
  {St.strength(now, St.Gauge{St.Needs{1n+pct}, St.Unmeasured{}}) == St.Unshown{} : St.Strength}

# LAW strength_ungauged_free (R1): a judge or the intent check (no code
# to break) and a check whose owner waived its share (`--strength 0`,
# however it is spelled: waived, or a share of 0) are free on every
# state, whatever mark they carry
# EXCLUDES: a judge read as weak or unshown because no break ran for it;
#   a waived check keeping done from being certified; `true` under a
#   share of 0 (0 of 12 caught meets 0 percent) shown strong and
#   certifying done on its own; a stray mark on a judge read as strong
law strength_ungauged_free:
  for now: Nat
  for m: St.Mark
  {St.strength(now, St.Gauge{St.Exempt{}, m}) == St.Free{} : St.Strength} &
  {St.strength(now, St.Gauge{St.Waived{}, m}) == St.Free{} : St.Strength} &
  {St.strength(now, St.Gauge{St.Needs{0n}, m}) == St.Free{} : St.Strength}

# LAW strength_short_of_share_weak (R1): a whole measurement on the state
# now whose caught breaks are below the share of those run is weak
# EXCLUDES: a check that catches 3 of 24 breaks under an 80 percent bar
#   reported strong; `true`, or a test that asserts nothing (none of one
#   or more caught), reported strong; a rounding that lets a check just
#   under its share through
law strength_short_of_share_weak:
  for +pct: Nat
  for +c: Nat
  for +n: Nat
  for +p: Nat
  for +now: Nat
  for whole: {Nat.is_le(p, n) == True{} : Bool}
  for ran: {Nat.is_eq(n, 0n) == False{} : Bool}
  for short: {Nat.is_le(Nat.mul(1n+pct, n), Nat.mul(100n, c)) == False{} : Bool}
  {St.strength(now, St.Gauge{St.Needs{1n+pct}, St.Measured{c, n, p, now}}) == St.Weak{} : St.Strength}

# LAW strength_stale_mark_unshown (R1): a mark taken on another state
# shows nothing on the state now
# EXCLUDES: a check measured before the worker's last change counted as
#   strong for the code that changed since
law strength_stale_mark_unshown:
  for pct: Nat
  for c: Nat
  for n: Nat
  for p: Nat
  for +at: Nat
  for +now: Nat
  for other: {Nat.is_eq(at, now) == False{} : Bool}
  {St.strength(now, St.Gauge{St.Needs{1n+pct}, St.Measured{c, n, p, at}}) == St.Unshown{} : St.Strength}

# LAW strength_cut_short_unshown (R1): a measurement that ran fewer
# breaks than it planned (the budget or the time ran out) shows nothing
# EXCLUDES: one caught break of one run read as strong when 24 were
#   planned; a budget squeezed on purpose to certify a weak check
law strength_cut_short_unshown:
  for pct: Nat
  for c: Nat
  for +n: Nat
  for +p: Nat
  for +now: Nat
  for short: {Nat.is_lt(n, p) == True{} : Bool}
  {St.strength(now, St.Gauge{St.Needs{1n+pct}, St.Measured{c, n, p, now}}) == St.Unshown{} : St.Strength}

# Laws: certified (R2)
# --------------------

# LAW strength_certified_is_spec (R2): done is certified exactly as the
# spec says (K2)
# EXCLUDES: a majority of strong checks certifying past a weak one, no
#   check at all certifying
law strength_certified_is_spec:
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  {St.certified(now, gs) == S.certified(now, gs) : Bool}

# LAW strength_blocking_check_never_certifies (R2): a check that is weak
# or unshown on the state now, anywhere among the checks, keeps done
# from being certified
# EXCLUDES: a weak check hidden among strong ones; a check never measured
#   skipped
law strength_blocking_check_never_certifies:
  for +now: Nat
  for +pre: List<&2, St.Gauge>
  for +g: St.Gauge
  for post: List<&2, St.Gauge>
  for weak: {S.blocking(S.strength(now, g)) == True{} : Bool}
  {St.certified(now, sp_around(pre, g, post)) == False{} : Bool}

# LAW strength_certified_needs_strong (R2): with no check strong on the
# state now (only judges, the intent check, waived checks, or none) done
# is not certified
# EXCLUDES: a task with only judges, or only waived checks, certified;
#   no checks certified
law strength_certified_needs_strong:
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  for none: {S.strongs(now, gs) == 0n : Nat}
  {St.certified(now, gs) == False{} : Bool}

# Laws: the label (R3)
# --------------------

# LAW strength_label_is_spec (R3): the label of every result is the
# spec's (K3)
# EXCLUDES: a failed or unverified result relabelled; a passed one kept
#   while not certified
law strength_label_is_spec:
  for +l: V.Label
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  {St.label(l, now, gs) == S.label(l, now, gs) : St.Label}

# LAW strength_label_uncertified_iff (R3): the label is not certified
# exactly when every check passed (verify's label verified or passed) and
# done is not certified
# EXCLUDES: a failed claim shown as not certified (it failed); a weak
#   check shown as done
law strength_label_uncertified_iff:
  for +l: V.Label
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  {S.is_uncertified(St.label(l, now, gs)) == Bool.and(S.passing(l), Bool.not(S.certified(now, gs))) : Bool}

# LAW strength_label_done_needs_certified (R3): a label that says done
# (verified; checks passed, unconfined) needs done certified on the
# state now
# EXCLUDES: done claimed on checks that let the broken code pass
law strength_label_done_needs_certified:
  for +l: V.Label
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  for done: {S.is_done(St.label(l, now, gs)) == True{} : Bool}
  {S.certified(now, gs) == True{} : Bool}

# Laws: the verifier's step (R4)
# ------------------------------

# LAW strength_settle_is_spec (R4): the step after verify ended a claim
# is the spec's (K4)
# EXCLUDES: a check measured out of order, a measured check measured
#   again on the same state, an end before every gauged check was
#   measured
law strength_settle_is_spec:
  for +l: V.Label
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  {St.settle(l, now, gs) == S.settle(l, now, gs) : St.Step}

# LAW strength_settle_unpassed_runs_nothing (R4): a claim that did not
# pass ends at once with its label: no break runs for it
# EXCLUDES: breaks run (time and money spent) for a claim that failed
law strength_settle_unpassed_runs_nothing:
  for +l: V.Label
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  for no: {S.passing(l) == False{} : Bool}
  {St.settle(l, now, gs) == St.End{S.label(l, now, gs)} : St.Step}

# LAW strength_settle_ends_done_certified (R4): a step that ends a claim
# done (verified; checks passed, unconfined) has done certified on the
# state now
# EXCLUDES: a claim ended done while a gauged check is weak, unshown or
#   never measured
law strength_settle_ends_done_certified:
  for +l: V.Label
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  for done: {S.ends_done(St.settle(l, now, gs)) == True{} : Bool}
  {S.certified(now, gs) == True{} : Bool}

# Laws: who records a mark (R5)
# -----------------------------

# LAW strength_record_needs_verifier (R5): the owner and the worker never
# record a mark; the checks stay as they were
# EXCLUDES: the worker writing its own strength; the owner faking one
law strength_record_needs_verifier:
  for +who: V.Actor
  for i: Nat
  for m: St.Mark
  for +gs: List<&2, St.Gauge>
  for no: {S.is_verifier(who) == False{} : Bool}
  {St.record(who, i, m, gs) == (False{}, gs) : Bool & List<&2, St.Gauge>}

# LAW strength_record_missing_refused (R5): the verifier's record for an
# index with no check is refused and changes nothing
# EXCLUDES: a mark appended as a new check, a mark written on the last
#   check instead
law strength_record_missing_refused:
  for +i: Nat
  for m: St.Mark
  for +gs: List<&2, St.Gauge>
  for none: {S.nth(i, gs) == None{} : Maybe<&2, St.Gauge>}
  {St.record(V.Verifier{}, i, m, gs) == (False{}, gs) : Bool & List<&2, St.Gauge>}

# LAW strength_record_writes_one (R5): the verifier's record for a check
# that exists is admitted; after it, the check at every index j is that
# check with the recorded mark (its bar kept) when j is the index, and
# the check that was there otherwise
# EXCLUDES: a mark written on another check, every check marked at once,
#   a check added or lost, the owner's bar changed by a record
law strength_record_writes_one:
  for +i: Nat
  for +m: St.Mark
  for +gs: List<&2, St.Gauge>
  for +j: Nat
  for has: {Nat.is_lt(i, List.length(&2, St.Gauge, gs)) == True{} : Bool}
  {S.admitted(St.record(V.Verifier{}, i, m, gs)) == True{} : Bool} &
  {S.nth(j, S.after(St.record(V.Verifier{}, i, m, gs))) == S.remark_if(Nat.is_eq(j, i), m, S.nth(j, gs)) : Maybe<&2, St.Gauge>}

# Laws: the exit code (R6)
# ------------------------

# LAW strength_exit_is_spec (R6): the exit code of every headless run is
# the spec's (K6)
# EXCLUDES: a run whose checks passed without catching broken code
#   exiting 0
law strength_exit_is_spec:
  for +base: Nat
  for +now: Nat
  for +slots: List<&2, V.Slot>
  for +gs: List<&2, St.Gauge>
  {St.exit(base, now, slots, gs) == S.exit(base, now, slots, gs) : Nat}

# LAW strength_exit_uncertified_three (R6): a run of exit 0 whose checks
# (one or more) all passed on the final state while done is not
# certified exits 3, the code of an unjudged answer
# EXCLUDES: exit 0 (done) for checks that let the broken code pass; exit
#   1 (a failure) for a run whose checks passed
law strength_exit_uncertified_three:
  for +now: Nat
  for +slots: List<&2, V.Slot>
  for +gs: List<&2, St.Gauge>
  for all: {SV.all_confirmed(now, slots) == True{} : Bool}
  for some: {Nat.is_eq(List.length(&2, V.Slot, slots), 0n) == False{} : Bool}
  for un: {S.certified(now, gs) == False{} : Bool}
  {St.exit(0n, now, slots, gs) == Ht.unjudged_code() : Nat} &
  {Ht.unjudged_code() == 3n : Nat}

# LAW strength_exit_zero_needs_certified (R6): the code is 0 exactly when
# the run's own code is 0, every check passed on the final state, and
# there is no check or done is certified
# EXCLUDES: exit 0 for a weak check, a failed check, or a failed run;
#   exit nonzero for a run with no checks that exited 0
law strength_exit_zero_needs_certified:
  for +base: Nat
  for +now: Nat
  for +slots: List<&2, V.Slot>
  for +gs: List<&2, St.Gauge>
  {Nat.is_eq(St.exit(base, now, slots, gs), 0n) == Bool.and(Nat.is_eq(base, 0n), Bool.and(SV.all_confirmed(now, slots), Bool.or(Nat.is_eq(List.length(&2, V.Slot, slots), 0n), S.certified(now, gs)))) : Bool}

# LAW strength_exit_keeps_code (R6): a nonzero code of the run itself is
# kept whatever the checks
# EXCLUDES: a failed run turned into 3 or 0 by its checks
law strength_exit_keeps_code:
  for +p: Nat
  for +now: Nat
  for +slots: List<&2, V.Slot>
  for +gs: List<&2, St.Gauge>
  {St.exit(1n+p, now, slots, gs) == 1n+p : Nat}

# LAW strength_example (R1-R6): anchor: a check that caught 23 of 24
# breaks under the 80 percent bar is strong and certifies a passed claim;
# `true` catching 0 of 12 is weak and the claim is not certified (exit
# 3); a mark of state 6 is unshown on state 7; a measurement that ran 3
# of 24 is unshown; a passed claim with an unmeasured check measures it;
# a failed claim ends failed at once; a judge-only task is not certified;
# a waived check next to a strong one certifies; `true` catching 0 of 12
# under a share of 0 is free
# EXCLUDES: another decision for these facts
law strength_example:
  {[St.strength(7n, St.Gauge{St.Needs{80n}, St.Measured{23n, 24n, 24n, 7n}}), St.strength(7n, St.Gauge{St.Needs{80n}, St.Measured{0n, 12n, 12n, 7n}}), St.strength(7n, St.Gauge{St.Needs{80n}, St.Measured{24n, 24n, 24n, 6n}}), St.strength(7n, St.Gauge{St.Needs{80n}, St.Measured{3n, 3n, 24n, 7n}}), St.strength(7n, St.Gauge{St.Needs{80n}, St.Measured{0n, 0n, 0n, 7n}}), St.strength(7n, St.Gauge{St.Exempt{}, St.Unmeasured{}}), St.strength(7n, St.Gauge{St.Needs{0n}, St.Measured{0n, 12n, 12n, 7n}})] == [St.Strong{}, St.Weak{}, St.Unshown{}, St.Unshown{}, St.Weak{}, St.Free{}, St.Free{}] : List<&2, St.Strength>} &
  {[St.settle(V.Passed{}, 7n, [St.Gauge{St.Needs{80n}, St.Measured{23n, 24n, 24n, 7n}}, St.Gauge{St.Exempt{}, St.Unmeasured{}}]), St.settle(V.Passed{}, 7n, [St.Gauge{St.Needs{80n}, St.Measured{0n, 12n, 12n, 7n}}]), St.settle(V.Passed{}, 7n, [St.Gauge{St.Exempt{}, St.Unmeasured{}}, St.Gauge{St.Needs{80n}, St.Unmeasured{}}]), St.settle(V.Failed{}, 7n, [St.Gauge{St.Needs{80n}, St.Unmeasured{}}]), St.settle(V.Passed{}, 7n, [St.Gauge{St.Exempt{}, St.Unmeasured{}}]), St.settle(V.Passed{}, 7n, [St.Gauge{St.Waived{}, St.Unmeasured{}}, St.Gauge{St.Needs{80n}, St.Measured{20n, 24n, 24n, 7n}}])] == [St.End{St.Passed{}}, St.End{St.Uncertified{}}, St.Measure{1n}, St.End{St.Failed{}}, St.End{St.Uncertified{}}, St.End{St.Passed{}}] : List<&2, St.Step>} &
  {[St.exit(0n, 7n, [V.Judged{V.Confirmed{}, 7n}], [St.Gauge{St.Needs{80n}, St.Measured{0n, 12n, 12n, 7n}}]), St.exit(0n, 7n, [V.Judged{V.Confirmed{}, 7n}], [St.Gauge{St.Needs{80n}, St.Measured{23n, 24n, 24n, 7n}}]), St.exit(0n, 7n, [], []), St.exit(0n, 7n, [V.Judged{V.Refuted{}, 7n}], [St.Gauge{St.Needs{80n}, St.Unmeasured{}}]), St.exit(2n, 7n, [V.Judged{V.Confirmed{}, 7n}], [St.Gauge{St.Exempt{}, St.Unmeasured{}}])] == [3n, 0n, 0n, 1n, 2n] : List<&2, Nat>}

# Laws: the entry (R7)
# --------------------

# LAW strength_entry_answers (R7): the entry answers every request Rust
# spells (every number within the wire) with the model's decision
# spelled as Rust reads it
# EXCLUDES: a field misread, a label or step tag of another one, a
#   default
law strength_entry_answers:
  for +q: FS.Req
  for fit: {SW.fit_req(q) == True{} : Bool}
  {FS.ffi(SW.w_req(q, "")) == SW.w_reply(q) : String}

# LAW strength_entry_reads (R7): the laws' reader reads every spelled
# request that fits the wire back whole
# EXCLUDES: a reader that refuses everything
law strength_entry_reads:
  for +q: FS.Req
  for fit: {SW.fit_req(q) == True{} : Bool}
  {SW.read(SW.w_req(q, "")) == Some{q} : Maybe<&2, FS.Req>}

# LAW strength_entry_exact (R7): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: a decision answered on input that is no request (an unknown
#   tag, label, actor, bar, mark or verdict read as a known one, a list
#   cut short, a missing field, a number past the wire, input left over)
law strength_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FS.ffi(s)) == False{} : Bool}
  exs q: FS.Req
  {s == SW.w_req(q, "") : String} & {SW.fit_req(q) == True{} : Bool}

# LAW strength_entry_refuses (R7): for every input whose answer opens
# with 'E' (an error), the answer is exactly
# `E strength: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law strength_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FS.ffi(s)) == True{} : Bool}
  {FS.ffi(s) == Wr.err("strength: malformed request") : String}

# LAW strength_entry_leftover_refused (R7): a request Rust spells followed
# by any input answers exactly the error form
# EXCLUDES: the input after the request ignored or read into a field
law strength_entry_leftover_refused:
  for +q: FS.Req
  for c: Char
  for r: String
  for fit: {SW.fit_req(q) == True{} : Bool}
  {FS.ffi(SW.w_req(q, SCon{c, r})) == Wr.err("strength: malformed request") : String}

# LAW strength_entry_example (R7): anchor: the strings Rust sends and the
# replies it reads: a passed claim with a strong check ends passed; one
# with a weak check ends not certified; one with an unmeasured check
# measures it; the label of a passed claim with a weak check; the exit of
# such a run; the verifier's record and the worker's; the strength of a
# strong check; an unknown tag; input left over
# EXCLUDES: another spelling of a request or a reply
law strength_entry_example:
  {[FS.ffi("0,3,7,1,2,80,1,23,24,24,7,"), FS.ffi("0,3,7,1,2,80,1,0,12,12,7,"), FS.ffi("0,3,7,1,2,80,0,"), FS.ffi("1,3,7,1,2,80,1,0,12,12,7,"), FS.ffi("2,0,7,1,1,0,7,1,2,80,1,0,12,12,7,"), FS.ffi("3,2,0,1,23,24,24,7,1,2,80,0,"), FS.ffi("3,1,0,1,23,24,24,7,1,2,80,0,"), FS.ffi("4,7,2,80,1,23,24,24,7,"), FS.ffi("5,"), FS.ffi("4,7,0,0,x")] == ["1,3,", "1,4,", "0,0,", "4,", "3,", "T1,2,80,1,23,24,24,7,", "F1,2,80,0,", "0,", Wr.err("strength: malformed request"), Wr.err("strength: malformed request")] : List<&2, String>}
