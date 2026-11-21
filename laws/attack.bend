# eukhe: the laws of area attack

import Base
import ../bend/verify.bend as V
import ../bend/strength.bend as St
import ../bend/attack.bend as At
import ../spec/verified/strength.bend as S
import ../bend/ffi_attack.bend as FA
import ../bend/wire.bend as Wr
import ../spec/verified/attack.bend as SA
import ../spec/verified/attack_wire.bend as SAW
import ./base.bend as LawsBase

# (S8) Blind attackers: their survivors count like breaks
# ---------------------------------------------------------------------
# spec/README.md S8, S8.1, S8.2. bend/attack.bend: after the breaks of
# bend/strength.bend were measured, fresh attackers that never saw the
# worker's transcript each write wrong code for the task with a witness
# (a command and the output the task requires). Every input is free
# unless a law names a premise.
#
# A1 (S8): an attack survives exactly when it ran, its wrong code passed
#     every gauged check, its witness shows the code wrong, and the judge
#     agrees; unrun when it did not run or the judge gave no verdict on
#     wrong code that passed; clean otherwise.
# A2 (S8.1): done is never certified while an attack survived.
# A3 (S8.2): attacks never certify done past a weak or unshown check;
#     with no attacks, done is certified exactly as bend/strength.bend
#     says; a task with no strong check is certified only with two or
#     more clean attacks; an unrun attack changes nothing.
# A4: certified, the label and the exit code are the rules
#     spec/verified/attack.bend restates (B2-B4) on every input.
# A5: the entry (bend/ffi_attack.bend) answers each request Rust writes
#     with the model's decision; every input it does not answer with the
#     error form is such a request read whole, and every error it answers
#     is exactly "attack: malformed request".
# The rest of S8 is Rust (crates/eukhe-core/src/durable/acceptance):
# - the attacks shown and dropped: tests.rs
#   a_blind_attack_that_survives_ends_not_certified (a survivor ends not
#   certified, exit 3; a change of the checks drops the attacks),
#   a_judge_only_task_with_two_clean_attacks_is_certified,
#   an_attack_that_could_not_run_certifies_nothing; command.rs
#   the_status_lists_the_blind_attacks (`/accept` lists them, an attack
#   of an earlier state shown stale); e2e
#   a_blind_attack_whose_lookup_table_passes_the_tests_ends_not_certified
#   (crates/eukhe-cli/tests/mutation_gate_e2e.rs).
# - the attacker's reply: strength/attack.rs
#   an_attack_reads_from_the_first_json_object_of_the_reply.
# - the scratch copies (never the user's workspace): strength/scratch.rs
#   a_scratch_copy_holds_the_sources_and_the_dependencies_and_goes_away;
#   the runs count against the run's limits through the session's
#   BudgetGate, and at most MAX_ATTACKS (2) attackers run per claim
#   (strength/attack.rs).

# Spec helpers
# ------------

# the judge agreed (a verdict, and yes)
def ap_agreed(m: Maybe<&2, Bool>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{yes}:
      yes

# the judge gave no verdict
def ap_silent(m: Maybe<&2, Bool>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{yes}:
      False{}

# the judge rejected (a verdict, and no)
def ap_rejected(m: Maybe<&2, Bool>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{yes}:
      Bool.not(yes)

# the outcome is unrun
def ap_is_unrun(o: At.Outcome) -> Bool:
  match o:
    case At.Survived{}:
      False{}
    case At.Clean{}:
      False{}
    case At.Unrun{}:
      True{}

# the outcome is clean
def ap_is_clean(o: At.Outcome) -> Bool:
  match o:
    case At.Survived{}:
      False{}
    case At.Clean{}:
      True{}
    case At.Unrun{}:
      False{}

# no outcome is a survivor
def ap_none_survived(os: List<&2, At.Outcome>) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Con{o, t}:
      match o:
        case At.Survived{}:
          False{}
        case At.Clean{}:
          ap_none_survived(t)
        case At.Unrun{}:
          ap_none_survived(t)

# how many outcomes are clean
def ap_clean_count(os: List<&2, At.Outcome>) -> Nat:
  match os:
    case Nil{}:
      0n
    case Con{o, t}:
      match o:
        case At.Survived{}:
          ap_clean_count(t)
        case At.Clean{}:
          1n+ap_clean_count(t)
        case At.Unrun{}:
          ap_clean_count(t)

# Laws: the outcome of one attack (A1)
# ------------------------------------

# LAW attack_survives_iff (A1): an attack survives exactly when it ran,
# its code passed the checks, the witness shows it wrong and the judge
# agrees
# EXCLUDES: an attack that failed a check counted as a survivor; a
#   witness whose output matches the required one counted; a survivor
#   the judge rejected counted
law attack_survives_iff:
  for +ran: Bool
  for +passes: Bool
  for +differs: Bool
  for +agrees: Maybe<&2, Bool>
  {At.is_survived(At.outcome(At.Run{ran, passes, differs, agrees})) == Bool.and(ran, Bool.and(passes, Bool.and(differs, ap_agreed(agrees)))) : Bool}

# LAW attack_unrun_iff (A1): an attack is unrun exactly when it did not
# run, or its wrong code passed the checks, its witness shows it wrong
# and the judge gave no verdict
# EXCLUDES: an attack cut off by the budget read as clean or as a
#   survivor; a judge's missing verdict read as either; an attack the
#   checks caught, or whose witness shows nothing, read as unrun
law attack_unrun_iff:
  for +ran: Bool
  for +passes: Bool
  for +differs: Bool
  for +agrees: Maybe<&2, Bool>
  {ap_is_unrun(At.outcome(At.Run{ran, passes, differs, agrees})) == Bool.or(Bool.not(ran), Bool.and(passes, Bool.and(differs, ap_silent(agrees)))) : Bool}

# LAW attack_clean_iff (A1): an attack is clean exactly when it ran and
# its wrong code failed a check, or its witness does not show it wrong,
# or the judge rejected the required output
# EXCLUDES: an attack that did not run counted clean; a survivor counted
#   clean; the checks catching the wrong code, a witness that matches,
#   or a judge's no not counted clean
law attack_clean_iff:
  for +ran: Bool
  for +passes: Bool
  for +differs: Bool
  for +agrees: Maybe<&2, Bool>
  {ap_is_clean(At.outcome(At.Run{ran, passes, differs, agrees})) == Bool.and(ran, Bool.or(Bool.not(passes), Bool.or(Bool.not(differs), ap_rejected(agrees)))) : Bool}

# Laws: certified (A2, A3)
# ------------------------

# LAW attack_survivor_blocks (A2): a surviving attack anywhere among the
# outcomes keeps done from being certified
# EXCLUDES: a lookup table that passes the checks and misses a held-out
#   input certified because other attacks ran clean
law attack_survivor_blocks:
  for now: Nat
  for gs: List<&2, St.Gauge>
  for +pre: List<&2, At.Outcome>
  for post: List<&2, At.Outcome>
  {At.certified(now, gs, List.append(&2, At.Outcome, pre, At.Survived{} <> post)) == False{} : Bool}

# LAW attack_never_certifies_past_a_blocking_check (A3): a weak or
# unshown check keeps done from being certified whatever the attacks
# EXCLUDES: clean attacks lifting a weak check to done
law attack_never_certifies_past_a_blocking_check:
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  for +os: List<&2, At.Outcome>
  for blocked: {St.clear(now, gs) == False{} : Bool}
  {At.certified(now, gs, os) == False{} : Bool}

# LAW attack_none_is_strength (A3): with no attack, done is certified
# exactly as bend/strength.bend says (layer 1 is the floor)
# EXCLUDES: layer 2 turning off certification when no attacker ran; a
#   judge-only task certified with no attack at all
law attack_none_is_strength:
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  {At.certified(now, gs, Nil{}) == St.certified(now, gs) : Bool}

# LAW attack_unrun_changes_nothing (A3): an unrun attack added anywhere
# changes nothing
# EXCLUDES: a budget cut-off read as a pass or as a survivor
law attack_unrun_changes_nothing:
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  for +pre: List<&2, At.Outcome>
  for +post: List<&2, At.Outcome>
  {At.certified(now, gs, List.append(&2, At.Outcome, pre, At.Unrun{} <> post)) == At.certified(now, gs, List.append(&2, At.Outcome, pre, post)) : Bool}

# LAW attack_judge_only_counts_clean (A3, A1): with no strong check and
# none weak or unshown, done is certified exactly when no outcome is a
# survivor and two or more outcomes are clean, each outcome counted by
# what it is
# EXCLUDES: an unrun attack, or a survivor, counted among the two clean
#   ones; [Unrun, Unrun] or [Clean, Unrun] certifying a judge-only task;
#   a clean attack counted twice; a survivor after two clean attacks
#   overlooked
law attack_judge_only_counts_clean:
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  for +os: List<&2, At.Outcome>
  for none: {S.strongs(now, gs) == 0n : Nat}
  for clear: {St.clear(now, gs) == True{} : Bool}
  {At.certified(now, gs, os) == Bool.and(ap_none_survived(os), Nat.is_le(2n, ap_clean_count(os))) : Bool}

# Laws: the label and the exit (A2, A3)
# -------------------------------------

# LAW attack_label_none_is_strength (A3): with no attack the label is
# bend/strength.bend's
# EXCLUDES: layer 2 relabelling a result no attacker touched
law attack_label_none_is_strength:
  for +l: V.Label
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  {At.label(l, now, gs, Nil{}) == St.label(l, now, gs) : St.Label}

# LAW attack_label_survivor_uncertified (A2): a result whose checks all
# passed is not certified while an attack survived
# EXCLUDES: a survivor shown in the report while the label says done
law attack_label_survivor_uncertified:
  for +l: V.Label
  for now: Nat
  for gs: List<&2, St.Gauge>
  for +pre: List<&2, At.Outcome>
  for post: List<&2, At.Outcome>
  for passing: {St.passes(l) == True{} : Bool}
  {At.label(l, now, gs, List.append(&2, At.Outcome, pre, At.Survived{} <> post)) == St.Uncertified{} : St.Label}

# LAW attack_exit_none_is_strength (A3): with no attack the exit code is
# bend/strength.bend's
# EXCLUDES: a headless run whose attackers never ran exiting otherwise
law attack_exit_none_is_strength:
  for +base: Nat
  for +now: Nat
  for +slots: List<&2, V.Slot>
  for +gs: List<&2, St.Gauge>
  {At.exit(base, now, slots, gs, Nil{}) == St.exit(base, now, slots, gs) : Nat}

# LAW attack_exit_survivor_never_zero (A2): a headless run with one or
# more checks and an attack that survived never exits 0
# EXCLUDES: a lookup table that passes the checks and misses a held-out
#   input exiting 0
law attack_exit_survivor_never_zero:
  for +base: Nat
  for +now: Nat
  for +slots: List<&2, V.Slot>
  for gs: List<&2, St.Gauge>
  for +pre: List<&2, At.Outcome>
  for post: List<&2, At.Outcome>
  for checked: {V.some(slots) == True{} : Bool}
  {Nat.is_eq(At.exit(base, now, slots, gs, List.append(&2, At.Outcome, pre, At.Survived{} <> post)), 0n) == False{} : Bool}

# Laws: the model is the spec (A4)
# --------------------------------

# LAW attack_certified_is_spec (A4, A2, A3): done is certified with every
# set of outcomes exactly as the spec says (B2)
# EXCLUDES: one clean attack lifting a judge-only task; a clean attack
#   counted twice; an unrun attack counted clean
law attack_certified_is_spec:
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  for +os: List<&2, At.Outcome>
  {At.certified(now, gs, os) == SA.certified(now, gs, os) : Bool}

# LAW attack_label_is_spec (A4, A2): the label of every result is the
# spec's (B3)
# EXCLUDES: a failed or unverified result relabelled by the attacks; a
#   passed one kept while an attack survived
law attack_label_is_spec:
  for +l: V.Label
  for +now: Nat
  for +gs: List<&2, St.Gauge>
  for +os: List<&2, At.Outcome>
  {At.label(l, now, gs, os) == SA.label(l, now, gs, os) : St.Label}

# LAW attack_exit_is_spec (A4, A2): the exit code of every headless run is
# the spec's (B4)
# EXCLUDES: a run whose checks passed with a surviving attack exiting 0;
#   a failed run's own code replaced
law attack_exit_is_spec:
  for +base: Nat
  for +now: Nat
  for +slots: List<&2, V.Slot>
  for +gs: List<&2, St.Gauge>
  for +os: List<&2, At.Outcome>
  {At.exit(base, now, slots, gs, os) == SA.exit(base, now, slots, gs, os) : Nat}

# LAW attack_example (A1-A4): anchor: wrong code that passed, shown wrong
# by its witness and agreed by the judge survives; the judge rejecting it
# or giving no verdict makes it clean or unrun; failing a check or a
# witness that matches is clean; an attack that did not run is unrun. A
# passed claim with a strong check stays passed with no attack and is not
# certified with a survivor; a judge-only task needs two clean attacks
# (an unrun one between them changes nothing), never past a weak check;
# a failed claim stays failed. A run whose checks passed exits 3 with a
# survivor, 0 without; with no checks it exits 0; a refuted check exits
# 1; a run's own code 2 is kept
# EXCLUDES: another decision for these facts
law attack_example:
  {[At.outcome(At.Run{True{}, True{}, True{}, Some{True{}}}), At.outcome(At.Run{True{}, True{}, True{}, Some{False{}}}), At.outcome(At.Run{True{}, True{}, True{}, None{}}), At.outcome(At.Run{True{}, False{}, True{}, Some{True{}}}), At.outcome(At.Run{True{}, True{}, False{}, Some{True{}}}), At.outcome(At.Run{False{}, True{}, True{}, Some{True{}}})] == [At.Survived{}, At.Clean{}, At.Unrun{}, At.Clean{}, At.Clean{}, At.Unrun{}] : List<&2, At.Outcome>} &
  {[At.label(V.Passed{}, 7n, [St.Gauge{St.Needs{80n}, St.Measured{23n, 24n, 24n, 7n}}], []), At.label(V.Passed{}, 7n, [St.Gauge{St.Needs{80n}, St.Measured{23n, 24n, 24n, 7n}}], [At.Clean{}, At.Survived{}]), At.label(V.Passed{}, 7n, [St.Gauge{St.Exempt{}, St.Unmeasured{}}], [At.Clean{}]), At.label(V.Passed{}, 7n, [St.Gauge{St.Exempt{}, St.Unmeasured{}}], [At.Clean{}, At.Unrun{}, At.Clean{}]), At.label(V.Passed{}, 7n, [St.Gauge{St.Needs{80n}, St.Measured{0n, 12n, 12n, 7n}}], [At.Clean{}, At.Clean{}]), At.label(V.Verified{}, 7n, [St.Gauge{St.Waived{}, St.Unmeasured{}}], [At.Clean{}, At.Clean{}, At.Survived{}]), At.label(V.Failed{}, 7n, [St.Gauge{St.Needs{80n}, St.Measured{23n, 24n, 24n, 7n}}], [At.Clean{}, At.Clean{}])] == [St.Passed{}, St.Uncertified{}, St.Uncertified{}, St.Passed{}, St.Uncertified{}, St.Uncertified{}, St.Failed{}] : List<&2, St.Label>} &
  {[At.exit(0n, 7n, [V.Judged{V.Confirmed{}, 7n}], [St.Gauge{St.Needs{80n}, St.Measured{23n, 24n, 24n, 7n}}], [At.Survived{}]), At.exit(0n, 7n, [V.Judged{V.Confirmed{}, 7n}], [St.Gauge{St.Needs{80n}, St.Measured{23n, 24n, 24n, 7n}}], [At.Clean{}]), At.exit(0n, 7n, [], [], [At.Survived{}]), At.exit(0n, 7n, [V.Judged{V.Refuted{}, 7n}], [St.Gauge{St.Needs{80n}, St.Measured{23n, 24n, 24n, 7n}}], []), At.exit(2n, 7n, [V.Judged{V.Confirmed{}, 7n}], [St.Gauge{St.Needs{80n}, St.Measured{23n, 24n, 24n, 7n}}], [At.Survived{}]), At.exit(0n, 7n, [V.Judged{V.Confirmed{}, 7n}], [St.Gauge{St.Exempt{}, St.Unmeasured{}}], [At.Clean{}, At.Clean{}])] == [3n, 0n, 0n, 1n, 2n, 0n] : List<&2, Nat>}

# Laws: the entry (A5)
# --------------------

# LAW attack_entry_answers (A5): the entry answers every request Rust
# spells (every number within the wire) with the model's decision spelled
# as Rust reads it
# EXCLUDES: a field misread, an outcome or label tag of another one, a
#   default
law attack_entry_answers:
  for +q: FA.Req
  for fit: {SAW.fit_req(q) == True{} : Bool}
  {FA.ffi(SAW.w_req(q, "")) == SAW.w_reply(q) : String}

# LAW attack_entry_reads (A5): the laws' reader reads every spelled request
# that fits the wire back whole
# EXCLUDES: a reader that refuses everything
law attack_entry_reads:
  for +q: FA.Req
  for fit: {SAW.fit_req(q) == True{} : Bool}
  {SAW.read(SAW.w_req(q, "")) == Some{q} : Maybe<&2, FA.Req>}

# LAW attack_entry_exact (A5): every input the entry does not answer with
# the error form is a spelled request that fits the wire
# EXCLUDES: a decision answered on input that is no request (an unknown
#   tag, outcome, bar, mark, verdict or label read as a known one, a
#   list cut short, a missing field, a number past the wire, input left
#   over)
law attack_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FA.ffi(s)) == False{} : Bool}
  exs q: FA.Req
  {s == SAW.w_req(q, "") : String} & {SAW.fit_req(q) == True{} : Bool}

# LAW attack_entry_refuses (A5): for every input whose answer opens with
# 'E' (an error), the answer is exactly `E attack: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law attack_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FA.ffi(s)) == True{} : Bool}
  {FA.ffi(s) == Wr.err("attack: malformed request") : String}

# LAW attack_entry_leftover_refused (A5): a request Rust spells followed
# by any input answers exactly the error form
# EXCLUDES: the input after the request ignored or read into a field
law attack_entry_leftover_refused:
  for +q: FA.Req
  for c: Char
  for r: String
  for fit: {SAW.fit_req(q) == True{} : Bool}
  {FA.ffi(SAW.w_req(q, SCon{c, r})) == Wr.err("attack: malformed request") : String}

# LAW attack_entry_example (A5): anchor: the strings Rust sends and the
# replies it reads: an attack that survives, one the judge gave no
# verdict, one that failed a check, one that did not run; the label of a
# passed claim with a strong check and a survivor, and without; a
# judge-only claim with two clean attacks, and with one; the exit of a
# run whose checks passed with a survivor, and without; an unknown tag; a
# malformed Bool; an unknown outcome; input left over
# EXCLUDES: another spelling of a request or a reply
law attack_entry_example:
  {[FA.ffi("0,TTT1,T"), FA.ffi("0,TTT0,"), FA.ffi("0,TFT1,T"), FA.ffi("0,FTT1,T"), FA.ffi("1,3,7,1,2,80,1,23,24,24,7,1,0,"), FA.ffi("1,3,7,1,2,80,1,23,24,24,7,0,"), FA.ffi("1,3,7,1,0,0,2,1,1,"), FA.ffi("1,3,7,1,0,0,1,1,"), FA.ffi("2,0,7,1,1,0,7,1,2,80,1,23,24,24,7,1,0,"), FA.ffi("2,0,7,1,1,0,7,1,2,80,1,23,24,24,7,0,"), FA.ffi("3,"), FA.ffi("0,TTX0,"), FA.ffi("1,3,7,0,1,3,"), FA.ffi("0,TTT0,x")] == ["0,", "2,", "1,", "2,", "4,", "3,", "3,", "4,", "3,", "0,", Wr.err("attack: malformed request"), Wr.err("attack: malformed request"), Wr.err("attack: malformed request"), Wr.err("attack: malformed request")] : List<&2, String>}
