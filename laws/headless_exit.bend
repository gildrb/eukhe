# eukhe: the laws of area headless_exit

import Base
import ../bend/headless_exit.bend as Hx
import ../bend/ffi_headless_exit.bend as FHx
import ../bend/wire.bend as Wr
import ../spec/durable/headless.bend as Sp
import ../spec/durable/headless_wire.bend as SpW

# (D5) A headless run exits nonzero unless it answered
# ----------------------------------------------------
# bend/headless_exit.bend, run as the compiled core by
# bend/ffi_headless_exit.bend (eukhe-bend rules/headless.rs `exit`; asked
# by eukhe-cli when `eukhe -p` or `--mode json` ends, for the process exit
# code). spec/durable/headless.bend restates the rule (E1-E2),
# spec/durable/headless_wire.bend the wire (W3-W5). Every input is free:
# any facts, any string.
#
# R1: the exit of every facts is the spec's (E1-E2).
# R2: the code is 0 exactly when the run answered, and 1 otherwise.
# R3: every failure fact makes the code nonzero, whatever the other
#     facts: a failed command, a give-up, each failing reason of an
#     unanswered run, a provider error, an aborted, unfinished or failed
#     slash entry, a failed compaction, a failed autonomous turn.
# R4: the cause is the first failure in the order of E1.
# R5: a run that answered, was reset, went stale or was withdrawn is no
#     failure by itself: the exit is that of no run.
# R6: the entry answers each request Rust writes (W3) with the spelling
#     (W4) of the spec's exit, and any input that is not exactly one
#     request with exactly `E headless_exit: malformed request`.

# the code of an exit
def code_of(v: Hx.Verdict) -> Nat:
  match v:
    case Hx.Verdict{n, c}:
      n

# the cause of an exit
def cause_of(v: Hx.Verdict) -> Hx.Cause:
  match v:
    case Hx.Verdict{n, c}:
      c

# Laws: the exit (R1-R2)
# ----------------------

# LAW headless_exit_refines_spec (R1): the exit of every facts is the
# spec's
# EXCLUDES: a failure fact left out, causes checked in another order, a
#   reset, stale or withdrawn run read as a failure, a code that does not
#   follow the cause
law headless_exit_refines_spec:
  for +f: Hx.Facts
  {Hx.decide(f) == Sp.exit_spec(f) : Hx.Verdict}

# LAW headless_exit_zero_iff_answered (R2): the code is 0 exactly when the
# run answered
# EXCLUDES: a failed run that exits 0 (a script reads it as done), an
#   answered run that exits nonzero
law headless_exit_zero_iff_answered:
  for +f: Hx.Facts
  {Nat.is_eq(code_of(Hx.decide(f)), 0n) == Sp.answered(cause_of(Hx.decide(f))) : Bool}

# LAW headless_exit_code_at_most_one (R2): the code is 0 or 1
# EXCLUDES: a code past 1 (a signal number, a code a shell reads as
#   another failure)
law headless_exit_code_at_most_one:
  for +f: Hx.Facts
  {Nat.is_le(code_of(Hx.decide(f)), 1n) == True{} : Bool}

# Laws: every failure fails (R3)
# ------------------------------

# LAW headless_exit_command_failed_fails (R3): a failed session command
# exits nonzero
# EXCLUDES: a `/command` prompt that failed read as an answer
law headless_exit_command_failed_fails:
  for g: Bool
  for r: Hx.Run
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{True{}, g, r, p, c, a})) == 1n : Nat}

# LAW headless_exit_gave_up_fails (R3): a wait that gave up at its limit
# exits nonzero
# EXCLUDES: a run that stopped with work still pending read as done
law headless_exit_gave_up_fails:
  for cf: Bool
  for r: Hx.Run
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{cf, True{}, r, p, c, a})) == 1n : Nat}

# LAW headless_exit_model_error_fails (R3): a run that settled on a model
# error exits nonzero
# EXCLUDES: a provider failure hidden behind an earlier answer
law headless_exit_model_error_fails:
  for cf: Bool
  for gu: Bool
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{cf, gu, Hx.Unanswered{Hx.ModelError{}}, p, c, a})) == 1n : Nat}

# LAW headless_exit_run_limit_fails (R3): a run stopped by the run limit
# exits nonzero
# EXCLUDES: a run cut off by its limit read as done
law headless_exit_run_limit_fails:
  for cf: Bool
  for gu: Bool
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{cf, gu, Hx.Unanswered{Hx.RunLimit{}}, p, c, a})) == 1n : Nat}

# LAW headless_exit_no_model_fails (R3): a run with no model exits nonzero
# EXCLUDES: a run that never asked a model read as done
law headless_exit_no_model_fails:
  for cf: Bool
  for gu: Bool
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{cf, gu, Hx.Unanswered{Hx.NoModel{}}, p, c, a})) == 1n : Nat}

# LAW headless_exit_forced_tool_fails (R3): a run that ended on a forced
# tool exits nonzero
# EXCLUDES: a forced tool call that never got its answer read as done
law headless_exit_forced_tool_fails:
  for cf: Bool
  for gu: Bool
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{cf, gu, Hx.Unanswered{Hx.ForcedTool{}}, p, c, a})) == 1n : Nat}

# LAW headless_exit_faulted_fails (R3): a faulted run exits nonzero
# EXCLUDES: a crashed run read as done
law headless_exit_faulted_fails:
  for cf: Bool
  for gu: Bool
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{cf, gu, Hx.Unanswered{Hx.Faulted{}}, p, c, a})) == 1n : Nat}

# LAW headless_exit_run_aborted_fails (R3): an aborted run exits nonzero
# EXCLUDES: an interrupted run read as done
law headless_exit_run_aborted_fails:
  for cf: Bool
  for gu: Bool
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{cf, gu, Hx.Unanswered{Hx.Aborted{}}, p, c, a})) == 1n : Nat}

# LAW headless_exit_other_reason_fails (R3): a run unanswered for a reason
# the rule does not name exits nonzero
# EXCLUDES: a new failure reason that silently exits 0
law headless_exit_other_reason_fails:
  for cf: Bool
  for gu: Bool
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{cf, gu, Hx.Unanswered{Hx.Other{}}, p, c, a})) == 1n : Nat}

# LAW headless_exit_provider_error_fails (R3): a provider error as the
# terminal entry exits nonzero
# EXCLUDES: an error reply printed and exited 0
law headless_exit_provider_error_fails:
  for cf: Bool
  for gu: Bool
  for r: Hx.Run
  for c: Bool
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{cf, gu, r, Hx.PProviderError{}, c, a})) == 1n : Nat}

# LAW headless_exit_aborted_fails (R3): an aborted reply as the terminal
# entry exits nonzero
# EXCLUDES: a cut-off reply read as an answer
law headless_exit_aborted_fails:
  for cf: Bool
  for gu: Bool
  for r: Hx.Run
  for c: Bool
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{cf, gu, r, Hx.PAborted{}, c, a})) == 1n : Nat}

# LAW headless_exit_unfinished_fails (R3): an unfinished reply (a tool use,
# a pending or deferred turn) as the terminal entry exits nonzero
# EXCLUDES: a run that stopped mid-turn read as done
law headless_exit_unfinished_fails:
  for cf: Bool
  for gu: Bool
  for r: Hx.Run
  for c: Bool
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{cf, gu, r, Hx.PUnfinished{}, c, a})) == 1n : Nat}

# LAW headless_exit_slash_failed_fails (R3): a failed slash command as the
# terminal entry exits nonzero
# EXCLUDES: a slash command error read as success
law headless_exit_slash_failed_fails:
  for cf: Bool
  for gu: Bool
  for r: Hx.Run
  for c: Bool
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{cf, gu, r, Hx.PSlashFailed{}, c, a})) == 1n : Nat}

# LAW headless_exit_compaction_failed_fails (R3): a failed compaction exits
# nonzero
# EXCLUDES: a compaction failure hidden behind an answer
law headless_exit_compaction_failed_fails:
  for cf: Bool
  for gu: Bool
  for r: Hx.Run
  for p: Hx.Primary
  for a: Bool
  {code_of(Hx.decide(Hx.Facts{cf, gu, r, p, True{}, a})) == 1n : Nat}

# LAW headless_exit_autonomous_failed_fails (R3): a failed autonomous turn
# exits nonzero
# EXCLUDES: a failed follow-up turn hidden behind the first answer
law headless_exit_autonomous_failed_fails:
  for cf: Bool
  for gu: Bool
  for r: Hx.Run
  for p: Hx.Primary
  for c: Bool
  {code_of(Hx.decide(Hx.Facts{cf, gu, r, p, c, True{}})) == 1n : Nat}

# Laws: precedence (R4)
# ---------------------

# LAW headless_exit_command_failed_first (R4): a failed command is the
# cause, whatever else holds
# EXCLUDES: a later cause reported for a failed command
law headless_exit_command_failed_first:
  for g: Bool
  for r: Hx.Run
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  {cause_of(Hx.decide(Hx.Facts{True{}, g, r, p, c, a})) == Hx.CCommandFailed{} : Hx.Cause}

# LAW headless_exit_gave_up_before_run (R4): without a failed command, a
# give-up is the cause, whatever the run and the transcript
# EXCLUDES: a run's state reported for a run the wait abandoned
law headless_exit_gave_up_before_run:
  for r: Hx.Run
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  {cause_of(Hx.decide(Hx.Facts{False{}, True{}, r, p, c, a})) == Hx.CGaveUp{} : Hx.Cause}

# LAW headless_exit_run_before_transcript (R4): without a failed command or
# a give-up, a run that failed is the cause, with its reason, whatever the
# transcript and the flags
# EXCLUDES: a run failure reported as the transcript entry it left, a
#   reason lost or swapped
law headless_exit_run_before_transcript:
  for +r: Hx.Reason
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  for fails: {Sp.run_fails(r) == True{} : Bool}
  {cause_of(Hx.decide(Hx.Facts{False{}, False{}, Hx.Unanswered{r}, p, c, a})) == Hx.CRunFailed{r} : Hx.Cause}

# LAW headless_exit_transcript_before_flags (R4): without an earlier
# failure, a failed terminal entry is the cause, whatever the flags
# EXCLUDES: a compaction or autonomous failure reported over the entry
#   that failed
law headless_exit_transcript_before_flags:
  for +r: Hx.Run
  for +p: Hx.Primary
  for c: Bool
  for a: Bool
  for +x: Hx.Cause
  for ok: {Sp.run_cause(r) == None{} : Maybe<&2, Hx.Cause>}
  for failed: {Sp.primary_cause(p) == Some{x} : Maybe<&2, Hx.Cause>}
  {cause_of(Hx.decide(Hx.Facts{False{}, False{}, r, p, c, a})) == x : Hx.Cause}

# LAW headless_exit_compaction_before_autonomous (R4): without an earlier
# failure, a failed compaction is the cause, whatever the autonomous turn
# EXCLUDES: the two flags checked the other way round
law headless_exit_compaction_before_autonomous:
  for +r: Hx.Run
  for +p: Hx.Primary
  for a: Bool
  for ok: {Sp.run_cause(r) == None{} : Maybe<&2, Hx.Cause>}
  for clean: {Sp.primary_cause(p) == None{} : Maybe<&2, Hx.Cause>}
  {cause_of(Hx.decide(Hx.Facts{False{}, False{}, r, p, True{}, a})) == Hx.CCompactionFailed{} : Hx.Cause}

# Laws: no failure by itself (R5)
# -------------------------------

# LAW headless_exit_unfailed_run_neutral (R5): a run that answered, was
# reset, went stale or was withdrawn exits as no run would
# EXCLUDES: a reset, stale or withdrawn run read as a failure (a
#   superseded run turning a good answer into exit 1), an answered run
#   that hides a later failure
law headless_exit_unfailed_run_neutral:
  for +cf: Bool
  for +gu: Bool
  for +p: Hx.Primary
  for +c: Bool
  for +a: Bool
  {[Hx.decide(Hx.Facts{cf, gu, Hx.Answered{}, p, c, a}), Hx.decide(Hx.Facts{cf, gu, Hx.Unanswered{Hx.Reset{}}, p, c, a}), Hx.decide(Hx.Facts{cf, gu, Hx.Unanswered{Hx.Stale{}}, p, c, a}), Hx.decide(Hx.Facts{cf, gu, Hx.Unanswered{Hx.Withdrawn{}}, p, c, a})] == [Hx.decide(Hx.Facts{cf, gu, Hx.NoRun{}, p, c, a}), Hx.decide(Hx.Facts{cf, gu, Hx.NoRun{}, p, c, a}), Hx.decide(Hx.Facts{cf, gu, Hx.NoRun{}, p, c, a}), Hx.decide(Hx.Facts{cf, gu, Hx.NoRun{}, p, c, a})] : List<&2, Hx.Verdict>}

# LAW headless_exit_example (R1-R5): anchor: an answered run exits 0; a
# slash command alone exits 0; a model error, a stale run left with a
# tool use, a give-up and a failed command exit 1 with their causes
# EXCLUDES: a spec that drifts from the exits Rust reports
law headless_exit_example:
  {[Hx.decide(Hx.Facts{False{}, False{}, Hx.Answered{}, Hx.PAnswer{}, False{}, False{}}), Hx.decide(Hx.Facts{False{}, False{}, Hx.NoRun{}, Hx.PSlashOk{}, False{}, False{}}), Hx.decide(Hx.Facts{False{}, False{}, Hx.Unanswered{Hx.ModelError{}}, Hx.PProviderError{}, False{}, False{}}), Hx.decide(Hx.Facts{False{}, False{}, Hx.Unanswered{Hx.Stale{}}, Hx.PUnfinished{}, False{}, False{}}), Hx.decide(Hx.Facts{False{}, True{}, Hx.Answered{}, Hx.PAnswer{}, False{}, False{}}), Hx.decide(Hx.Facts{True{}, False{}, Hx.NoRun{}, Hx.PNothing{}, False{}, False{}})] == [Hx.Verdict{0n, Hx.CAnswered{}}, Hx.Verdict{0n, Hx.CAnswered{}}, Hx.Verdict{1n, Hx.CRunFailed{Hx.ModelError{}}}, Hx.Verdict{1n, Hx.CUnfinished{}}, Hx.Verdict{1n, Hx.CGaveUp{}}, Hx.Verdict{1n, Hx.CCommandFailed{}}] : List<&2, Hx.Verdict>}

# Laws: the entry (R6)
# --------------------

# LAW headless_exit_entry_answers (R6): the entry answers every request
# Rust spells with the spelling of the spec's exit
# EXCLUDES: a field misread or swapped (two flags, a run and a primary
#   tag), a reason lost on the way back, a cause tag of another cause, a
#   default
law headless_exit_entry_answers:
  for +f: Hx.Facts
  {FHx.ffi(SpW.w_exit_req(f, "")) == SpW.w_exit_reply(f) : String}

# LAW headless_exit_entry_reads (R6): the laws' reader reads every spelled
# request back whole, so headless_exit_entry_malformed_exact refuses only
# what Rust never writes
# EXCLUDES: a reader (and so an entry) that refuses a request Rust writes
law headless_exit_entry_reads:
  for +f: Hx.Facts
  {SpW.read_exit(SpW.w_exit_req(f, "")) == Some{f} : Maybe<&2, Hx.Facts>}

# LAW headless_exit_entry_malformed_exact (R6): every input that is not
# exactly one request (an unknown tag, a malformed field, input left
# over) gets exactly the error form 'E ', then
# "headless_exit: malformed request"
# EXCLUDES: an exit answered for input that is no request, another error
#   text, a default
law headless_exit_entry_malformed_exact:
  for +s: String
  for no: {SpW.read_exit(s) == None{} : Maybe<&2, Hx.Facts>}
  {FHx.ffi(s) == Wr.err("headless_exit: malformed request") : String}

# LAW headless_exit_entry_example (R6): anchor: the strings Rust sends and
# the replies it reads: an answer, a model error, a stale run with an
# aborted entry, a failed compaction; an unknown reason, a short request,
# input left over
# EXCLUDES: another spelling of a request or a reply
law headless_exit_entry_example:
  {[FHx.ffi("FF1,1,FF"), FHx.ffi("FF2,0,1,FF"), FHx.ffi("FF2,7,4,FF"), FHx.ffi("FF0,0,TF"), FHx.ffi("FF2,10,1,FF"), FHx.ffi("FF1,1,F"), FHx.ffi("FF1,1,FFx")] == ["0,0,", "1,3,0,", "1,5,", "1,8,", Wr.err("headless_exit: malformed request"), Wr.err("headless_exit: malformed request"), Wr.err("headless_exit: malformed request")] : List<&2, String>}
