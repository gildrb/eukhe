# eukhe: the laws of area headless_exit

import Base
import ../bend/headless_exit.bend as Hx
import ../bend/ffi_headless_exit.bend as FHx
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../spec/durable/headless.bend as Sp
import ../spec/durable/headless_wire.bend as SpW

# (D5) A headless run exits nonzero unless it answered or is budget-limited
# ------------------------------------------------------------------------
# bend/headless_exit.bend, run as the compiled core by
# bend/ffi_headless_exit.bend (eukhe-bend rules/headless.rs `exit`; asked
# by eukhe-cli when `eukhe -p` or `--mode json` ends, for the process exit
# code). spec/durable/headless.bend states the rule in words (E1-E2) and
# the failure of a run and of a terminal entry as tables (run_cause,
# primary_cause); spec/durable/headless_wire.bend the wire (W3-W5). Every
# input is free: any facts, any string.
#
# R1: the exit of every facts is the one E1-E2 state: R2-R5 fix its code
#     and its cause for every facts.
# R2: the code is 0 exactly when no failure fact holds (the run
#     answered), or the final answer from the budget's reserve was
#     delivered and no failure but those a used-up budget leaves holds
#     (the run is budget-limited), and 1 otherwise.
# R3: every failure fact makes the code nonzero, whatever the other
#     facts: a failed command, a give-up, each failing reason of an
#     unanswered run, a provider error, an aborted, unfinished or failed
#     slash entry, a failed compaction, a failed autonomous turn; and,
#     without the final answer from the reserve, the wait ended at the
#     time budget's deadline, a run or a terminal entry the budget
#     refused. The delivered final answer excuses only those three.
# R4: the cause is the first failure in the order of E1, and that the run
#     answered when no failure holds (budget-limited when the final answer
#     from the reserve was delivered).
# R5: a run that answered, was reset, went stale or was withdrawn is no
#     failure by itself: the exit is that of no run.
# R6: the entry answers each request Rust writes (W3) with the spelling
#     (W4) of the core's exit (bend/headless_exit.bend `decide`, fixed by
#     R1-R5), answers no input but exactly one request with anything but
#     the error form, and answers any input that is not exactly one
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

# a failure that does not hold
def holds_not(m: Maybe<&2, Hx.Cause>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

# a failure that does not hold, or one the delivered final answer from
# the budget's reserve excuses (Sp.excused)
def only_excused(m: Maybe<&2, Hx.Cause>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      Sp.excused(x)

# whether the final answer from the budget's reserve was delivered
def budget_answered(f: Hx.Facts) -> Bool:
  match f:
    case Hx.Facts{cf, w, run, p, c, a, ba}:
      ba

# E1 read over the facts: no failure holds: no failed command, a quiet
# wait (Sp.wait_cause), a run that did not fail (no run, answered, reset,
# stale, withdrawn: Sp.run_cause), a terminal entry that is no failure
# (nothing, an answer, a slash command that succeeded: Sp.primary_cause),
# no failed compaction, no failed autonomous turn
def no_failure(f: Hx.Facts) -> Bool:
  match f:
    case Hx.Facts{cf, w, run, p, c, a, ba}:
      Bool.and(Bool.not(cf), Bool.and(holds_not(Sp.wait_cause(w)), Bool.and(holds_not(Sp.run_cause(run)), Bool.and(holds_not(Sp.primary_cause(p)), Bool.and(Bool.not(c), Bool.not(a))))))

# E1 read over the facts: budget-limited: the final answer from the
# budget's reserve was delivered, and no failure holds but those it
# excuses (only_excused: the wait at the time budget's deadline, a run
# or a terminal entry the budget refused)
def budget_limited(f: Hx.Facts) -> Bool:
  match f:
    case Hx.Facts{cf, w, run, p, c, a, ba}:
      Bool.and(ba, Bool.and(Bool.not(cf), Bool.and(only_excused(Sp.wait_cause(w)), Bool.and(only_excused(Sp.run_cause(run)), Bool.and(only_excused(Sp.primary_cause(p)), Bool.and(Bool.not(c), Bool.not(a)))))))

# Laws: the exit (R1-R2)
# ----------------------

# LAW headless_exit_zero_iff_no_failure (R2): the code is 0 exactly when
# no failure fact holds (no_failure: no failed command, a quiet wait, a
# run that did not fail by the table Sp.run_cause, a terminal entry that
# is no failure by the table Sp.primary_cause, no failed compaction, no
# failed autonomous turn) or the run is budget-limited (budget_limited:
# the final answer from the reserve delivered, no failure but those it
# excuses)
# EXCLUDES: a failed run that exits 0 (a script reads it as done), a run
#   with no failure that exits nonzero, a failure fact the code ignores,
#   a budget-limited run that exits nonzero, a used-up budget without a
#   delivered final answer that exits 0
law headless_exit_zero_iff_no_failure:
  for +f: Hx.Facts
  {Nat.is_eq(code_of(Hx.decide(f)), 0n) == Bool.or(no_failure(f), budget_limited(f)) : Bool}

# LAW headless_exit_no_failure_answered (R1, R4): when no failure fact
# holds (no_failure) and no final answer from the budget's reserve was
# delivered, the cause is that the run answered
# EXCLUDES: a run with no failure reported with a failure cause (a cause
#   invented from a reset or a slash command that succeeded)
law headless_exit_no_failure_answered:
  for +f: Hx.Facts
  for clean: {no_failure(f) == True{} : Bool}
  for plain: {budget_answered(f) == False{} : Bool}
  {cause_of(Hx.decide(f)) == Hx.CAnswered{} : Hx.Cause}

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
  for w: Hx.Wait
  for r: Hx.Run
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  for ba: Bool
  {code_of(Hx.decide(Hx.Facts{True{}, w, r, p, c, a, ba})) == 1n : Nat}

# LAW headless_exit_gave_up_fails (R3): a wait that gave up at its limit
# exits nonzero
# EXCLUDES: a run that stopped with work still pending read as done
law headless_exit_gave_up_fails:
  for cf: Bool
  for r: Hx.Run
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  for ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, Hx.GaveUp{}, r, p, c, a, ba})) == 1n : Nat}

# LAW headless_exit_model_error_fails (R3): a run that settled on a model
# error exits nonzero
# EXCLUDES: a provider failure hidden behind an earlier answer
law headless_exit_model_error_fails:
  for cf: Bool
  for w: Hx.Wait
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  for ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.ModelError{}}, p, c, a, ba})) == 1n : Nat}

# LAW headless_exit_run_limit_fails (R3): a run stopped by the run limit
# exits nonzero
# EXCLUDES: a run cut off by its limit read as done
law headless_exit_run_limit_fails:
  for cf: Bool
  for w: Hx.Wait
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  for ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.RunLimit{}}, p, c, a, ba})) == 1n : Nat}

# LAW headless_exit_no_model_fails (R3): a run with no model exits nonzero
# EXCLUDES: a run that never asked a model read as done
law headless_exit_no_model_fails:
  for cf: Bool
  for w: Hx.Wait
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  for ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.NoModel{}}, p, c, a, ba})) == 1n : Nat}

# LAW headless_exit_forced_tool_fails (R3): a run that ended on a forced
# tool exits nonzero
# EXCLUDES: a forced tool call that never got its answer read as done
law headless_exit_forced_tool_fails:
  for cf: Bool
  for w: Hx.Wait
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  for ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.ForcedTool{}}, p, c, a, ba})) == 1n : Nat}

# LAW headless_exit_faulted_fails (R3): a faulted run exits nonzero
# EXCLUDES: a crashed run read as done
law headless_exit_faulted_fails:
  for cf: Bool
  for w: Hx.Wait
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  for ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.Faulted{}}, p, c, a, ba})) == 1n : Nat}

# LAW headless_exit_run_aborted_fails (R3): an aborted run exits nonzero
# EXCLUDES: an interrupted run read as done
law headless_exit_run_aborted_fails:
  for cf: Bool
  for w: Hx.Wait
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  for ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.Aborted{}}, p, c, a, ba})) == 1n : Nat}

# LAW headless_exit_other_reason_fails (R3): a run unanswered for a reason
# the rule does not name exits nonzero
# EXCLUDES: a new failure reason that silently exits 0
law headless_exit_other_reason_fails:
  for cf: Bool
  for w: Hx.Wait
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  for ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.Other{}}, p, c, a, ba})) == 1n : Nat}

# LAW headless_exit_provider_error_fails (R3): a provider error as the
# terminal entry exits nonzero
# EXCLUDES: an error reply printed and exited 0
law headless_exit_provider_error_fails:
  for cf: Bool
  for w: Hx.Wait
  for r: Hx.Run
  for c: Bool
  for a: Bool
  for +ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, w, r, Hx.PProviderError{}, c, a, ba})) == 1n : Nat}

# LAW headless_exit_aborted_fails (R3): an aborted reply as the terminal
# entry exits nonzero
# EXCLUDES: a cut-off reply read as an answer
law headless_exit_aborted_fails:
  for cf: Bool
  for w: Hx.Wait
  for r: Hx.Run
  for c: Bool
  for a: Bool
  for +ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, w, r, Hx.PAborted{}, c, a, ba})) == 1n : Nat}

# LAW headless_exit_unfinished_fails (R3): an unfinished reply (a tool use,
# a pending or deferred turn) as the terminal entry exits nonzero
# EXCLUDES: a run that stopped mid-turn read as done
law headless_exit_unfinished_fails:
  for cf: Bool
  for w: Hx.Wait
  for r: Hx.Run
  for c: Bool
  for a: Bool
  for +ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, w, r, Hx.PUnfinished{}, c, a, ba})) == 1n : Nat}

# LAW headless_exit_slash_failed_fails (R3): a failed slash command as the
# terminal entry exits nonzero
# EXCLUDES: a slash command error read as success
law headless_exit_slash_failed_fails:
  for cf: Bool
  for w: Hx.Wait
  for r: Hx.Run
  for c: Bool
  for a: Bool
  for +ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, w, r, Hx.PSlashFailed{}, c, a, ba})) == 1n : Nat}

# LAW headless_exit_compaction_failed_fails (R3): a failed compaction exits
# nonzero
# EXCLUDES: a compaction failure hidden behind an answer
law headless_exit_compaction_failed_fails:
  for cf: Bool
  for w: Hx.Wait
  for r: Hx.Run
  for p: Hx.Primary
  for a: Bool
  for +ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, w, r, p, True{}, a, ba})) == 1n : Nat}

# LAW headless_exit_autonomous_failed_fails (R3): a failed autonomous turn
# exits nonzero
# EXCLUDES: a failed follow-up turn hidden behind the first answer
law headless_exit_autonomous_failed_fails:
  for cf: Bool
  for w: Hx.Wait
  for r: Hx.Run
  for p: Hx.Primary
  for c: Bool
  for +ba: Bool
  {code_of(Hx.decide(Hx.Facts{cf, w, r, p, c, True{}, ba})) == 1n : Nat}

# Laws: precedence (R4)
# ---------------------

# LAW headless_exit_cause_is_first_failure (R1, R4): for every facts the
# cause is E1's (Sp.exit_cause): the first failure in E1's order (a
# failed command, the wait, the last run, the terminal entry, a failed
# compaction, a failed autonomous turn), where the wait at the time
# budget's deadline and a run or a terminal entry the budget refused
# fail only without the delivered final answer from the reserve; with
# none, budget-limited when that answer was delivered, else answered
# EXCLUDES: a provider error, an aborted, unfinished or failed slash
#   entry after the final answer reported as budget-unanswered; a later
#   failure reported over an earlier one; a failure reported as answered
#   or budget-limited
law headless_exit_cause_is_first_failure:
  for +f: Hx.Facts
  {cause_of(Hx.decide(f)) == Sp.exit_cause(f) : Hx.Cause}

# LAW headless_exit_command_failed_first (R4): a failed command is the
# cause, whatever else holds
# EXCLUDES: a later cause reported for a failed command
law headless_exit_command_failed_first:
  for w: Hx.Wait
  for r: Hx.Run
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  for ba: Bool
  {cause_of(Hx.decide(Hx.Facts{True{}, w, r, p, c, a, ba})) == Hx.CCommandFailed{} : Hx.Cause}

# LAW headless_exit_gave_up_before_run (R4): without a failed command, a
# give-up at the wait limit is the cause, whatever the run, the
# transcript and the final answer from the reserve
# EXCLUDES: a run's state reported for a run the wait abandoned
law headless_exit_gave_up_before_run:
  for r: Hx.Run
  for p: Hx.Primary
  for c: Bool
  for a: Bool
  for ba: Bool
  {cause_of(Hx.decide(Hx.Facts{False{}, Hx.GaveUp{}, r, p, c, a, ba})) == Hx.CGaveUp{} : Hx.Cause}

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
  for ba: Bool
  for fails: {Sp.run_fails(r) == True{} : Bool}
  {cause_of(Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, Hx.Unanswered{r}, p, c, a, ba})) == Hx.CRunFailed{r} : Hx.Cause}

# LAW headless_exit_transcript_before_flags (R4): without an earlier
# failure and without the final answer from the reserve, a failed
# terminal entry is the cause, whatever the flags
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
  {cause_of(Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, r, p, c, a, False{}})) == x : Hx.Cause}

# LAW headless_exit_compaction_before_autonomous (R4): without an earlier
# failure, a failed compaction is the cause, whatever the autonomous turn
# EXCLUDES: the two flags checked the other way round
law headless_exit_compaction_before_autonomous:
  for +r: Hx.Run
  for +p: Hx.Primary
  for a: Bool
  for +ba: Bool
  for ok: {Sp.run_cause(r) == None{} : Maybe<&2, Hx.Cause>}
  for clean: {Sp.primary_cause(p) == None{} : Maybe<&2, Hx.Cause>}
  {cause_of(Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, r, p, True{}, a, ba})) == Hx.CCompactionFailed{} : Hx.Cause}

# LAW headless_exit_autonomous_last (R4): without an earlier failure (no
# failed command, a quiet wait, a run that did not fail by Sp.run_cause, a
# terminal entry that is no failure by Sp.primary_cause, no failed
# compaction), a failed autonomous turn is the cause
# EXCLUDES: a failed autonomous turn reported as an answer or as another
#   cause
law headless_exit_autonomous_last:
  for +r: Hx.Run
  for +p: Hx.Primary
  for +ba: Bool
  for ok: {Sp.run_cause(r) == None{} : Maybe<&2, Hx.Cause>}
  for clean: {Sp.primary_cause(p) == None{} : Maybe<&2, Hx.Cause>}
  {cause_of(Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, r, p, False{}, True{}, ba})) == Hx.CAutonomousFailed{} : Hx.Cause}

# Laws: no failure by itself (R5)
# -------------------------------

# LAW headless_exit_unfailed_run_neutral (R5): a run that answered, was
# reset, went stale or was withdrawn exits as no run would
# EXCLUDES: a reset, stale or withdrawn run read as a failure (a
#   superseded run turning a good answer into exit 1), an answered run
#   that hides a later failure
law headless_exit_unfailed_run_neutral:
  for +cf: Bool
  for +w: Hx.Wait
  for +p: Hx.Primary
  for +c: Bool
  for +a: Bool
  for +ba: Bool
  {[Hx.decide(Hx.Facts{cf, w, Hx.Answered{}, p, c, a, ba}), Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.Reset{}}, p, c, a, ba}), Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.Stale{}}, p, c, a, ba}), Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.Withdrawn{}}, p, c, a, ba})] == [Hx.decide(Hx.Facts{cf, w, Hx.NoRun{}, p, c, a, ba}), Hx.decide(Hx.Facts{cf, w, Hx.NoRun{}, p, c, a, ba}), Hx.decide(Hx.Facts{cf, w, Hx.NoRun{}, p, c, a, ba}), Hx.decide(Hx.Facts{cf, w, Hx.NoRun{}, p, c, a, ba})] : List<&2, Hx.Verdict>}

# Laws: the budget (R2-R4)
# ------------------------

# LAW headless_exit_budget_limited_zero (R2, R4): a run whose final answer
# from the budget's reserve was delivered and in which no failure holds
# but those it excuses (budget_limited: the wait at the time budget's
# deadline, a run or a terminal entry the budget refused) exits 0 as
# budget-limited
# EXCLUDES: a run that gave its final answer exiting 1 because its wait
#   ended at the budget's deadline (a tool still running) or a later turn
#   the budget refused; such a run reported as answered
law headless_exit_budget_limited_zero:
  for +f: Hx.Facts
  for limited: {budget_limited(f) == True{} : Bool}
  {Hx.decide(f) == Hx.Verdict{0n, Hx.CBudgetLimited{}} : Hx.Verdict}

# LAW headless_exit_budget_unanswered_fails (R3): without the final answer
# from the budget's reserve, the wait ended at the time budget's deadline,
# a run the budget refused and a terminal entry the budget refused each
# exit 1, whatever the other facts
# EXCLUDES: a run the budget stopped before any answer read as done
law headless_exit_budget_unanswered_fails:
  for +cf: Bool
  for +w: Hx.Wait
  for +r: Hx.Run
  for +p: Hx.Primary
  for +c: Bool
  for +a: Bool
  {[code_of(Hx.decide(Hx.Facts{cf, Hx.BudgetDeadline{}, r, p, c, a, False{}})), code_of(Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.BudgetRefused{}}, p, c, a, False{}})), code_of(Hx.decide(Hx.Facts{cf, w, r, Hx.PBudgetRefused{}, c, a, False{}}))] == [1n, 1n, 1n] : List<&2, Nat>}

# LAW headless_exit_budget_keeps_other_failures (R3): the delivered final
# answer from the budget's reserve hides no other failure: a model error,
# a give-up at the wait limit, a failed command and a failed compaction
# each still exit 1, whatever the other facts
# EXCLUDES: a final answer from the reserve turning a model error, a
#   give-up, a failed command or a failed compaction into exit 0
law headless_exit_budget_keeps_other_failures:
  for +cf: Bool
  for +w: Hx.Wait
  for +r: Hx.Run
  for +p: Hx.Primary
  for +c: Bool
  for +a: Bool
  {[code_of(Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.ModelError{}}, p, c, a, True{}})), code_of(Hx.decide(Hx.Facts{cf, Hx.GaveUp{}, r, p, c, a, True{}})), code_of(Hx.decide(Hx.Facts{True{}, w, r, p, c, a, True{}})), code_of(Hx.decide(Hx.Facts{cf, w, r, p, True{}, a, True{}}))] == [1n, 1n, 1n, 1n] : List<&2, Nat>}

# LAW headless_exit_budget_example (R2-R4): anchor: a final answer from
# the reserve with a job running at the deadline exits 0 budget-limited
# (it exited 1 as a give-up before the budget rule), and so does one
# followed by a turn the budget refused; the same wait without that
# answer, and a budget refusal without it, exit 1 budget-unanswered; a
# model error after the final answer exits 1 with its cause
# EXCLUDES: an exit other than E1-E2 give for these facts
law headless_exit_budget_example:
  {[Hx.decide(Hx.Facts{False{}, Hx.BudgetDeadline{}, Hx.Answered{}, Hx.PAnswer{}, False{}, False{}, True{}}), Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, Hx.Unanswered{Hx.BudgetRefused{}}, Hx.PBudgetRefused{}, False{}, False{}, True{}}), Hx.decide(Hx.Facts{False{}, Hx.BudgetDeadline{}, Hx.Answered{}, Hx.PAnswer{}, False{}, False{}, False{}}), Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, Hx.Unanswered{Hx.BudgetRefused{}}, Hx.PBudgetRefused{}, False{}, False{}, False{}}), Hx.decide(Hx.Facts{False{}, Hx.BudgetDeadline{}, Hx.Unanswered{Hx.ModelError{}}, Hx.PProviderError{}, False{}, False{}, True{}})] == [Hx.Verdict{0n, Hx.CBudgetLimited{}}, Hx.Verdict{0n, Hx.CBudgetLimited{}}, Hx.Verdict{1n, Hx.CBudgetUnanswered{}}, Hx.Verdict{1n, Hx.CBudgetUnanswered{}}, Hx.Verdict{1n, Hx.CRunFailed{Hx.ModelError{}}}] : List<&2, Hx.Verdict>}

# LAW headless_exit_example (R1-R5): anchor: an answered run exits 0; a
# slash command alone exits 0; a model error, a stale run left with a
# tool use, a give-up and a failed command exit 1 with their causes
# EXCLUDES: an exit other than E1-E2 give for these facts
law headless_exit_example:
  {[Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, Hx.Answered{}, Hx.PAnswer{}, False{}, False{}, False{}}), Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, Hx.NoRun{}, Hx.PSlashOk{}, False{}, False{}, False{}}), Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, Hx.Unanswered{Hx.ModelError{}}, Hx.PProviderError{}, False{}, False{}, False{}}), Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, Hx.Unanswered{Hx.Stale{}}, Hx.PUnfinished{}, False{}, False{}, False{}}), Hx.decide(Hx.Facts{False{}, Hx.GaveUp{}, Hx.Answered{}, Hx.PAnswer{}, False{}, False{}, False{}}), Hx.decide(Hx.Facts{True{}, Hx.Quiet{}, Hx.NoRun{}, Hx.PNothing{}, False{}, False{}, False{}})] == [Hx.Verdict{0n, Hx.CAnswered{}}, Hx.Verdict{0n, Hx.CAnswered{}}, Hx.Verdict{1n, Hx.CRunFailed{Hx.ModelError{}}}, Hx.Verdict{1n, Hx.CUnfinished{}}, Hx.Verdict{1n, Hx.CGaveUp{}}, Hx.Verdict{1n, Hx.CCommandFailed{}}] : List<&2, Hx.Verdict>}

# Laws: the entry (R6)
# --------------------

# LAW headless_exit_entry_answers (R6): the entry answers every request
# Rust spells (W3) with the spelling (W4) of the core's exit for it
# EXCLUDES: a field misread or swapped (the flags, a wait, a run and a
#   primary tag), a reason lost on the way back, a cause tag of another
#   cause, a default
law headless_exit_entry_answers:
  for +f: Hx.Facts
  {FHx.ffi(SpW.w_exit_req(f, "")) == SpW.w_verdict(Hx.decide(f), "") : String}

# LAW headless_exit_entry_reads_only_requests (R6): every input the entry
# does not answer with the error form is exactly one spelled request (W3),
# with nothing before or after it
# EXCLUDES: an exit answered for input that is no request (an unknown tag
#   or reason, a short request, input left over, a lenient field reader)
law headless_exit_entry_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FHx.ffi(s)) == False{} : Bool}
  exs f: Hx.Facts
  {s == SpW.w_exit_req(f, "") : String}

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

# LAW headless_exit_entry_left_over (R6): a spelled request (W3) followed
# by any more input answers exactly the error form 'E ', then
# "headless_exit: malformed request"
# EXCLUDES: the input after the request ignored or read into a field, a
#   trailing newline or byte answered with an exit or with another error
#   text
law headless_exit_entry_left_over:
  for +f: Hx.Facts
  for +ch: Char
  for +t: String
  {FHx.ffi(SpW.w_exit_req(f, SCon{ch, t})) == Wr.err("headless_exit: malformed request") : String}

# LAW headless_exit_entry_example (R6): anchor: the strings Rust sends and
# the replies it reads: an answer, a model error, a stale run with an
# aborted entry, a failed compaction, a final answer from the reserve with
# the wait at the deadline (budget-limited), a budget refusal without it
# (budget unanswered); an unknown reason, an unknown wait, a short
# request, input left over
# EXCLUDES: another spelling of a request or a reply
law headless_exit_entry_example:
  {[FHx.ffi("F0,1,1,FFF"), FHx.ffi("F0,2,0,1,FFF"), FHx.ffi("F0,2,7,4,FFF"), FHx.ffi("F0,0,0,TFF"), FHx.ffi("F2,1,1,FFT"), FHx.ffi("F2,2,10,7,FFF"), FHx.ffi("F0,2,11,1,FFF"), FHx.ffi("F3,1,1,FFF"), FHx.ffi("F0,1,1,FF"), FHx.ffi("F0,1,1,FFFx")] == ["0,0,", "1,3,0,", "1,5,", "1,8,", "0,10,", "1,11,", Wr.err("headless_exit: malformed request"), Wr.err("headless_exit: malformed request"), Wr.err("headless_exit: malformed request"), Wr.err("headless_exit: malformed request")] : List<&2, String>}
