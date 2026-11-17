# eukhe: the laws of area autonomous

import Base
import ../bend/verify.bend as V
import ../bend/autonomous.bend as Au
import ../bend/ffi_autonomous.bend as FAu
import ../bend/wire.bend as Wr
import ../spec/autonomous/autonomous.bend as SpA

# (AU2-AU6) An autonomous run goes on until its checks or its budget end it
# --------------------------------------------------------------------------
# bend/autonomous.bend, run as the compiled core by
# bend/ffi_autonomous.bend (eukhe-bend rules/autonomous.rs; asked by
# eukhe-core durable/goals at each final answer with whether the run is
# autonomous, how the answer ended, the checks' outcome at that answer and
# whether the run's budget admits work). spec/autonomous/autonomous.bend
# states the rule in words (A1-A5) and its wire (W1-W3). Every input is
# free: any facts, any label, any string.
#
# R1: the run is continued with its prompt exactly when it is autonomous,
#     its answer settled, it has no check and the budget admits work.
# R2: the checks' return holds the run exactly when it is autonomous, its
#     answer settled, the claim went back and the budget admits work.
# R3: an ended claim stops an autonomous run with the claim's label,
#     whatever the budget.
# R4: a budget that admits no work stops an autonomous run whose answer
#     settled and whose claim did not end.
# R5: the run gets nothing exactly when it is not autonomous or its answer
#     broke.
# R6: the entry answers each request Rust writes (W1) with the spelling
#     (W2) of the core's step for it, and any input that is not exactly
#     one request with exactly `E autonomous: malformed request`.

# Laws: the step (R1-R5)
# ----------------------

# LAW autonomous_continues_iff (R1): the run is continued with its prompt
# exactly when it is autonomous, its answer settled, it has no check and
# the budget admits work (SpA.continues)
# EXCLUDES: a run with checks continued past its claim (the checks
#   bypassed), a run continued past its budget, a failed or aborted answer
#   continued, a run not autonomous continued, an autonomous run without
#   checks that stops while the budget admits work
law autonomous_continues_iff:
  for +f: Au.Facts
  {SpA.is_continue(Au.decide(f)) == SpA.continues(f) : Bool}

# LAW autonomous_holds_iff (R2): the checks' return holds the run exactly
# when it is autonomous, its answer settled, the claim went back to the
# worker and the budget admits work (SpA.holds)
# EXCLUDES: a returned claim answered by a second continuation of the run
#   (two inputs for one answer), a returned claim that stops the run, a
#   hold past the budget
law autonomous_holds_iff:
  for +f: Au.Facts
  {SpA.is_hold(Au.decide(f)) == SpA.holds(f) : Bool}

# LAW autonomous_off_iff (R5): the run gets nothing exactly when it is not
# autonomous or its final answer broke (SpA.off)
# EXCLUDES: a run that is not autonomous continued, stopped or held; a
#   failed or aborted answer read as a claim's end or a budget stop; an
#   autonomous settled answer ignored
law autonomous_off_iff:
  for +f: Au.Facts
  {SpA.is_off(Au.decide(f)) == SpA.off(f) : Bool}

# LAW autonomous_claim_end_stops (R3): a claim that ended stops an
# autonomous run whose answer settled, with the claim's label, whatever
# the budget
# EXCLUDES: a run continued after its checks ended the claim (the old
#   gate loop's extra turns), another label reported, a budget stop
#   hiding the checks' verdict
law autonomous_claim_end_stops:
  for l: V.Label
  for b: Au.Budget
  {Au.decide(Au.Facts{True{}, Au.Settled{}, Au.Ended{l}, b}) == Au.Stop{Au.ByChecks{l}} : Au.Step}

# LAW autonomous_short_stops (R4): a budget that admits no work stops an
# autonomous run whose answer settled and whose claim did not end
# EXCLUDES: a run continued or held past its limits, a budget stop read
#   as a checks' verdict
law autonomous_short_stops:
  for +c: Au.Checks
  for h: {SpA.ended(c) == False{} : Bool}
  {Au.decide(Au.Facts{True{}, Au.Settled{}, c, Au.Short{}}) == Au.Stop{Au.ByBudget{}} : Au.Step}

# LAW autonomous_example (R1-R5): anchor: an autonomous run without checks
# continues; a returned claim holds; a claim ended failed stops failed,
# one ended passed with the budget short stops passed; a budget short
# without checks stops by the budget; a broken answer and a run not
# autonomous get nothing
# EXCLUDES: a step other than A1-A4 give for these facts
law autonomous_example:
  {[Au.decide(Au.Facts{True{}, Au.Settled{}, Au.Unchecked{}, Au.Working{}}), Au.decide(Au.Facts{True{}, Au.Settled{}, Au.Returned{}, Au.Working{}}), Au.decide(Au.Facts{True{}, Au.Settled{}, Au.Ended{V.Failed{}}, Au.Working{}}), Au.decide(Au.Facts{True{}, Au.Settled{}, Au.Ended{V.Passed{}}, Au.Short{}}), Au.decide(Au.Facts{True{}, Au.Settled{}, Au.Unchecked{}, Au.Short{}}), Au.decide(Au.Facts{True{}, Au.Broken{}, Au.Unchecked{}, Au.Working{}}), Au.decide(Au.Facts{False{}, Au.Settled{}, Au.Unchecked{}, Au.Working{}})] == [Au.Continue{}, Au.Hold{}, Au.Stop{Au.ByChecks{V.Failed{}}}, Au.Stop{Au.ByChecks{V.Passed{}}}, Au.Stop{Au.ByBudget{}}, Au.Off{}, Au.Off{}] : List<&2, Au.Step>}

# Laws: the entry (R6)
# --------------------

# LAW autonomous_entry_answers (R6): the entry answers every request Rust
# spells (W1) with the spelling (W2) of the core's step for it
# EXCLUDES: a fact misread, a label lost on the way, a step tag of another
#   step, a default
law autonomous_entry_answers:
  for +f: Au.Facts
  {FAu.ffi(SpA.w_req(f, "")) == SpA.w_step(Au.decide(f), "") : String}

# LAW autonomous_entry_malformed_exact (R6): every input that is not
# exactly one request (an unknown answer, checks, label or budget tag, a
# malformed field, input left over) gets exactly the error form 'E ', then
# "autonomous: malformed request"
# EXCLUDES: a step answered for input that is no request, another error
#   text, a default
law autonomous_entry_malformed_exact:
  for +s: String
  for no: {SpA.read_req(s) == None{} : Maybe<&2, Au.Facts>}
  {FAu.ffi(s) == Wr.err("autonomous: malformed request") : String}

# LAW autonomous_entry_left_over (R6): a spelled request (W1) followed by
# any more input answers exactly the error form
# EXCLUDES: the input after the request ignored or read into a field
law autonomous_entry_left_over:
  for +f: Au.Facts
  for +ch: Char
  for +t: String
  {FAu.ffi(SpA.w_req(f, SCon{ch, t})) == Wr.err("autonomous: malformed request") : String}

# LAW autonomous_entry_example (R6): anchor: the strings Rust sends and the
# replies it reads: a run without checks, a returned claim, a claim ended
# passed, a budget short, a broken answer, a run not autonomous; an
# unknown answer, checks, label and budget tag, a malformed Bool, a short
# request, input left over
# EXCLUDES: another spelling of a request or a reply
law autonomous_entry_example:
  {[FAu.ffi("T0,0,0,"), FAu.ffi("T0,1,0,"), FAu.ffi("T0,2,3,1,"), FAu.ffi("T0,0,1,"), FAu.ffi("T1,0,0,"), FAu.ffi("F0,0,0,"), FAu.ffi("T2,0,0,"), FAu.ffi("T0,3,0,"), FAu.ffi("T0,2,4,0,"), FAu.ffi("T0,0,2,"), FAu.ffi("X0,0,0,"), FAu.ffi("T0,0,"), FAu.ffi("T0,0,0,x")] == ["2,", "1,", "3,0,3,", "3,1,", "0,", "0,", Wr.err("autonomous: malformed request"), Wr.err("autonomous: malformed request"), Wr.err("autonomous: malformed request"), Wr.err("autonomous: malformed request"), Wr.err("autonomous: malformed request"), Wr.err("autonomous: malformed request"), Wr.err("autonomous: malformed request")] : List<&2, String>}
