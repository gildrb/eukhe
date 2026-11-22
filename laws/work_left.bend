# eukhe: the laws of area work_left

import Base
import ../bend/progress.bend as Pg
import ../bend/work_left.bend as Wl
import ../bend/ffi_work_left.bend as FWl
import ../bend/wire.bend as Wr
import ../spec/agents/work_left.bend as SpL
import ./base.bend as LawsBase

# (A4) A final answer with work left continues
# --------------------------------------------
# bend/work_left.bend, run as the compiled core by bend/ffi_work_left.bend
# (eukhe-bend rules/work_left.rs `step`; asked by the work-left hook,
# crates/eukhe-core/src/durable/directors/work_left.rs, at each final
# answer the Director stack, the autonomous run and the loop did not
# continue: first unread, then again with the judge's reading when the
# core asks for it). spec/agents/work_left.bend states the rule in words
# (K1-K5) and its wire (K6-K8). Every input is free: any fact, any count
# of steps, any progress check, any reading, any string.
#
# R1: the run goes on exactly when the answer is the run's to judge (K1)
#     and the judge read work left in it (K3).
# R2: the core asks for the judge's reading exactly when the answer is the
#     run's to judge and no reading is given (K2).
# R3: a continuation costs exactly one step of the Director loop; a step
#     that does not go on costs none (K5).
# R4: the entry answers each request Rust writes (K6) with the spelling
#     (K7) of the core's step for it; an input it answers with a step is
#     exactly such a request; every other input gets exactly
#     `E work_left: malformed request` (K8).
# Every other answer yields (K4): the step has three outcomes, so R1 and
# R2 fix the third.
# A4's Rust parts are not laws: which answers state work left (the
# judge's prompt), the facts Rust gathers, the continuation's text and
# origin, the display row, and the record in eukhe.directors that a rerun
# repeats. Their gate is the tests in
# crates/eukhe-core/src/durable/directors/work_left_tests.rs:
# an_answer_that_asks_to_go_on_continues_the_run_without_the_user,
# a_done_or_unjudged_answer_stands, a_run_that_did_not_act_is_never_judged,
# queued_user_input_holds_the_answer,
# the_chain_ends_after_stall_steps_continuations_without_new_work,
# a_rerun_repeats_the_recorded_decision.

# Laws: the step (R1-R3)
# ----------------------

# LAW work_left_continues_iff_left (R1): the run goes on exactly when no
# autonomous run or loop drives it, no input is queued, it acted since the
# user's last message, the budget admits more work, the progress check
# goes on, the loop has a step left, and the judge read work left in its
# final answer (SpL.continue_due)
# EXCLUDES: a run handed back to an absent user while its answer leaves
#   work undone; a continuation past a driver, queued input, a stopped
#   progress check, an empty budget or the last loop step; a continuation
#   of a run that only read; an unjudged or finished answer continued
law work_left_continues_iff_left:
  for +f: Wl.Facts
  {SpL.continues(Wl.decide(f)) == SpL.continue_due(f) : Bool}

# LAW work_left_asks_iff_unread (R2): the core asks for the judge's
# reading exactly when the answer is the run's to judge (SpL.judged) and
# the judge has not read it (SpL.ask_due)
# EXCLUDES: a judge request for an answer the run will not judge anyway (a
#   driver, queued input, a run that only read, an empty budget, a stopped
#   progress check, no loop step left): a request that costs and changes
#   nothing; an answer the run judges left unread; a second request once a
#   reading is given
law work_left_asks_iff_unread:
  for +f: Wl.Facts
  {SpL.asks(Wl.decide(f)) == SpL.ask_due(f) : Bool}

# LAW work_left_continue_costs_one_step (R3): the loop's steps before the
# step are the steps a continuation leaves plus the one it spent, and a
# step that does not go on leaves them as they were (SpL.steps_before)
# EXCLUDES: a continuation that spends no step (an endless chain), more
#   than one, or leaves a count unrelated to the loop's
law work_left_continue_costs_one_step:
  for +f: Wl.Facts
  {SpL.steps_before(f, Wl.decide(f)) == SpL.left_of(f) : Nat}

# LAW work_left_example (R1-R3): anchor: an answer of a run that acted,
# undriven and funded, with 3 steps left, read as work left continues with
# 2 left; the same unread asks; the same read as finished, or unjudged,
# yields; with a driver, queued input, no act, no budget, a stopped
# progress check or no step left it yields
# EXCLUDES: a step other than K1-K5 give for these facts
law work_left_example:
  {[Wl.decide(Wl.Facts{False{}, False{}, True{}, True{}, Pg.Go{1n}, 3n, Wl.Left{}}), Wl.decide(Wl.Facts{False{}, False{}, True{}, True{}, Pg.Go{0n}, 3n, Wl.Unread{}}), Wl.decide(Wl.Facts{False{}, False{}, True{}, True{}, Pg.Go{0n}, 3n, Wl.Finished{}}), Wl.decide(Wl.Facts{False{}, False{}, True{}, True{}, Pg.Go{0n}, 3n, Wl.Unjudged{}}), Wl.decide(Wl.Facts{True{}, False{}, True{}, True{}, Pg.Go{0n}, 3n, Wl.Left{}}), Wl.decide(Wl.Facts{False{}, True{}, True{}, True{}, Pg.Go{0n}, 3n, Wl.Left{}}), Wl.decide(Wl.Facts{False{}, False{}, False{}, True{}, Pg.Go{0n}, 3n, Wl.Left{}}), Wl.decide(Wl.Facts{False{}, False{}, True{}, False{}, Pg.Go{0n}, 3n, Wl.Left{}}), Wl.decide(Wl.Facts{False{}, False{}, True{}, True{}, Pg.Stop{3n}, 3n, Wl.Left{}}), Wl.decide(Wl.Facts{False{}, False{}, True{}, True{}, Pg.Go{0n}, 0n, Wl.Left{}})] == [Wl.Continue{2n}, Wl.Ask{}, Wl.Yield{}, Wl.Yield{}, Wl.Yield{}, Wl.Yield{}, Wl.Yield{}, Wl.Yield{}, Wl.Yield{}, Wl.Yield{}] : List<&2, Wl.Step>}

# Laws: the entry (R4)
# --------------------

# the counts of a request fit the wire (below 10^14, as Rust saturates
# them): the loop's steps left and the progress check's count of stalls
def wl_fits(f: Wl.Facts) -> Bool:
  match f:
    case Wl.Facts{d, q, a, b, s, n, r}:
      match s:
        case Pg.Go{k}:
          Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(k))
        case Pg.Stop{k}:
          Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(k))

# LAW work_left_entry_answers (R4): the entry answers every request Rust
# spells (K6), its counts within the wire (wl_fits), with the spelling
# (K7) of the core's step for it
# EXCLUDES: a fact, the steps, the progress check or the reading misread;
#   a step tag of another step; the steps left lost on the way; a default
law work_left_entry_answers:
  for +f: Wl.Facts
  for fits: {wl_fits(f) == True{} : Bool}
  {FWl.ffi(SpL.w_req(f, "")) == SpL.w_step(Wl.decide(f), "") : String}

# LAW work_left_entry_exact (R4): every input the entry does not answer
# with the error form is exactly one request Rust spells (K6) for some
# facts, its counts within the wire, with nothing after it
# EXCLUDES: an answer for input that is no request: an unknown progress or
#   reading tag, a malformed field, a short request, a count past the
#   wire, input left over
law work_left_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FWl.ffi(s)) == False{} : Bool}
  exs f: Wl.Facts
  {s == SpL.w_req(f, "") : String} & {wl_fits(f) == True{} : Bool}

# LAW work_left_entry_refuses (R4): every error the entry answers is
# exactly 'E ', then "work_left: malformed request"
# EXCLUDES: an error text that varies with the input, a second error form
law work_left_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FWl.ffi(s)) == True{} : Bool}
  {FWl.ffi(s) == Wr.err("work_left: malformed request") : String}

# LAW work_left_entry_left_over (R4): a spelled request (K6), its counts
# within the wire (wl_fits), followed by any more input answers exactly
# the error form
# EXCLUDES: the input after the request ignored or read into a field
law work_left_entry_left_over:
  for +f: Wl.Facts
  for fits: {wl_fits(f) == True{} : Bool}
  for +ch: Char
  for +t: String
  {FWl.ffi(SpL.w_req(f, SCon{ch, t})) == Wr.err("work_left: malformed request") : String}

# LAW work_left_entry_example (R4): anchor: the strings Rust sends and the
# replies it reads: an answer read as work left with 3 steps left, one not
# read yet, one finished, one driven, one with its progress check stopped;
# an unknown progress tag, an unknown reading, a malformed Bool, a short
# request, input left over
# EXCLUDES: another spelling of a request or a reply
law work_left_entry_example:
  {[FWl.ffi("FFTT0,1,3,2,"), FWl.ffi("FFTT0,0,3,0,"), FWl.ffi("FFTT0,0,3,1,"), FWl.ffi("TFTT0,0,3,2,"), FWl.ffi("FFTT1,3,3,2,"), FWl.ffi("FFTT2,0,3,2,"), FWl.ffi("FFTT0,0,3,4,"), FWl.ffi("XFTT0,0,3,2,"), FWl.ffi("FFTT0,0,3,"), FWl.ffi("FFTT0,0,3,2,x")] == ["0,2,", "2,", "1,", "1,", "1,", Wr.err("work_left: malformed request"), Wr.err("work_left: malformed request"), Wr.err("work_left: malformed request"), Wr.err("work_left: malformed request"), Wr.err("work_left: malformed request")] : List<&2, String>}
