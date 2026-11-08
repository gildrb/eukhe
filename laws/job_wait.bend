# eukhe: the laws of area job_wait

import Base
import ../bend/ffi_job_wait.bend as FJw
import ../bend/job.bend as Jb
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S2) A blocking wait on a job, event by event
# ---------------------------------------------
# The Rust wait (crates/eukhe-core/src/durable/jobs/mod.rs `wait_until`)
# opens the stepper bend/ffi_job_wait.bend with its budget in ticks and
# sends each event in the order it arrives: a tick (the deadline timer
# fired) or the job's end; it settles, detaches or waits on as the reply
# says. The requirement is stated here (no other document states it; the
# model `wait` of bend/job.bend is pinned by the laws of area job):
#
# S2: the stepper opened with any budget b answers, after any events in
#     any order, the model's wait on those events with budget b, the end
#     standing for every exit and for the kill: an end before b ticks
#     settles, b ticks with no end detach, a settled or detached call
#     stays so, and no call both settles and detaches.
#     Laws: job_wait_step_is_model, job_wait_final_is_final,
#     job_wait_never_settles_and_detaches, job_wait_end_in_time_settles,
#     job_wait_budget_spent_detaches.
# A1: an open is exactly one Nat that fits the wire (the budget); any
#     other open answers `E job_wait: malformed open`, and the refused
#     stepper answers every later input with `E job_wait: the open was
#     refused`.
#     Laws: job_wait_open_exact, job_wait_refused_open.
# A2: an event is exactly the tag 0 (a tick) or 1 (the end); any other
#     input (an unknown tag, a bad number, input left over) answers `E
#     job_wait: malformed event` and keeps the wait.
#     Laws: job_wait_step_exact, job_wait_step_refuses,
#     job_wait_entry_unknown_tag.
# (omp's wait tool, packages/coding-agent/src/tools/wait.ts, races the
# job's promise against a timer: the job settling or the time running
# out ends the call, the same two ends as S2.)
#
# The grammar is restated from the entry's header, never from its code:
#
#   open    budget: Nat                 reply: Turn
#   step    Ev                          reply: Turn
#   Ev      0 a tick | 1 the end came
#   Turn    0 waits | 1 settles | 2 detaches

# Terms
# -----

# A host event: None a tick (the deadline timer fired), Some{x} the job's
# end x came. The wire carries only that it came: x stays the host's.
def jw_spell_ev(e: Maybe<&2, Jb.End>) -> String:
  match e:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{x}:
      Wr.put_nat(1n, "")

# the model's event for a host event: a tick, or the exit or kill the
# end is
def jw_jev(e: Maybe<&2, Jb.End>) -> Jb.JEv:
  match e:
    case None{}:
      Jb.Tick{}
    case Some{x}:
      match x:
        case Jb.Exited{c}:
          Jb.Quit{c}
        case Jb.Killed{}:
          Jb.Kill{}

def jw_jevs(es: List<&2, Maybe<&2, Jb.End>>) -> List<&2, Jb.JEv>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      jw_jev(e) <> jw_jevs(rest)

# the model's answer spelled as a turn: 0 the call waits (no answer yet),
# 1 it settled, 2 it detached
def jw_spell_wait(w: Maybe<&2, Jb.Wait>) -> String:
  match w:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{a}:
      match a:
        case Jb.Settled{e}:
          Wr.put_nat(1n, "")
        case Jb.Detached{}:
          Wr.put_nat(2n, "")

# the reply after the host events es, from the state and reply r
def jw_last(es: List<&2, Maybe<&2, Jb.End>>, r: FJw.St & String) -> String:
  match es:
    case Nil{}:
      (st, out) = r
      out
    case e <> rest:
      (st, out) = r
      jw_last(rest, FJw.step(st, jw_spell_ev(e)))

# the reply after the stepper opened with budget b saw the host events es
def jw_run(+b: Nat, es: List<&2, Maybe<&2, Jb.End>>) -> String:
  jw_last(es, FJw.open(Wr.put_nat(b, "")))

# every reply, from the state and reply r through the host events es
def jw_feed(es: List<&2, Maybe<&2, Jb.End>>, r: FJw.St & String) -> List<&2, String>:
  match es:
    case Nil{}:
      (st, out) = r
      [out]
    case e <> rest:
      (st, out) = r
      out <> jw_feed(rest, FJw.step(st, jw_spell_ev(e)))

# the replies of raw inputs, from the state and reply r
def jw_feed_raw(ins: List<&2, String>, r: FJw.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      (st, out) = r
      [out]
    case i <> t:
      (st, out) = r
      out <> jw_feed_raw(t, FJw.step(st, i))

# s is one of xs
def jw_has(xs: List<&2, String>, +s: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(String.eq(x, s), jw_has(rest, s))

# the ticks among es
def jw_ticks(es: List<&2, Maybe<&2, Jb.End>>) -> Nat:
  match es:
    case Nil{}:
      0n
    case e <> rest:
      match e:
        case None{}:
          1n+jw_ticks(rest)
        case Some{x}:
          jw_ticks(rest)

# an end is among es
def jw_has_end(es: List<&2, Maybe<&2, Jb.End>>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case None{}:
          jw_has_end(rest)
        case Some{x}:
          True{}

# the reply of a stepper's answer
def jw_reply(r: FJw.St & String) -> String:
  (st, out) = r
  out

# one refusal of a refused open per input of ins
def jw_refusals(ins: List<&2, String>) -> List<&2, String>:
  match ins:
    case Nil{}:
      Nil{}
    case i <> t:
      SCon{'E', SCon{' ', "job_wait: the open was refused"}} <> jw_refusals(t)

# Laws
# ----

# LAW job_wait_step_is_model: the stepper opened with any budget b (in
# ticks) answers, after any host events in any order, the model's wait
# on those events with budget b, the end standing for any exit or the
# kill (each end its own); every prefix of a run is such a run, so every
# reply of the stepper is the model's
# EXCLUDES: a tick or an end ignored, miscounted or read as the other, a
# settle after a detach or a detach after a settle, a budget off by one,
# a wait that settles with no end or detaches with budget left
law job_wait_step_is_model:
  for +b: Nat
  for fits: {LawsBase.wire_fits(b) == True{} : Bool}
  for es: List<&2, Maybe<&2, Jb.End>>
  {jw_run(b, es) == jw_spell_wait(Jb.wait(jw_jevs(es), b)) : String}

# LAW job_wait_final_is_final: once a run settled or detached, no later
# event changes its reply
# EXCLUDES: a final turn that is not sticky (a late end settling a
# detached call, a late tick detaching a settled one, a reset)
law job_wait_final_is_final:
  for +b: Nat
  for fits: {LawsBase.wire_fits(b) == True{} : Bool}
  for +es: List<&2, Maybe<&2, Jb.End>>
  for more: List<&2, Maybe<&2, Jb.End>>
  for done: {String.eq(jw_run(b, es), Wr.put_nat(0n, "")) == False{} : Bool}
  {jw_run(b, List.append(&2, Maybe<&2, Jb.End>, es, more)) == jw_run(b, es) : String}

# LAW job_wait_never_settles_and_detaches: no run, in any order of
# events, both settles and detaches
# EXCLUDES: a call that returns twice: a settle and a detach in one run
law job_wait_never_settles_and_detaches:
  for +b: Nat
  for fits: {LawsBase.wire_fits(b) == True{} : Bool}
  for +es: List<&2, Maybe<&2, Jb.End>>
  {Bool.and(jw_has(jw_feed(es, FJw.open(Wr.put_nat(b, ""))), Wr.put_nat(1n, "")), jw_has(jw_feed(es, FJw.open(Wr.put_nat(b, ""))), Wr.put_nat(2n, ""))) == False{} : Bool}

# LAW job_wait_end_in_time_settles: an end that comes before the budget
# runs out settles the call, after any events before it
# EXCLUDES: an end ignored, an end with budget left that detaches
law job_wait_end_in_time_settles:
  for +b: Nat
  for fits: {LawsBase.wire_fits(b) == True{} : Bool}
  for +es: List<&2, Maybe<&2, Jb.End>>
  for +x: Jb.End
  for early: {Nat.is_lt(jw_ticks(es), b) == True{} : Bool}
  {jw_run(b, List.append(&2, Maybe<&2, Jb.End>, es, [Some{x}])) == Wr.put_nat(1n, "") : String}

# LAW job_wait_budget_spent_detaches: when the budget runs out with no
# end, the call detaches
# EXCLUDES: a tick ignored, a call that blocks past its budget
law job_wait_budget_spent_detaches:
  for +b: Nat
  for fits: {LawsBase.wire_fits(b) == True{} : Bool}
  for +es: List<&2, Maybe<&2, Jb.End>>
  for none: {jw_has_end(es) == False{} : Bool}
  for spent: {Nat.is_le(b, jw_ticks(es)) == True{} : Bool}
  {jw_run(b, es) == Wr.put_nat(2n, "") : String}

# LAW job_wait_open_exact (A1): every open the stepper answers other than
# with the error form is exactly one Nat that fits the wire, with nothing
# after it (the budget job_wait_step_is_model reads)
# EXCLUDES: a budget guessed from garbage, a leading zero or a sign read,
#   input left over after the budget ignored, an open with no budget
#   answered as a wait
law job_wait_open_exact:
  for +i: String
  for ok: {LawsBase.wire_opens_err(jw_reply(FJw.open(i))) == False{} : Bool}
  exs b: Nat
  {i == Wr.put_nat(b, "") : String} & {LawsBase.wire_fits(b) == True{} : Bool}

# LAW job_wait_refused_open (A1): an open the stepper answers with the
# error form answers exactly 'E ' + "job_wait: malformed open", and the
# stepper then answers every later input, whatever it is, with exactly
# 'E ' + "job_wait: the open was refused"
# EXCLUDES: another error text, a refused stepper that later settles,
#   detaches or waits (a live state from garbage)
law job_wait_refused_open:
  for +i: String
  for bad: {LawsBase.wire_opens_err(jw_reply(FJw.open(i))) == True{} : Bool}
  for ins: List<&2, String>
  {jw_feed_raw(ins, FJw.open(i)) == SCon{'E', SCon{' ', "job_wait: malformed open"}} <> jw_refusals(ins) : List<&2, String>}

# LAW job_wait_step_exact (A2): in any wait, every input the stepper
# answers other than with the error form is exactly one tag below 2 (0 a
# tick, 1 the end), with nothing after it
# EXCLUDES: an event guessed from garbage (a third tag, a bad number, no
#   input), input left over after the tag ignored
law job_wait_step_exact:
  for +w: FJw.Wt
  for +i: String
  for ok: {LawsBase.wire_opens_err(jw_reply(FJw.step(FJw.Open{w}, i))) == False{} : Bool}
  exs t: Nat
  {i == Wr.put_nat(t, "") : String} & {Nat.is_lt(t, 2n) == True{} : Bool}

# LAW job_wait_step_refuses (A2): in any wait, an input the stepper
# answers with the error form keeps the wait and answers exactly 'E ' +
# "job_wait: malformed event"
# EXCLUDES: a wait changed (budget spent, turn changed) by garbage,
#   another error text
law job_wait_step_refuses:
  for +w: FJw.Wt
  for +i: String
  for bad: {LawsBase.wire_opens_err(jw_reply(FJw.step(FJw.Open{w}, i))) == True{} : Bool}
  {FJw.step(FJw.Open{w}, i) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}

# LAW job_wait_entry_unknown_tag: in any wait, a tag past 1 (any number
# of digits) keeps the wait and answers exactly the malformed-event error
# form, whatever follows
# EXCLUDES: an unknown tag read as a tick or as the end
law job_wait_entry_unknown_tag:
  for +w: FJw.Wt
  for +n: Nat
  for +rest: String
  {FJw.step(FJw.Open{w}, Wr.put_nat(2n+n, rest)) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}

# LAW job_wait_entry_example: anchor: the bytes Rust sends (an open with
# one tick of budget; the tick; the end) and their replies, a passed
# deadline before the end, a run with budget 0, malformed opens and
# events; the premises of the laws above hold for some input
# EXCLUDES: an entry that answers other bytes than the grammar's; vacuous
# premises
law job_wait_entry_example:
  {jw_feed_raw(["0,", "1,"], FJw.open("1,")) == ["0,", "2,", "2,"] : List<&2, String>} &
  {jw_feed_raw(["1,", "0,"], FJw.open("1,")) == ["0,", "1,", "1,"] : List<&2, String>} &
  {jw_feed_raw(["1,"], FJw.open("0,")) == ["2,", "2,"] : List<&2, String>} &
  {jw_feed_raw(["2,", "0,x", "", "0,"], FJw.open("2,")) == ["0,", "E job_wait: malformed event", "E job_wait: malformed event", "E job_wait: malformed event", "0,"] : List<&2, String>} &
  {jw_feed_raw(["0,"], FJw.open("1")) == ["E job_wait: malformed open", "E job_wait: the open was refused"] : List<&2, String>} &
  {[LawsBase.wire_opens_err(jw_reply(FJw.open("01,"))), LawsBase.wire_opens_err(jw_reply(FJw.open("1,x"))), LawsBase.wire_opens_err(jw_reply(FJw.open("1,")))] == [True{}, True{}, False{}] : List<&2, Bool>} &
  {[LawsBase.wire_opens_err(jw_reply(FJw.step(FJw.Open{FJw.Waiting{1n}}, "2,"))), LawsBase.wire_opens_err(jw_reply(FJw.step(FJw.Open{FJw.Waiting{1n}}, "1,1,"))), LawsBase.wire_opens_err(jw_reply(FJw.step(FJw.Open{FJw.Waiting{1n}}, "0,")))] == [True{}, True{}, False{}] : List<&2, Bool>} &
  {[LawsBase.wire_fits(1n), Nat.is_lt(jw_ticks([None{}]), 2n), jw_has_end([None{}]), Nat.is_le(1n, jw_ticks([None{}])), String.eq(jw_run(1n, [None{}]), "0,")] == [True{}, True{}, False{}, True{}, False{}] : List<&2, Bool>}
