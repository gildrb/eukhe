# eukhe: the laws of area job_wait

import Base
import ../bend/ffi_job_wait.bend as FJw
import ../bend/job.bend as Jb
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ./job.bend as Job

# (S2) A blocking wait on a job, event by event
# ---------------------------------------------
# docs/runtime.md S2, the model `wait` in bend/job.bend. The Rust wait
# (crates/eukhe-core/src/durable/jobs/mod.rs `wait_until`) opens the
# stepper bend/ffi_job_wait.bend with its budget in ticks and sends each
# event in the order it arrives: a tick (the deadline timer fired) or the
# job's end; it settles, detaches or waits on as the reply says. These
# laws pin every reply for every budget and every order of events: the
# model's answer, the end standing for every exit and for the kill. The
# grammar is restated from the entry's header, never from its code:
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

# the ticks of budget left after an event, from l: a tick spends one (none
# below zero), the end none
def jw_left(ready: Bool, l: Nat) -> Nat:
  match ready:
    case True{}:
      l
    case False{}:
      match l:
        case 0n:
          0n
        case 1n+p:
          p

# the stepper after the turn t, with left ticks of budget: a wait keeps
# waiting, a settle or a detach is final
def jw_after(left: Nat, +t: Jb.Turn) -> FJw.St & String:
  match t:
    case Jb.Waits{}:
      (FJw.Open{FJw.Waiting{left}}, Job.wt_spell_turn(Jb.Waits{}))
    case Jb.Settles{}:
      (FJw.Open{FJw.Final{Jb.Settles{}}}, Job.wt_spell_turn(Jb.Settles{}))
    case Jb.Detaches{}:
      (FJw.Open{FJw.Final{Jb.Detaches{}}}, Job.wt_spell_turn(Jb.Detaches{}))

# one event (the end when ready) in the wait w: waiting, the poll with
# the deadline due when no tick of budget is left after the event and the
# end ready when it is the end; final, the same final turn
def jw_step(w: FJw.Wt, +ready: Bool) -> FJw.St & String:
  match w:
    case FJw.Waiting{l}:
      +left = jw_left(ready, l)
      jw_after(left, Job.wt_poll_spec(Nat.is_eq(left, 0n), ready))
    case FJw.Final{+t}:
      (FJw.Open{FJw.Final{t}}, Job.wt_spell_turn(t))

# the budget s spells, when s is exactly one Nat
def jw_read_open.end(whole: Bool, b: Nat) -> Maybe<&2, Nat>:
  match whole:
    case True{}:
      Some{b}
    case False{}:
      None{}

def jw_read_open.go(r: Wr.Dec<Nat>) -> Maybe<&2, Nat>:
  match r:
    case Wr.Got{b, s}:
      jw_read_open.end(Wr.end(s), b)
    case Wr.Bad{}:
      None{}

def jw_read_open(s: String) -> Maybe<&2, Nat>:
  jw_read_open.go(Wr.get_nat(s))

# the event s spells (True: the end, False: a tick), when s is exactly
# one tag 0 or 1
def jw_read_ev.tag(t: Nat) -> Maybe<&2, Bool>:
  match t:
    case 0n:
      Some{False{}}
    case 1n:
      Some{True{}}
    case 2n+p:
      None{}

def jw_read_ev.end(whole: Bool, t: Nat) -> Maybe<&2, Bool>:
  match whole:
    case True{}:
      jw_read_ev.tag(t)
    case False{}:
      None{}

def jw_read_ev.go(r: Wr.Dec<Nat>) -> Maybe<&2, Bool>:
  match r:
    case Wr.Got{t, s}:
      jw_read_ev.end(Wr.end(s), t)
    case Wr.Bad{}:
      None{}

def jw_read_ev(s: String) -> Maybe<&2, Bool>:
  jw_read_ev.go(Wr.get_nat(s))

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

# LAW job_wait_entry_open: an open with a budget b (spelled from the
# wire's primitives) is the poll at rest: it detaches with no budget,
# else it waits with b ticks left
# EXCLUDES: a budget misread or off by one, an open that settles
law job_wait_entry_open:
  for +b: Nat
  for fits: {LawsBase.wire_fits(b) == True{} : Bool}
  {FJw.open(Wr.put_nat(b, "")) == jw_after(b, Job.wt_poll_spec(Nat.is_eq(b, 0n), False{})) : FJw.St & String}

# LAW job_wait_entry_open_reads: an open input the laws' reader reads as
# exactly one Nat b opens as the budget b
# EXCLUDES: an open input read otherwise than by the wire's grammar
law job_wait_entry_open_reads:
  for +i: String
  for +b: Nat
  for got: {jw_read_open(i) == Some{b} : Maybe<&2, Nat>}
  {FJw.open(i) == jw_after(b, Job.wt_poll_spec(Nat.is_eq(b, 0n), False{})) : FJw.St & String}

# LAW job_wait_entry_open_malformed_exact: an open input that is not
# exactly one Nat opens the refused state and answers exactly the error
# form 'E ' + "job_wait: malformed open"
# EXCLUDES: a guessed budget, another error text, a live state from
# garbage
law job_wait_entry_open_malformed_exact:
  for +i: String
  for no: {jw_read_open(i) == None{} : Maybe<&2, Nat>}
  {FJw.open(i) == (FJw.Shut{}, SCon{'E', SCon{' ', "job_wait: malformed open"}}) : FJw.St & String}

# LAW job_wait_entry_shut: a refused open answers every step with exactly
# the error form 'E ' + "job_wait: the open was refused"
# EXCLUDES: a refused stepper that settles, detaches or waits
law job_wait_entry_shut:
  for +i: String
  {FJw.step(FJw.Shut{}, i) == (FJw.Shut{}, SCon{'E', SCon{' ', "job_wait: the open was refused"}}) : FJw.St & String}

# LAW job_wait_entry_answers: in any wait, each host event (spelled from
# the wire's primitives) answers the poll: a passed deadline (no tick of
# budget left after the event) detaches, else the end settles, else the
# call waits with the event's tick spent; a settled or detached wait
# answers its final turn and stays final
# EXCLUDES: a tick or an end read as the other, a settle after a detach,
# a final turn that changes, a tick that spends no budget or the end one
law job_wait_entry_answers:
  for +w: FJw.Wt
  for +e: Maybe<&2, Jb.End>
  {FJw.step(FJw.Open{w}, jw_spell_ev(e)) == jw_step(w, Maybe.is_some(&2, Jb.End, e)) : FJw.St & String}

# LAW job_wait_entry_reads: in any wait, an input the laws' reader reads
# as exactly one event steps as that event
# EXCLUDES: an input read otherwise by the entry than by the wire's
# grammar (a third tag accepted, a tag misread)
law job_wait_entry_reads:
  for +w: FJw.Wt
  for +i: String
  for +ready: Bool
  for got: {jw_read_ev(i) == Some{ready} : Maybe<&2, Bool>}
  {FJw.step(FJw.Open{w}, i) == jw_step(w, ready) : FJw.St & String}

# LAW job_wait_entry_malformed_exact: in any wait, an input that is not
# exactly one event (an unknown tag, a bad number, input left over, no
# input) keeps the wait and answers exactly the error form 'E ' +
# "job_wait: malformed event"
# EXCLUDES: a guessed event, a wait changed by garbage, another error text
law job_wait_entry_malformed_exact:
  for +w: FJw.Wt
  for +i: String
  for no: {jw_read_ev(i) == None{} : Maybe<&2, Bool>}
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
  {[jw_read_open("01,"), jw_read_open("1,x")] == [None{}, None{}] : List<&2, Maybe<&2, Nat>>} &
  {[jw_read_ev("2,"), jw_read_ev("1,1,")] == [None{}, None{}] : List<&2, Maybe<&2, Bool>>} &
  {[LawsBase.wire_fits(1n), Nat.is_lt(jw_ticks([None{}]), 2n), jw_has_end([None{}]), Nat.is_le(1n, jw_ticks([None{}])), String.eq(jw_run(1n, [None{}]), "0,")] == [True{}, True{}, False{}, True{}, False{}] : List<&2, Bool>}
