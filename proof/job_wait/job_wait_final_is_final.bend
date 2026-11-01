# eukhe: the proof of LAW job_wait_final_is_final
# The open with a spelled budget is the poll at rest (JWB.jwb.open). By
# induction on the events from a wait with 1+p ticks left: a run that
# still waits after all of es contradicts the premise; once a tick
# detaches or the end settles, the wait is final, and a final wait
# answers its turn to every event (JWB.jwb.final), so the events after it
# change nothing.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/job.bend as M
import ../../bend/wire.bend as Wr
import ../../laws/job_wait.bend as JobWait
import ./base.bend as JWB

# a final wait answers the same before and after more events
def jwf.both(+es: List<&2, Maybe<&2, M.End>>, more: List<&2, Maybe<&2, M.End>>, +t: M.Turn) -> {JobWait.jw_last(List.append(&2, Maybe<&2, M.End>, es, more), (FJw.Open{FJw.Final{t}}, FJw.put_turn(t))) == JobWait.jw_last(es, (FJw.Open{FJw.Final{t}}, FJw.put_turn(t))) : String}:
  Equal.trans(String, JobWait.jw_last(List.append(&2, Maybe<&2, M.End>, es, more), (FJw.Open{FJw.Final{t}}, FJw.put_turn(t))), FJw.put_turn(t), JobWait.jw_last(es, (FJw.Open{FJw.Final{t}}, FJw.put_turn(t))), JWB.jwb.final(List.append(&2, Maybe<&2, M.End>, es, more), t), Equal.sym(String, JobWait.jw_last(es, (FJw.Open{FJw.Final{t}}, FJw.put_turn(t))), FJw.put_turn(t), JWB.jwb.final(es, t)))

def jwf.go(es: List<&2, Maybe<&2, M.End>>, more: List<&2, Maybe<&2, M.End>>, +p: Nat, done: {String.eq(JobWait.jw_last(es, (FJw.Open{FJw.Waiting{1n+p}}, Wr.put_nat(0n, ""))), Wr.put_nat(0n, "")) == False{} : Bool}) -> {JobWait.jw_last(List.append(&2, Maybe<&2, M.End>, es, more), (FJw.Open{FJw.Waiting{1n+p}}, Wr.put_nat(0n, ""))) == JobWait.jw_last(es, (FJw.Open{FJw.Waiting{1n+p}}, Wr.put_nat(0n, ""))) : String}:
  match es:
    case Nil{}:
      JWB.jwb.tf({JobWait.jw_last(more, (FJw.Open{FJw.Waiting{1n+p}}, Wr.put_nat(0n, ""))) == Wr.put_nat(0n, "") : String}, done)
    case e <> rest:
      match e:
        case None{}:
          match p:
            case 0n:
              jwf.both(rest, more, M.Detaches{})
            case 1n+q:
              jwf.go(rest, more, q, done)
        case Some{x}:
          jwf.both(rest, more, M.Settles{})

def jwf.top(+b: Nat, es: List<&2, Maybe<&2, M.End>>, more: List<&2, Maybe<&2, M.End>>, done: {String.eq(JobWait.jw_last(es, FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{}))), Wr.put_nat(0n, "")) == False{} : Bool}) -> {JobWait.jw_last(List.append(&2, Maybe<&2, M.End>, es, more), FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{}))) == JobWait.jw_last(es, FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{}))) : String}:
  match b:
    case 0n:
      jwf.both(es, more, M.Detaches{})
    case 1n+p:
      jwf.go(es, more, p, done)

def JobWait.job_wait_final_is_final(b, fits, es, more, done):
  +eq = JWB.jwb.open(b, fits)
  +done2 = Equal.trans(Bool, String.eq(JobWait.jw_last(es, FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{}))), Wr.put_nat(0n, "")), String.eq(JobWait.jw_last(es, FJw.open(Wr.put_nat(b, ""))), Wr.put_nat(0n, "")), False{}, Equal.cong(FJw.St & String, Bool, r => String.eq(JobWait.jw_last(es, r), Wr.put_nat(0n, "")), FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{})), FJw.open(Wr.put_nat(b, "")), Equal.sym(FJw.St & String, FJw.open(Wr.put_nat(b, "")), FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{})), eq)), done)
  %Equal.sym(FJw.St & String, FJw.open(Wr.put_nat(b, "")), FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{})), eq) : {JobWait.jw_last(List.append(&2, Maybe<&2, M.End>, es, more), _) == JobWait.jw_last(es, _) : String}
  jwf.top(b, es, more, done2)
