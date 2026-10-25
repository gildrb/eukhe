# eukhe: the proof of LAW job_wait_end_in_time_settles
# The open with a spelled budget is the poll at rest (JWB.jwb.open). By
# induction on the events from a wait with 1+p ticks left: fewer ticks
# than the budget never detach, an earlier end already settled (a final
# wait answers its turn forever: JWB.jwb.final), and the end then settles.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/job.bend as M
import ../../bend/wire.bend as Wr
import ../../laws/job_wait.bend as JobWait
import ./base.bend as JWB

def jwd.go(es: List<&2, Maybe<&2, M.End>>, +p: Nat, +x: M.End, early: {Nat.is_lt(JobWait.jw_ticks(es), 1n+p) == True{} : Bool}) -> {JobWait.jw_last(List.append(&2, Maybe<&2, M.End>, es, [Some{x}]), (FJw.Open{FJw.Waiting{1n+p}}, Wr.put_nat(0n, ""))) == Wr.put_nat(1n, "") : String}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case None{}:
          match p:
            case 0n:
              JWB.jwb.tf({JobWait.jw_last(List.append(&2, Maybe<&2, M.End>, rest, [Some{x}]), (FJw.Open{FJw.Final{M.Detaches{}}}, FJw.put_turn(M.Detaches{}))) == Wr.put_nat(1n, "") : String}, Equal.trans(Bool, True{}, Nat.is_lt(JobWait.jw_ticks(rest), 0n), False{}, Equal.sym(Bool, Nat.is_lt(JobWait.jw_ticks(rest), 0n), True{}, early), JWB.jwb.lt_zero(JobWait.jw_ticks(rest))))
            case 1n+q:
              jwd.go(rest, q, x, early)
        case Some{y}:
          JWB.jwb.final(List.append(&2, Maybe<&2, M.End>, rest, [Some{x}]), M.Settles{})

def jwd.top(+b: Nat, es: List<&2, Maybe<&2, M.End>>, +x: M.End, early: {Nat.is_lt(JobWait.jw_ticks(es), b) == True{} : Bool}) -> {JobWait.jw_last(List.append(&2, Maybe<&2, M.End>, es, [Some{x}]), FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{}))) == Wr.put_nat(1n, "") : String}:
  match b:
    case 0n:
      JWB.jwb.tf({JobWait.jw_last(List.append(&2, Maybe<&2, M.End>, es, [Some{x}]), (FJw.Open{FJw.Final{M.Detaches{}}}, FJw.put_turn(M.Detaches{}))) == Wr.put_nat(1n, "") : String}, Equal.trans(Bool, True{}, Nat.is_lt(JobWait.jw_ticks(es), 0n), False{}, Equal.sym(Bool, Nat.is_lt(JobWait.jw_ticks(es), 0n), True{}, early), JWB.jwb.lt_zero(JobWait.jw_ticks(es))))
    case 1n+p:
      jwd.go(es, p, x, early)

def JobWait.job_wait_end_in_time_settles(b, fits, es, x, early):
  %Equal.sym(FJw.St & String, FJw.open(Wr.put_nat(b, "")), FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{})), JWB.jwb.open(b, fits)) : {JobWait.jw_last(List.append(&2, Maybe<&2, M.End>, es, [Some{x}]), _) == Wr.put_nat(1n, "") : String}
  jwd.top(b, es, x, early)
