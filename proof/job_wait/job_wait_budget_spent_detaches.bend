# eukhe: the proof of LAW job_wait_budget_spent_detaches
# The open with a spelled budget is the poll at rest (JWB.jwb.open). By
# induction on the events from a wait with 1+p ticks left: with no end
# among them, the tick that spends the last tick of budget detaches, and
# a detached wait answers its turn forever (JWB.jwb.final).

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/job.bend as M
import ../../bend/wire.bend as Wr
import ../../laws/job_wait.bend as JobWait
import ./base.bend as JWB

def jwe.go(es: List<&2, Maybe<&2, M.End>>, +p: Nat, none: {JobWait.jw_has_end(es) == False{} : Bool}, spent: {Nat.is_le(1n+p, JobWait.jw_ticks(es)) == True{} : Bool}) -> {JobWait.jw_last(es, (FJw.Open{FJw.Waiting{1n+p}}, Wr.put_nat(0n, ""))) == Wr.put_nat(2n, "") : String}:
  match es:
    case Nil{}:
      JWB.jwb.tf({Wr.put_nat(0n, "") == Wr.put_nat(2n, "") : String}, Equal.sym(Bool, False{}, True{}, spent))
    case e <> rest:
      match e:
        case None{}:
          match p:
            case 0n:
              JWB.jwb.final(rest, M.Detaches{})
            case 1n+q:
              jwe.go(rest, q, none, spent)
        case Some{x}:
          JWB.jwb.tf({JobWait.jw_last(rest, (FJw.Open{FJw.Final{M.Settles{}}}, FJw.put_turn(M.Settles{}))) == Wr.put_nat(2n, "") : String}, none)

def jwe.top(+b: Nat, es: List<&2, Maybe<&2, M.End>>, none: {JobWait.jw_has_end(es) == False{} : Bool}, spent: {Nat.is_le(b, JobWait.jw_ticks(es)) == True{} : Bool}) -> {JobWait.jw_last(es, FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{}))) == Wr.put_nat(2n, "") : String}:
  match b:
    case 0n:
      JWB.jwb.final(es, M.Detaches{})
    case 1n+p:
      jwe.go(es, p, none, spent)

def JobWait.job_wait_budget_spent_detaches(b, fits, es, none, spent):
  %Equal.sym(FJw.St & String, FJw.open(Wr.put_nat(b, "")), FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{})), JWB.jwb.open(b, fits)) : {JobWait.jw_last(es, _) == Wr.put_nat(2n, "") : String}
  jwe.top(b, es, none, spent)
