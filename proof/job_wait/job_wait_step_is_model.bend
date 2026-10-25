# eukhe: the proof of LAW job_wait_step_is_model
# The open with a spelled budget is the poll at rest (JWB.jwb.open). By
# induction on the events from a wait with 1+p ticks left: a tick with one
# tick left detaches, and the model with no budget left detaches whatever
# comes (JWB.jwb.zero); a tick with more left waits on, as the model does;
# the end settles, as the model does with an exit or the kill; a final
# wait answers its turn forever (JWB.jwb.final).

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/job.bend as M
import ../../bend/wire.bend as Wr
import ../../laws/job_wait.bend as JobWait
import ./base.bend as JWB

# a detached wait answers what the model answers with no budget left
def jwm.detached(+es: List<&2, Maybe<&2, M.End>>) -> {JobWait.jw_last(es, (FJw.Open{FJw.Final{M.Detaches{}}}, FJw.put_turn(M.Detaches{}))) == JobWait.jw_spell_wait(M.wait(JobWait.jw_jevs(es), 0n)) : String}:
  %Equal.sym(Maybe<&2, M.Wait>, M.wait(JobWait.jw_jevs(es), 0n), Some{M.Detached{}}, JWB.jwb.zero(JobWait.jw_jevs(es))) : {JobWait.jw_last(es, (FJw.Open{FJw.Final{M.Detaches{}}}, FJw.put_turn(M.Detaches{}))) == JobWait.jw_spell_wait(_) : String}
  JWB.jwb.final(es, M.Detaches{})

# from a wait with 1+p ticks left, the replies are the model's
def jwm.go(es: List<&2, Maybe<&2, M.End>>, +p: Nat) -> {JobWait.jw_last(es, (FJw.Open{FJw.Waiting{1n+p}}, Wr.put_nat(0n, ""))) == JobWait.jw_spell_wait(M.wait(JobWait.jw_jevs(es), 1n+p)) : String}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case None{}:
          match p:
            case 0n:
              jwm.detached(rest)
            case 1n+q:
              jwm.go(rest, q)
        case Some{x}:
          match x:
            case M.Exited{c}:
              JWB.jwb.final(rest, M.Settles{})
            case M.Killed{}:
              JWB.jwb.final(rest, M.Settles{})

def jwm.top(+b: Nat, es: List<&2, Maybe<&2, M.End>>) -> {JobWait.jw_last(es, FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{}))) == JobWait.jw_spell_wait(M.wait(JobWait.jw_jevs(es), b)) : String}:
  match b:
    case 0n:
      jwm.detached(es)
    case 1n+p:
      jwm.go(es, p)

def JobWait.job_wait_step_is_model(b, fits, es):
  %Equal.sym(FJw.St & String, FJw.open(Wr.put_nat(b, "")), FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{})), JWB.jwb.open(b, fits)) : {JobWait.jw_last(es, _) == JobWait.jw_spell_wait(M.wait(JobWait.jw_jevs(es), b)) : String}
  jwm.top(b, es)
