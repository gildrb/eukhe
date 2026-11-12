# eukhe: the proof of LAW job_wait_refused_open
# An open read whole is the wait after a turn, whose reply is a Nat
# (JWB.jwb.take_ok), against the premise: so the open is the refused
# state with its error form (jwr.go). The refused state answers every
# input with its refusal before reading it (jwr.feed).

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/job.bend as M
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/job_wait.bend as JobWait
import ../base/staging.bend as LStg
import ./base.bend as JWB

def jwr.end(whole: Bool, +b: Nat, bad: {LawsBase.wire_opens_err(JobWait.jw_reply(FJw.open.end(whole, b))) == True{} : Bool}) -> {FJw.open.end(whole, b) == (FJw.Shut{}, SCon{'E', SCon{' ', "job_wait: malformed open"}}) : FJw.St & String}:
  match whole:
    case True{}:
      LStg.stg.absurd({FJw.open.end(True{}, b) == (FJw.Shut{}, SCon{'E', SCon{' ', "job_wait: malformed open"}}) : FJw.St & String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(JobWait.jw_reply(FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{})))), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(JobWait.jw_reply(FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{})))), True{}, bad), JWB.jwb.take_ok(b, M.poll(Nat.is_eq(b, 0n), False{}))))
    case False{}:
      {==}

def jwr.go(d: Wr.Dec<Nat>, bad: {LawsBase.wire_opens_err(JobWait.jw_reply(FJw.open.go(d))) == True{} : Bool}) -> {FJw.open.go(d) == (FJw.Shut{}, SCon{'E', SCon{' ', "job_wait: malformed open"}}) : FJw.St & String}:
  match d:
    case Wr.Got{+b, +s}:
      jwr.end(Wr.end(s), b, bad)
    case Wr.Bad{}:
      {==}

# the refused state answers x, then one refusal per input
def jwr.feed(ins: List<&2, String>, +x: String) -> {JobWait.jw_feed_raw(ins, (FJw.Shut{}, x)) == x <> JobWait.jw_refusals(ins) : List<&2, String>}:
  match ins:
    case Nil{}:
      {==}
    case i <> t:
      Equal.cong(List<&2, String>, List<&2, String>, z => x <> z, JobWait.jw_feed_raw(t, (FJw.Shut{}, SCon{'E', SCon{' ', "job_wait: the open was refused"}})), SCon{'E', SCon{' ', "job_wait: the open was refused"}} <> JobWait.jw_refusals(t), jwr.feed(t, SCon{'E', SCon{' ', "job_wait: the open was refused"}}))

def JobWait.job_wait_refused_open(i, bad, ins):
  %Equal.sym(FJw.St & String, FJw.open.go(Wr.get_nat(i)), (FJw.Shut{}, SCon{'E', SCon{' ', "job_wait: malformed open"}}), jwr.go(Wr.get_nat(i), bad)) : {JobWait.jw_feed_raw(ins, _) == SCon{'E', SCon{' ', "job_wait: malformed open"}} <> JobWait.jw_refusals(ins) : List<&2, String>}
  jwr.feed(ins, SCon{'E', SCon{' ', "job_wait: malformed open"}})
