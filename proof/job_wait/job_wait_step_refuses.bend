# eukhe: the proof of LAW job_wait_step_refuses
# A tick or the end answers the wait's turn, a Nat (JWB.jwb.wait_ok),
# against the premise; every other read keeps the wait and answers the
# malformed-event error form.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/job.bend as M
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/job_wait.bend as JobWait
import ../base/staging.bend as LStg
import ./base.bend as JWB

def jwf.tag(+w: FJw.Wt, t: Nat, bad: {LawsBase.wire_opens_err(JobWait.jw_reply(FJw.step.tag(w, t))) == True{} : Bool}) -> {FJw.step.tag(w, t) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}:
  match t:
    case 0n:
      LStg.stg.absurd({FJw.step.tag(w, 0n) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(JobWait.jw_reply(FJw.step.wait(w, False{}))), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(JobWait.jw_reply(FJw.step.wait(w, False{}))), True{}, bad), JWB.jwb.wait_ok(w, False{})))
    case 1n:
      LStg.stg.absurd({FJw.step.tag(w, 1n) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(JobWait.jw_reply(FJw.step.wait(w, True{}))), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(JobWait.jw_reply(FJw.step.wait(w, True{}))), True{}, bad), JWB.jwb.wait_ok(w, True{})))
    case 2n+p:
      {==}

def jwf.end(whole: Bool, +w: FJw.Wt, +t: Nat, bad: {LawsBase.wire_opens_err(JobWait.jw_reply(FJw.step.end(whole, w, t))) == True{} : Bool}) -> {FJw.step.end(whole, w, t) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}:
  match whole:
    case True{}:
      jwf.tag(w, t, bad)
    case False{}:
      {==}

def jwf.go(+w: FJw.Wt, d: Wr.Dec<Nat>, bad: {LawsBase.wire_opens_err(JobWait.jw_reply(FJw.step.go(w, d))) == True{} : Bool}) -> {FJw.step.go(w, d) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}:
  match d:
    case Wr.Got{+t, +s}:
      jwf.end(Wr.end(s), w, t, bad)
    case Wr.Bad{}:
      {==}

def JobWait.job_wait_step_refuses(w, i, bad):
  jwf.go(w, Wr.get_nat(i), bad)
