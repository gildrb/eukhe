# eukhe: the proof of LAW job_wait_entry_malformed_exact
# The entry reads its two Bools with the wire's own decoder, as the laws'
# reader does; where that reader finds no whole request, the entry answers
# its error form.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/wire.bend as Wr
import ../../laws/job.bend as Job
import ../base/logic/logic.bend as LLogicLogic

def wm.end(b: Bool, -due: Bool, -ready: Bool, no: {b == False{} : Bool}) -> {FJw.run.end(b, due, ready) == SCon{'E', SCon{' ', "job_wait: malformed request"}} : String}:
  match b:
    case True{}:
      LLogicLogic.pf.absurd_tf({FJw.run.end(True{}, due, ready) == SCon{'E', SCon{' ', "job_wait: malformed request"}} : String}, no)
    case False{}:
      {==}

def wm.ready(-due: Bool, r: Wr.Dec<Bool>, no: {Job.wt_reads.ready(r) == False{} : Bool}) -> {FJw.run.ready(due, r) == SCon{'E', SCon{' ', "job_wait: malformed request"}} : String}:
  match r:
    case Wr.Got{x, s}:
      wm.end(Wr.end(s), due, x, no)
    case Wr.Bad{}:
      {==}

def wm.due(r: Wr.Dec<Bool>, no: {Job.wt_reads.due(r) == False{} : Bool}) -> {FJw.run(r) == SCon{'E', SCon{' ', "job_wait: malformed request"}} : String}:
  match r:
    case Wr.Got{d, s}:
      wm.ready(d, Wr.get_bool(s), no)
    case Wr.Bad{}:
      {==}

def Job.job_wait_entry_malformed_exact(s, no):
  wm.due(Wr.get_bool(s), no)
