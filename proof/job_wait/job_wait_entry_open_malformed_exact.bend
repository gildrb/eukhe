# eukhe: the proof of LAW job_wait_entry_open_malformed_exact
# The entry reads the open with the wire's own decoder, as the laws'
# reader does; where that reader finds no whole Nat, the entry opens the
# refused state with its error form.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/wire.bend as Wr
import ../../laws/job_wait.bend as JobWait
import ./base.bend as JWB

def jwob.end(whole: Bool, +x: Nat, no: {JobWait.jw_read_open.end(whole, x) == None{} : Maybe<&2, Nat>}) -> {FJw.open.end(whole, x) == (FJw.Shut{}, SCon{'E', SCon{' ', "job_wait: malformed open"}}) : FJw.St & String}:
  match whole:
    case True{}:
      JWB.jwb.none_some_nat({FJw.open.end(True{}, x) == (FJw.Shut{}, SCon{'E', SCon{' ', "job_wait: malformed open"}}) : FJw.St & String}, x, Equal.sym(Maybe<&2, Nat>, Some{x}, None{}, no))
    case False{}:
      {==}

def jwob.go(r: Wr.Dec<Nat>, no: {JobWait.jw_read_open.go(r) == None{} : Maybe<&2, Nat>}) -> {FJw.open.go(r) == (FJw.Shut{}, SCon{'E', SCon{' ', "job_wait: malformed open"}}) : FJw.St & String}:
  match r:
    case Wr.Got{x, s}:
      jwob.end(Wr.end(s), x, no)
    case Wr.Bad{}:
      {==}

def JobWait.job_wait_entry_open_malformed_exact(i, no):
  jwob.go(Wr.get_nat(i), no)
