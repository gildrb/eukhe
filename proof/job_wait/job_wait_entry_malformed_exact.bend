# eukhe: the proof of LAW job_wait_entry_malformed_exact
# The entry reads the event with the wire's own decoder, as the laws'
# reader does; where that reader finds no tick or end, the entry keeps the
# wait and answers its error form.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/wire.bend as Wr
import ../../laws/job_wait.bend as JobWait
import ./base.bend as JWB

def jwx.tag(t: Nat, +w: FJw.Wt, no: {JobWait.jw_read_ev.tag(t) == None{} : Maybe<&2, Bool>}) -> {FJw.step.tag(w, t) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}:
  match t:
    case 0n:
      JWB.jwb.none_some({FJw.step.tag(w, 0n) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}, False{}, Equal.sym(Maybe<&2, Bool>, Some{False{}}, None{}, no))
    case 1n:
      JWB.jwb.none_some({FJw.step.tag(w, 1n) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}, True{}, Equal.sym(Maybe<&2, Bool>, Some{True{}}, None{}, no))
    case 2n+p:
      {==}

def jwx.end(whole: Bool, t: Nat, +w: FJw.Wt, no: {JobWait.jw_read_ev.end(whole, t) == None{} : Maybe<&2, Bool>}) -> {FJw.step.end(whole, w, t) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}:
  match whole:
    case True{}:
      jwx.tag(t, w, no)
    case False{}:
      {==}

def jwx.go(r: Wr.Dec<Nat>, +w: FJw.Wt, no: {JobWait.jw_read_ev.go(r) == None{} : Maybe<&2, Bool>}) -> {FJw.step.go(w, r) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}:
  match r:
    case Wr.Got{t, s}:
      jwx.end(Wr.end(s), t, w, no)
    case Wr.Bad{}:
      {==}

def JobWait.job_wait_entry_malformed_exact(w, i, no):
  jwx.go(Wr.get_nat(i), w, no)
