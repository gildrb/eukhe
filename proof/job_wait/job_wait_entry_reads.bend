# eukhe: the proof of LAW job_wait_entry_reads
# The entry reads the event with the wire's own decoder, as the laws'
# reader does: where that reader reads a tick or the end, the entry steps
# the wait as the laws do (JWB.jwb.step); every other arm contradicts the
# premise.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/wire.bend as Wr
import ../../laws/job_wait.bend as JobWait
import ./base.bend as JWB

def jwr.tag(t: Nat, +w: FJw.Wt, +ready: Bool, got: {JobWait.jw_read_ev.tag(t) == Some{ready} : Maybe<&2, Bool>}) -> {FJw.step.tag(w, t) == JobWait.jw_step(w, ready) : FJw.St & String}:
  match t:
    case 0n:
      %JWB.jwb.some_inj(False{}, ready, got) : {FJw.step.tag(w, 0n) == JobWait.jw_step(w, _) : FJw.St & String}
      JWB.jwb.step(w, False{})
    case 1n:
      %JWB.jwb.some_inj(True{}, ready, got) : {FJw.step.tag(w, 1n) == JobWait.jw_step(w, _) : FJw.St & String}
      JWB.jwb.step(w, True{})
    case 2n+p:
      JWB.jwb.none_some({FJw.step.tag(w, 2n+p) == JobWait.jw_step(w, ready) : FJw.St & String}, ready, got)

def jwr.end(whole: Bool, t: Nat, +w: FJw.Wt, +ready: Bool, got: {JobWait.jw_read_ev.end(whole, t) == Some{ready} : Maybe<&2, Bool>}) -> {FJw.step.end(whole, w, t) == JobWait.jw_step(w, ready) : FJw.St & String}:
  match whole:
    case True{}:
      jwr.tag(t, w, ready, got)
    case False{}:
      JWB.jwb.none_some({FJw.step.end(False{}, w, t) == JobWait.jw_step(w, ready) : FJw.St & String}, ready, got)

def jwr.go(r: Wr.Dec<Nat>, +w: FJw.Wt, +ready: Bool, got: {JobWait.jw_read_ev.go(r) == Some{ready} : Maybe<&2, Bool>}) -> {FJw.step.go(w, r) == JobWait.jw_step(w, ready) : FJw.St & String}:
  match r:
    case Wr.Got{t, s}:
      jwr.end(Wr.end(s), t, w, ready, got)
    case Wr.Bad{}:
      JWB.jwb.none_some({FJw.step.go(w, Wr.Bad{}) == JobWait.jw_step(w, ready) : FJw.St & String}, ready, got)

def JobWait.job_wait_entry_reads(w, i, ready, got):
  jwr.go(Wr.get_nat(i), w, ready, got)
