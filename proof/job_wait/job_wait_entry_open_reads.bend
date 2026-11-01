# eukhe: the proof of LAW job_wait_entry_open_reads
# The entry reads the open with the wire's own decoder, as the laws'
# reader does: where that reader reads one Nat b, the entry opens with b
# (JWB.jwb.take_poll); every other arm contradicts the premise.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/job.bend as M
import ../../bend/wire.bend as Wr
import ../../laws/job.bend as Job
import ../../laws/job_wait.bend as JobWait
import ./base.bend as JWB

def jwo.end(whole: Bool, +x: Nat, +b: Nat, got: {JobWait.jw_read_open.end(whole, x) == Some{b} : Maybe<&2, Nat>}) -> {FJw.open.end(whole, x) == JobWait.jw_after(b, Job.wt_poll_spec(Nat.is_eq(b, 0n), False{})) : FJw.St & String}:
  match whole:
    case True{}:
      %JWB.jwb.some_inj_nat(x, b, got) : {FJw.open.end(True{}, x) == JobWait.jw_after(_, Job.wt_poll_spec(Nat.is_eq(_, 0n), False{})) : FJw.St & String}
      JWB.jwb.take_poll(x, Nat.is_eq(x, 0n), False{})
    case False{}:
      JWB.jwb.none_some_nat({FJw.open.end(False{}, x) == JobWait.jw_after(b, Job.wt_poll_spec(Nat.is_eq(b, 0n), False{})) : FJw.St & String}, b, got)

def jwo.go(r: Wr.Dec<Nat>, +b: Nat, got: {JobWait.jw_read_open.go(r) == Some{b} : Maybe<&2, Nat>}) -> {FJw.open.go(r) == JobWait.jw_after(b, Job.wt_poll_spec(Nat.is_eq(b, 0n), False{})) : FJw.St & String}:
  match r:
    case Wr.Got{x, s}:
      jwo.end(Wr.end(s), x, b, got)
    case Wr.Bad{}:
      JWB.jwb.none_some_nat({FJw.open.go(Wr.Bad{}) == JobWait.jw_after(b, Job.wt_poll_spec(Nat.is_eq(b, 0n), False{})) : FJw.St & String}, b, got)

def JobWait.job_wait_entry_open_reads(i, b, got):
  jwo.go(Wr.get_nat(i), b, got)
