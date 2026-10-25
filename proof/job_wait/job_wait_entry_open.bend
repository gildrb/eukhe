# eukhe: the proof of LAW job_wait_entry_open
# The spelled budget reads back (JWB.jwb.open); the entry's wait after the
# model's poll is the laws' (JWB.jwb.take_poll).

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/job.bend as M
import ../../bend/wire.bend as Wr
import ../../laws/job.bend as Job
import ../../laws/job_wait.bend as JobWait
import ./base.bend as JWB

def JobWait.job_wait_entry_open(b, fits):
  Equal.trans(FJw.St & String, FJw.open(Wr.put_nat(b, "")), FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{})), JobWait.jw_after(b, Job.wt_poll_spec(Nat.is_eq(b, 0n), False{})), JWB.jwb.open(b, fits), JWB.jwb.take_poll(b, Nat.is_eq(b, 0n), False{}))
