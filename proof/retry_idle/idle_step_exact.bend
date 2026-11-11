# eukhe: the proof of LAW idle_step_exact
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ./base.bend as LARetryIdle

def RetryIdle.idle_step_exact(s, e):
  LARetryIdle.ri.step(s, e)
