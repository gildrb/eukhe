# eukhe: the proof of LAW idle_open_exact
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ./base.bend as LARetryIdle

def RetryIdle.idle_open_exact(d):
  LARetryIdle.ri.step(R.IdleSt{d, 0n, 0n, False{}}, R.IdleFire{0n})
