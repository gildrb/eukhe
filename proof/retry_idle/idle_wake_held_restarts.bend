# eukhe: the proof of LAW idle_wake_held_restarts
# Both sides compute to a sleep of 1 + u: 1 + u is above 0.
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

def RetryIdle.idle_wake_held_restarts(since, u):
  {==}
