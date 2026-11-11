# eukhe: the proof of LAW idle_wake_stalls_past_deadline
# d is never above d + x, so the free clock's selector stalls.
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

# d is never above d + x
def wsp.ngt(d: Nat, x: Nat) -> {Nat.is_gt(d, Nat.add(d, x)) == False{} : Bool}:
  match d:
    case 0n:
      LA.ri.gt_zero(x)
    case 1n+p:
      wsp.ngt(p, x)

def RetryIdle.idle_wake_stalls_past_deadline(d, x):
  %Equal.sym(Bool, Nat.is_gt(d, Nat.add(d, x)), False{}, wsp.ngt(d, x)) : {R.idle.wake.sel(_, Nat.sub(d, Nat.add(d, x))) == R.WakeStall{} : R.Wake}
  {==}
