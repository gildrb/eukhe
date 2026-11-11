# eukhe: the proof of LAW idle_wake_rearms_at_deadline
# since + 1 + u is above since, and since + 1 + u - since is 1 + u (both by
# induction on since).
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

def wra.gt(since: Nat, -u: Nat) -> {Nat.is_gt(Nat.add(since, 1n+u), since) == True{} : Bool}:
  match since:
    case 0n:
      {==}
    case 1n+p:
      wra.gt(p, u)

def wra.sub(since: Nat, -u: Nat) -> {Nat.sub(Nat.add(since, 1n+u), since) == 1n+u : Nat}:
  match since:
    case 0n:
      {==}
    case 1n+p:
      wra.sub(p, u)

def RetryIdle.idle_wake_rearms_at_deadline(since, u):
  %Equal.sym(Bool, Nat.is_gt(Nat.add(since, 1n+u), since), True{}, wra.gt(since, u)) : {R.idle.wake.sel(_, Nat.sub(Nat.add(since, 1n+u), since)) == R.WakeSleep{1n+u} : R.Wake}
  %Equal.sym(Nat, Nat.sub(Nat.add(since, 1n+u), since), 1n+u, wra.sub(since, u)) : {R.idle.wake.sel(True{}, _) == R.WakeSleep{1n+u} : R.Wake}
  {==}
