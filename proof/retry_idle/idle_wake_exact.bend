# eukhe: the proof of LAW idle_wake_exact
# d above since is since below d; the two selectors pick alike.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry_idle.bend as RetryIdle

def iwe.flip(a: Nat, b: Nat) -> {Nat.is_lt(a, b) == Nat.is_gt(b, a) : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match b:
        case 0n:
          {==}
        case 1n+q:
          iwe.flip(p, q)

def iwe.sel(b: Bool, left: Nat) -> {R.idle.wake.sel(b, left) == RetryIdle.wake_spec.free(b, left) : R.Wake}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def RetryIdle.idle_wake_exact(held, since, d):
  match held:
    case True{}:
      {==}
    case False{}:
      +s = since
      +e = d
      %iwe.flip(s, e) : {R.idle.wake.sel(_, Nat.sub(e, s)) == RetryIdle.wake_spec.free(Nat.is_lt(s, e), Nat.sub(e, s)) : R.Wake}
      iwe.sel(Nat.is_lt(s, e), Nat.sub(e, s))
