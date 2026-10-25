# eukhe: the proof of LAW retry_length_exact
# By induction on the providers tried.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry_ffi.bend as RetryFfi

def rl.len(ts: List<&2, R.Tried>) -> {R.length(ts) == List.length(&2, R.Tried, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case t <> rest:
      %rl.len(rest) : {1n+R.length(rest) == 1n+_ : Nat}
      {==}

def RetryFfi.retry_length_exact(ts):
  rl.len(ts)
