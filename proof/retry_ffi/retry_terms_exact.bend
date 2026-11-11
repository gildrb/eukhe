# eukhe: the proof of LAW retry_terms_exact
# Each accessor on each constructor computes.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry_ffi.bend as RetryFfi

def RetryFfi.retry_terms_exact(p, t, j, s, y, i):
  match p t j s y:
    case R.Policy{ps, pb, pm} R.Tried{ta, tw} R.NoJob{} R.Step{sa, sj} R.Tally{ys, yl}:
      match i:
        case R.IdleStall{a}:
          ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))))
        case R.IdleClose{a}:
          ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))))
    case R.Policy{ps, pb, pm} R.Tried{ta, tw} R.Live{f, l} R.Step{sa, sj} R.Tally{ys, yl}:
      match i:
        case R.IdleStall{a}:
          ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))))
        case R.IdleClose{a}:
          ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))))
