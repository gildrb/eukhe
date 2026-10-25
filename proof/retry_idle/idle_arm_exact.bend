# eukhe: the proof of LAW idle_arm_exact
# Each case of NaN, the sign and the whole part computes.

import Base
import ../../laws/retry_idle.bend as RetryIdle

def RetryIdle.idle_arm_exact(nan, neg, whole, frac):
  match nan:
    case True{}:
      {==}
    case False{}:
      match neg:
        case True{}:
          {==}
        case False{}:
          match whole:
            case 0n:
              {==}
            case 1n+p:
              {==}
