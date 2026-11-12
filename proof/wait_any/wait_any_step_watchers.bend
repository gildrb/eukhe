# eukhe: the proof of LAW wait_any_step_watchers
#
# PROOF: by the wake path, the watchers (none, or some) and the phase:
# every step then computes.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny

def WaitAny.wait_any_step_watchers(wake, w, p):
  match wake:
    case True{}:
      match w:
        case 0n:
          match p:
            case Wa.Live{}:
              {==}
            case Wa.Kept{}:
              {==}
            case Wa.Sent{}:
              {==}
        case 1n+q:
          match p:
            case Wa.Live{}:
              {==}
            case Wa.Kept{}:
              {==}
            case Wa.Sent{}:
              {==}
    case False{}:
      match w:
        case 0n:
          match p:
            case Wa.Live{}:
              {==}
            case Wa.Kept{}:
              {==}
            case Wa.Sent{}:
              {==}
        case 1n+q:
          match p:
            case Wa.Live{}:
              {==}
            case Wa.Kept{}:
              {==}
            case Wa.Sent{}:
              {==}
