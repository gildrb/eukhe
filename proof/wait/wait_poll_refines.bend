# eukhe: the proof of LAW wait_poll_refines
# Eight polls: each computes.

import Base
import ../../bend/wait.bend as Wt
import ../../laws/wait.bend as WaitLaws

def WaitLaws.wait_poll_refines(r):
  match r:
    case Wt.Polled{w, c, l}:
      match w c l:
        case True{} True{} True{}:
          {==}
        case True{} True{} False{}:
          {==}
        case True{} False{} True{}:
          {==}
        case True{} False{} False{}:
          {==}
        case False{} True{} True{}:
          {==}
        case False{} True{} False{}:
          {==}
        case False{} False{} True{}:
          {==}
        case False{} False{} False{}:
          {==}
