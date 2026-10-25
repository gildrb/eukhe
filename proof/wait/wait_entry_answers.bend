# eukhe: the proof of LAW wait_entry_answers
# Eight polls, each a closed string: each computes.

import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait.bend as FWt
import ../../laws/wait.bend as WaitLaws

def WaitLaws.wait_entry_answers(r):
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
