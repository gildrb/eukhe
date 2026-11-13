# eukhe: the proof of LAW headless_exit_unfailed_run_neutral
#
# PROOF: case analysis on the command and the wait: above the run both sides are the same cause; below it an answered, reset, stale or withdrawn run reads the transcript as no run does.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit

def HeadlessExit.headless_exit_unfailed_run_neutral(cf, w, p, c, a, ba):
  match cf:
    case True{}:
      {==}
    case False{}:
      match w:
        case Hx.Quiet{}:
          {==}
        case Hx.GaveUp{}:
          {==}
        case Hx.BudgetDeadline{}:
          match ba:
            case True{}:
              {==}
            case False{}:
              {==}
