# eukhe: the proof of LAW wait_run_exact
# The run is the walk from the deadline (proof/wait/wait_go_exact.bend).

import Base
import ../../bend/wait.bend as Wt
import ../../laws/wait.bend as WaitLaws
import ./wait_go_exact.bend as WG

def WaitLaws.wait_run_exact(dl, xs):
  match dl:
    case None{}:
      WG.wg.open(xs, None{})
    case Some{d}:
      match d:
        case 0n:
          {==}
        case 1n+m:
          WG.wg.open(xs, Some{m})
