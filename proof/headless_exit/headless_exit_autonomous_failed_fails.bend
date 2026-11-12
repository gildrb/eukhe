# eukhe: the proof of LAW headless_exit_autonomous_failed_fails
#
# PROOF: above the flags every cause has code 1 (hx.facts_fail, hx.run_fails); with no earlier failure a failed compaction or the failed autonomous turn is the cause (hx.auto_fails), code 1.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

# below the transcript, a failed autonomous turn leaves code 1
def hx.auto_flags(c: Bool, -ba: Bool) -> {Hx.code(Hx.by_flags(c, True{}, ba)) == 1n : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# whatever the terminal entry and the compaction, a failed autonomous turn
# leaves code 1
def hx.auto_fails(p: Hx.Primary, +c: Bool, +ba: Bool) -> {Hx.code(Hx.by_primary(p, c, True{}, ba)) == 1n : Nat}:
  match p:
    case Hx.PNothing{}:
      hx.auto_flags(c, ba)
    case Hx.PAnswer{}:
      hx.auto_flags(c, ba)
    case Hx.PUnfinished{}:
      {==}
    case Hx.PProviderError{}:
      {==}
    case Hx.PAborted{}:
      {==}
    case Hx.PSlashOk{}:
      hx.auto_flags(c, ba)
    case Hx.PSlashFailed{}:
      {==}
    case Hx.PBudgetRefused{}:
      match ba:
        case True{}:
          hx.auto_flags(c, True{})
        case False{}:
          {==}

def HeadlessExit.headless_exit_autonomous_failed_fails(cf, w, r, p, c, ba):
  LAHeadlessExit.hx.facts_fail(cf, w, r, p, c, True{}, ba, LAHeadlessExit.hx.run_fails(r, p, c, True{}, ba, hx.auto_fails(p, c, ba)))
