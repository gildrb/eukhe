# eukhe: the proof of LAW headless_exit_autonomous_failed_fails
#
# PROOF: above the flags every cause has code 1 (hx.facts_fail, hx.run_fails); with no earlier failure a failed compaction or the failed autonomous turn is the cause (hx.auto_fails), code 1.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

# whatever the terminal entry and the compaction, a failed autonomous turn
# leaves code 1
def hx.auto_fails(p: Hx.Primary, c: Bool) -> {Hx.code(Hx.by_primary(p, c, True{})) == 1n : Nat}:
  match p:
    case Hx.PNothing{}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}
    case Hx.PAnswer{}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}
    case Hx.PUnfinished{}:
      {==}
    case Hx.PProviderError{}:
      {==}
    case Hx.PAborted{}:
      {==}
    case Hx.PSlashOk{}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}
    case Hx.PSlashFailed{}:
      {==}

def HeadlessExit.headless_exit_autonomous_failed_fails(cf, gu, r, p, c):
  LAHeadlessExit.hx.facts_fail(cf, gu, r, p, c, True{}, LAHeadlessExit.hx.run_fails(r, p, c, True{}, hx.auto_fails(p, c)))
