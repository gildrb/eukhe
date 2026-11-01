# eukhe: the proof of LAW headless_exit_compaction_failed_fails
#
# PROOF: above the flags every cause has code 1 (hx.facts_fail, hx.run_fails); with no earlier failure the failed compaction is the cause (hx.comp_fails), code 1.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

# whatever the terminal entry, a failed compaction leaves code 1
def hx.comp_fails(p: Hx.Primary, -a: Bool) -> {Hx.code(Hx.by_primary(p, True{}, a)) == 1n : Nat}:
  match p:
    case Hx.PNothing{}:
      {==}
    case Hx.PAnswer{}:
      {==}
    case Hx.PUnfinished{}:
      {==}
    case Hx.PProviderError{}:
      {==}
    case Hx.PAborted{}:
      {==}
    case Hx.PSlashOk{}:
      {==}
    case Hx.PSlashFailed{}:
      {==}

def HeadlessExit.headless_exit_compaction_failed_fails(cf, gu, r, p, a):
  LAHeadlessExit.hx.facts_fail(cf, gu, r, p, True{}, a, LAHeadlessExit.hx.run_fails(r, p, True{}, a, hx.comp_fails(p, a)))
