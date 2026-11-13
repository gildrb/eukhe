# eukhe: the proof of LAW headless_exit_compaction_failed_fails
#
# PROOF: above the flags every cause has code 1 (hx.facts_fail, hx.run_fails); with no earlier failure the failed compaction is the cause (hx.comp_fails), code 1.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_compaction_failed_fails(cf, w, r, p, a, ba):
  LAHeadlessExit.hx.facts_fail(cf, w, r, p, True{}, a, ba, LAHeadlessExit.hx.run_fails(r, p, True{}, a, ba, LAHeadlessExit.hx.comp_fails(p, a, ba)))
