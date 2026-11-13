# eukhe: the proof of LAW headless_exit_forced_tool_fails
#
# PROOF: above the run a failed command, a give-up or the wait at the budget's deadline without the final answer exits 1 (hx.facts_fail); the run unanswered for ForcedTool is a run failure, code 1.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_forced_tool_fails(cf, w, p, c, a, ba):
  LAHeadlessExit.hx.facts_fail(cf, w, Hx.Unanswered{Hx.ForcedTool{}}, p, c, a, ba, {==})
