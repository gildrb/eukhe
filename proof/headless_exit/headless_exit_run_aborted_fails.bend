# eukhe: the proof of LAW headless_exit_run_aborted_fails
#
# PROOF: above the run a failed command, a give-up or the wait at the budget's deadline without the final answer exits 1 (hx.facts_fail); the run unanswered for Aborted is a run failure, code 1.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_run_aborted_fails(cf, w, p, c, a, ba):
  LAHeadlessExit.hx.facts_fail(cf, w, Hx.Unanswered{Hx.Aborted{}}, p, c, a, ba, {==})
