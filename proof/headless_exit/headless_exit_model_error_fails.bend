# eukhe: the proof of LAW headless_exit_model_error_fails
#
# PROOF: above the run a failed command or a give-up exits 1 (hx.facts_fail); the run unanswered for ModelError is a run failure, code 1.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_model_error_fails(cf, gu, p, c, a):
  LAHeadlessExit.hx.facts_fail(cf, gu, Hx.Unanswered{Hx.ModelError{}}, p, c, a, {==})
