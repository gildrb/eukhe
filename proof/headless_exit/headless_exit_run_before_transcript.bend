# eukhe: the proof of LAW headless_exit_run_before_transcript
#
# PROOF: case analysis on the reason: a failing reason is the cause with itself; a reset, stale, withdrawn or budget-refused run contradicts the premise.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ../base/logic/logic.bend as LLogicLogic

def HeadlessExit.headless_exit_run_before_transcript(r, p, c, a, ba, fails):
  match r:
    case Hx.ModelError{}:
      {==}
    case Hx.RunLimit{}:
      {==}
    case Hx.NoModel{}:
      {==}
    case Hx.ForcedTool{}:
      {==}
    case Hx.Faulted{}:
      {==}
    case Hx.Aborted{}:
      {==}
    case Hx.Reset{}:
      LLogicLogic.absurd({HeadlessExit.cause_of(Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, Hx.Unanswered{Hx.Reset{}}, p, c, a, ba})) == Hx.CRunFailed{Hx.Reset{}} : Hx.Cause}, fails)
    case Hx.Stale{}:
      LLogicLogic.absurd({HeadlessExit.cause_of(Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, Hx.Unanswered{Hx.Stale{}}, p, c, a, ba})) == Hx.CRunFailed{Hx.Stale{}} : Hx.Cause}, fails)
    case Hx.Withdrawn{}:
      LLogicLogic.absurd({HeadlessExit.cause_of(Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, Hx.Unanswered{Hx.Withdrawn{}}, p, c, a, ba})) == Hx.CRunFailed{Hx.Withdrawn{}} : Hx.Cause}, fails)
    case Hx.Other{}:
      {==}
    case Hx.BudgetRefused{}:
      LLogicLogic.absurd({HeadlessExit.cause_of(Hx.decide(Hx.Facts{False{}, Hx.Quiet{}, Hx.Unanswered{Hx.BudgetRefused{}}, p, c, a, ba})) == Hx.CRunFailed{Hx.BudgetRefused{}} : Hx.Cause}, fails)
