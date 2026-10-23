# eukhe: the proof of LAW run_deferred_reply_is_the_job_model

import Base
import ../../bend/retry.bend as R
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run
import ./base.bend as LA

def rk.run_deferred_reply_is_the_job_model(+l: RnDecision.Lim, +t: RnDecision.At, +fails: Nat, +budget: Nat, +failed: Nat, +gap: Nat) -> {Run.rust.later(RnDecision.decide.reply(l, t, RnState.Deferred{})) == R.Step.act(R.step(fails, budget, R.Live{failed, RnDecision.At.p(l, t)}, R.Later{gap})) : R.Act}:
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case RnDecision.At{+attempt, +notes, +waited, +compacted}:
          +cfg = {RnState.Cfg{rounds, wait, retries, most} : RnState.Cfg}
          +c = RnDecision.c.of(compacted)
          +a = Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes))
          +n = Nat.sub(most, notes)
          +ph = RnDecision.Then.ph(False{}, RnState.St.ph(RnStep.call(cfg, RnState.Deferred{}, 0n, c, a, n, Nat.sub(wait, waited))))
          %Equal.sym(RnDecision.Then, ph, Run.rust.wait(Nat.is_lt(waited, wait)), LA.rk.wait(cfg, 0n, c, a, n, wait, waited)) : {Run.rust.later(_) == R.Step.act(R.step(fails, budget, R.Live{failed, Nat.sub(wait, waited)}, R.Later{gap})) : R.Act}
          %LA.rk.eq0(wait, waited) : {Run.rust.later(Run.rust.wait(Nat.is_lt(waited, wait))) == R.Step.act(R.live.pending(_, Nat.sub(wait, waited), gap)) : R.Act}
          LA.rk.later(Nat.is_lt(waited, wait), Nat.sub(wait, waited), gap)

def Run.run_deferred_reply_is_the_job_model(l, t, fails, budget, failed, gap):
  rk.run_deferred_reply_is_the_job_model(l, t, fails, budget, failed, gap)
