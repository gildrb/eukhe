# eukhe: the proof of LAW run_failed_poll_is_the_job_model

import Base
import ../../bend/retry.bend as R
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run
import ./base.bend as LA

def rk.gt(+w: Nat, +x: Nat) -> {Nat.is_lt(x, w) == Nat.is_gt(Nat.sub(w, x), 0n) : Bool}:
  match w x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+v 0n:
      {==}
    case 1n+v 1n+y:
      rk.gt(v, y)

def rk.job(+retryable: Bool, +b1: Bool, +b2: Bool, +failed: Nat, +left: Nat, +gap: Nat) -> {Run.rust.job(Bool.and(retryable, b1), Run.rust.wait(b2)) == R.Step.act(R.live.failed(Bool.and(retryable, Bool.and(b1, b2)), failed, left, gap)) : R.Act}:
  match retryable b1 b2:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} b2:
      {==}
    case False{} b1 b2:
      {==}

def rk.run_failed_poll_is_the_job_model(+l: RnDecision.Lim, +t: RnDecision.At, +retryable: Bool, +failed: Nat, +budget: Nat, +gap: Nat) -> {Run.rust.job(RnDecision.decide.poll(retryable, failed, RnDecision.Lim.retries(l)), RnDecision.decide.reply(l, t, RnState.Deferred{})) == R.Step.act(R.step(RnDecision.Lim.retries(l), budget, R.Live{failed, RnDecision.At.p(l, t)}, R.Broke{retryable, gap})) : R.Act}:
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case RnDecision.At{+attempt, +notes, +waited, +compacted}:
          +cfg = {RnState.Cfg{rounds, wait, retries, most} : RnState.Cfg}
          +c = RnDecision.c.of(compacted)
          +a = Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes))
          +n = Nat.sub(most, notes)
          +ph = RnDecision.Then.ph(False{}, RnState.St.ph(RnStep.call(cfg, RnState.Deferred{}, 0n, c, a, n, Nat.sub(wait, waited))))
          %Equal.sym(RnDecision.Then, ph, Run.rust.wait(Nat.is_lt(waited, wait)), LA.rk.wait(cfg, 0n, c, a, n, wait, waited)) : {Run.rust.job(Bool.and(retryable, Nat.is_lt(failed, retries)), _) == R.Step.act(R.step(retries, budget, R.Live{failed, Nat.sub(wait, waited)}, R.Broke{retryable, gap})) : R.Act}
          %rk.gt(wait, waited) : {Run.rust.job(Bool.and(retryable, Nat.is_lt(failed, retries)), Run.rust.wait(Nat.is_lt(waited, wait))) == R.Step.act(R.live.failed(Bool.and(retryable, Bool.and(Nat.is_lt(failed, retries), _)), failed, Nat.sub(wait, waited), gap)) : R.Act}
          rk.job(retryable, Nat.is_lt(failed, retries), Nat.is_lt(waited, wait), failed, Nat.sub(wait, waited), gap)

def Run.run_failed_poll_is_the_job_model(l, t, retryable, failed, budget, gap):
  rk.run_failed_poll_is_the_job_model(l, t, retryable, failed, budget, gap)
