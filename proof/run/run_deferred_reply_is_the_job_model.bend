# eukhe: the proof of LAW run_deferred_reply_is_the_job_model

import Base
import ../../bend/retry.bend as R
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run
import ./base.bend as LA

def rk.run_deferred_reply_is_the_job_model(+l: Rn.Lim, +t: Rn.At, +fails: Nat, +budget: Nat, +failed: Nat, +gap: Nat) -> {Run.rust.later(Rn.decide.reply(l, t, Rn.Deferred{})) == R.Step.act(R.step(fails, budget, R.Live{failed, Rn.At.p(l, t)}, R.Later{gap})) : R.Act}:
  match l:
    case Rn.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case Rn.At{+attempt, +notes, +waited, +compacted}:
          +cfg = {Rn.Cfg{rounds, wait, retries, most} : Rn.Cfg}
          +c = Rn.c.of(compacted)
          +a = Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes))
          +n = Nat.sub(most, notes)
          +ph = Rn.Then.ph(False{}, Rn.St.ph(Rn.call(cfg, Rn.Deferred{}, 0n, c, a, n, Nat.sub(wait, waited))))
          %Equal.sym(Rn.Then, ph, Run.rust.wait(Nat.is_lt(waited, wait)), LA.rk.wait(cfg, 0n, c, a, n, wait, waited)) : {Run.rust.later(_) == R.Step.act(R.step(fails, budget, R.Live{failed, Nat.sub(wait, waited)}, R.Later{gap})) : R.Act}
          %LA.rk.eq0(wait, waited) : {Run.rust.later(Run.rust.wait(Nat.is_lt(waited, wait))) == R.Step.act(R.live.pending(_, Nat.sub(wait, waited), gap)) : R.Act}
          LA.rk.later(Nat.is_lt(waited, wait), Nat.sub(wait, waited), gap)

def Run.run_deferred_reply_is_the_job_model(l, t, fails, budget, failed, gap):
  rk.run_deferred_reply_is_the_job_model(l, t, fails, budget, failed, gap)
