# eukhe: the proof of LAW run_first_deferred_reply_is_the_job_model

import Base
import ../../bend/run.bend as Rn
import ../../bend/retry.bend as R
import ../../LAWS.bend as Laws
import ./base.bend as LA

def rk.run_first_deferred_reply_is_the_job_model(+l: Rn.Lim, +t: Rn.At, +fails: Nat, +gap: Nat) -> {Laws.rust.later(Rn.decide.reply(l, t, Rn.Deferred{})) == R.Step.act(R.step(fails, Rn.At.p(l, t), R.NoJob{}, R.Later{gap})) : R.Act}:
  match l:
    case Rn.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case Rn.At{+attempt, +notes, +waited, +compacted}:
          +cfg = {Rn.Cfg{rounds, wait, retries, most} : Rn.Cfg}
          +c = Rn.c.of(compacted)
          +a = Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes))
          +n = Nat.sub(most, notes)
          +ph = Rn.Then.ph(False{}, Rn.St.ph(Rn.call(cfg, Rn.Deferred{}, 0n, c, a, n, Nat.sub(wait, waited))))
          %Equal.sym(Rn.Then, ph, Laws.rust.wait(Nat.is_lt(waited, wait)), LA.rk.wait(cfg, 0n, c, a, n, wait, waited)) : {Laws.rust.later(_) == R.Step.act(R.step(fails, Nat.sub(wait, waited), R.NoJob{}, R.Later{gap})) : R.Act}
          %LA.rk.eq0(wait, waited) : {Laws.rust.later(Laws.rust.wait(Nat.is_lt(waited, wait))) == R.Step.act(R.live.pending(_, Nat.sub(wait, waited), gap)) : R.Act}
          LA.rk.later(Nat.is_lt(waited, wait), Nat.sub(wait, waited), gap)

def Laws.run_first_deferred_reply_is_the_job_model(l, t, fails, gap):
  rk.run_first_deferred_reply_is_the_job_model(l, t, fails, gap)
