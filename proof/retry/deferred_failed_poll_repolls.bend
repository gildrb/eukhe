# eukhe: the proof of LAW deferred_failed_poll_repolls

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/bool.bend as LBool
import ../base/logic/logic.bend as LLogicLogic

def rp.repoll(again: Bool, +failed: Nat, +left: Nat, +gap: Nat, e: {again == True{} : Bool}) -> {R.live.failed(again, failed, left, gap) == R.Step{R.Poll{}, R.Live{1n+failed, Nat.sub(left, 1n+gap)}} : R.Step}:
  match again:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.rp.absurdF({R.live.failed(False{}, failed, left, gap) == R.Step{R.Poll{}, R.Live{1n+failed, Nat.sub(left, 1n+gap)}} : R.Step}, e)

def failed_poll_repolls(+fails: Nat, +budget: Nat, +failed: Nat, +left: Nat, +gap: Nat, below: {Nat.is_lt(failed, fails) == True{} : Bool}, live: {Nat.is_gt(left, 0n) == True{} : Bool}) -> {R.step(fails, budget, R.Live{failed, left}, R.Broke{True{}, gap}) == R.Step{R.Poll{}, R.Live{1n+failed, Nat.sub(left, 1n+gap)}} : R.Step}:
  rp.repoll(Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n)), failed, left, gap, LBool.rp.and_tt(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n), below, live))

def Retry.deferred_failed_poll_repolls(fails, budget, failed, left, gap, below, live):
  failed_poll_repolls(fails, budget, failed, left, gap, below, live)
