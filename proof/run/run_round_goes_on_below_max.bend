# eukhe: the proof of LAW run_round_goes_on_below_max
#
# PROOF: how a round ends is the rule over the rounds Rust counted (LA.rk.round_rule); count + 1 < rounds, so the round goes on or resets.

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run/model.bend as Run
import ./base.bend as LA

def goes.rule(+rounds: Nat, +count: Nat, +reset: Bool, below: {Nat.is_lt(1n+count, rounds) == True{} : Bool}) -> {LA.rk.r_next(Nat.is_lt(1n+count, rounds), reset, count) == LA.rk.r_next(True{}, reset, count) : RnDecision.End}:
  %Equal.sym(Bool, Nat.is_lt(1n+count, rounds), True{}, below) : {LA.rk.r_next(_, reset, count) == LA.rk.r_next(True{}, reset, count) : RnDecision.End}
  {==}

def Run.run_round_goes_on_below_max(l, count, below):
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      +lim = {RnDecision.Lim{rounds, wait, retries, most} : RnDecision.Lim}
      (Equal.trans(RnDecision.End, RnDecision.decide.round(lim, count, False{}, False{}), LA.rk.r_round(lim, count, False{}, False{}), RnDecision.EndNext{1n+count}, LA.rk.round_rule(lim, count, False{}, False{}), goes.rule(rounds, count, False{}, below)), Equal.trans(RnDecision.End, RnDecision.decide.round(lim, count, False{}, True{}), LA.rk.r_round(lim, count, False{}, True{}), RnDecision.EndReset{}, LA.rk.round_rule(lim, count, False{}, True{}), goes.rule(rounds, count, True{}, below)))
