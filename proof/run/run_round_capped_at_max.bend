# eukhe: the proof of LAW run_round_capped_at_max
#
# PROOF: how a round ends is the rule over the rounds Rust counted (LA.rk.round_rule); rounds <= count + 1, so count + 1 < rounds is false.

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run/model.bend as Run
import ./base.bend as LA

# a <= b, so b < a is false
def cap.le_not_lt(+a: Nat, +b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LA.rk.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, e)
    case 1n+p 1n+q:
      cap.le_not_lt(p, q, e)

def cap.rule(+rounds: Nat, +count: Nat, +reset: Bool, at: {Nat.is_le(rounds, 1n+count) == True{} : Bool}) -> {LA.rk.r_next(Nat.is_lt(1n+count, rounds), reset, count) == RnDecision.EndCapped{} : RnDecision.End}:
  %Equal.sym(Bool, Nat.is_lt(1n+count, rounds), False{}, cap.le_not_lt(rounds, 1n+count, at)) : {LA.rk.r_next(_, reset, count) == RnDecision.EndCapped{} : RnDecision.End}
  {==}

def Run.run_round_capped_at_max(l, count, reset, at):
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      +lim = {RnDecision.Lim{rounds, wait, retries, most} : RnDecision.Lim}
      Equal.trans(RnDecision.End, RnDecision.decide.round(lim, count, False{}, reset), LA.rk.r_round(lim, count, False{}, reset), RnDecision.EndCapped{}, LA.rk.round_rule(lim, count, False{}, reset), cap.rule(rounds, count, reset, at))
