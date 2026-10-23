# eukhe: the proof of LAW run_rounds_capped

import Base
import ../../bend/run/measure.bend as RnMeasure
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run
import ./base.bend as LA

# The laws' conclusions
# ---------------------

def lt_add(x: Nat, -r: Nat) -> {Nat.is_lt(x, Nat.add(x, 1n+r)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+y:
      lt_add(y, r)

def lt_of(n: Nat, -r: Nat, -cap: Nat, eq: {Nat.add(n, 1n+r) == cap : Nat}) -> {Nat.is_lt(n, cap) == True{} : Bool}:
  %eq : {Nat.is_lt(n, _) == True{} : Bool}
  lt_add(n, r)

# a run that did not fail made fewer than max(cap, 1) rounds
def rounds_of(+cfg: RnState.Cfg, +s: RnState.St, +k: Nat, i: LA.InvS(cfg, s, k)) -> Or({RnState.failed(s) == True{} : Bool}, {Nat.is_lt(k, Nat.max(RnState.Cfg.cap(cfg), 1n)) == True{} : Bool}):
  (cp, co) = i
  match co:
    case Inl{f}:
      Inl{f}
    case Inr{eq}:
      Inr{lt_of(k, RnState.St.r(s), Nat.max(RnState.Cfg.cap(cfg), 1n), eq)}

def rounds_capped(+cfg: RnState.Cfg, +evs: List<&2, RnState.Ev>) -> Or({RnState.failed(RnStep.run(cfg, evs)) == True{} : Bool}, {Nat.is_lt(RnMeasure.rounds(cfg, evs), Nat.max(RnState.Cfg.cap(cfg), 1n)) == True{} : Bool}):
  rounds_of(cfg, RnStep.run(cfg, evs), RnMeasure.rounds(cfg, evs), LA.inv_run(evs, cfg, RnState.init(cfg), 0n, LA.inv_init(cfg)))

def Run.run_rounds_capped(cfg, evs):
  rounds_capped(cfg, evs)
