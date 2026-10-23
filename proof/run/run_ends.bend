# eukhe: the proof of LAW run_ends

import Base
import ../../bend/run/measure.bend as RnMeasure
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run
import ../base/logic/nat.bend as LLogicNat
import ../base/nat.bend as LNat
import ../base/run.bend as LRun
import ./base.bend as LA

# The bound
# ---------

# a generation: 2 + (U + 2)·(polls + 2), U = retries + notes
def G_eq(+P: Nat, +U: Nat) -> {LLogicNat.G(P, U) == 2n+Nat.mul(2n+U, 2n+P) : Nat}:
  +Y = Nat.add(P, Nat.mul(U, LLogicNat.Q(P)))
  %Equal.sym(Nat, Nat.add(P, 0n), P, LNat.add_zero(P)) : {1n+Nat.add(LLogicNat.Q(P), Nat.add(3n+_, Nat.mul(U, LLogicNat.Q(P)))) == 2n+Nat.mul(2n+U, 2n+P) : Nat}
  %Equal.sym(Nat, Nat.add(P, Nat.add(3n, Y)), Nat.add(3n, Nat.add(P, Y)), LNat.add_lcomm(P, 3n, Y)) : {3n+_ == 2n+Nat.mul(2n+U, 2n+P) : Nat}
  %Equal.sym(Nat, Nat.add(P, Nat.add(2n, Y)), Nat.add(2n, Nat.add(P, Y)), LNat.add_lcomm(P, 2n, Y)) : {6n+Nat.add(P, Y) == 4n+_ : Nat}
  {==}

# bound(cfg) is M at the start
def bound_m(+cfg: RnState.Cfg) -> {RnMeasure.bound(cfg) == LLogicNat.M(cfg, RnState.init(cfg)) : Nat}:
  match cfg:
    case RnState.Cfg{cap, pp, aa, nn}:
      +U = Nat.add(aa, nn)
      +gp = LLogicNat.gen(pp, RnState.Prepare{}, 1n, U, 0n)
      +r0 = Nat.sub(cap, 1n)
      %G_eq(pp, U) : {Nat.mul(Nat.max(cap, 1n), _) == LLogicNat.M(RnState.Cfg{cap, pp, aa, nn}, RnState.init(RnState.Cfg{cap, pp, aa, nn})) : Nat}
      %Equal.sym(Nat, Nat.max(cap, 1n), 1n+r0, LA.max1(cap)) : {Nat.mul(_, LLogicNat.G(pp, U)) == LLogicNat.M(RnState.Cfg{cap, pp, aa, nn}, RnState.init(RnState.Cfg{cap, pp, aa, nn})) : Nat}
      %LNat.add_succ(gp, Nat.mul(r0, LLogicNat.G(pp, U))) : {_ == Nat.add(gp, 1n+Nat.mul(r0, LLogicNat.G(pp, U))) : Nat}
      {==}

def run_append(xs: List<&2, RnState.Ev>, -ys: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St) -> {RnStep.run.go(List.append(&2, RnState.Ev, xs, ys), cfg, s) == RnStep.run.go(ys, cfg, RnStep.run.go(xs, cfg, s)) : RnState.St}:
  match xs:
    case Nil{}:
      {==}
    case e <> rest:
      run_append(rest, ys, cfg, RnStep.step(cfg, s, e))

# The laws
# --------

def run_ends(+cfg: RnState.Cfg, +xs: List<&2, RnState.Ev>, h: {List.length(&2, RnState.Ev, xs) == RnMeasure.bound(cfg) : Nat}, +more: List<&2, RnState.Ev>) -> {RnState.done(RnStep.run(cfg, List.append(&2, RnState.Ev, xs, more))) == True{} : Bool}:
  %Equal.sym(RnState.St, RnStep.run.go(List.append(&2, RnState.Ev, xs, more), cfg, RnState.init(cfg)), RnStep.run.go(more, cfg, RnStep.run.go(xs, cfg, RnState.init(cfg))), run_append(xs, more, cfg, RnState.init(cfg))) : {RnState.done(_) == True{} : Bool}
  LRun.stays_done(more, cfg, RnStep.run.go(xs, cfg, RnState.init(cfg)), LRun.ends(xs, cfg, RnState.init(cfg), 0n, Equal.trans(Nat, List.length(&2, RnState.Ev, xs), RnMeasure.bound(cfg), LLogicNat.M(cfg, RnState.init(cfg)), h, bound_m(cfg))))

# (H4) Every run ends

def Run.run_ends(cfg, evs, long, more):
  run_ends(cfg, evs, long, more)
