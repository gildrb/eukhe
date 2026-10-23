# eukhe: the proof of LAW run_ends

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run
import ../base/nat/add.bend as LNatAdd
import ../base/nat/misc.bend as LNatMisc
import ../base/run.bend as LRun
import ./base.bend as LA

# The bound
# ---------

# a generation: 2 + (U + 2)·(polls + 2), U = retries + notes
def G_eq(+P: Nat, +U: Nat) -> {LNatMisc.G(P, U) == 2n+Nat.mul(2n+U, 2n+P) : Nat}:
  +Y = Nat.add(P, Nat.mul(U, LNatMisc.Q(P)))
  %Equal.sym(Nat, Nat.add(P, 0n), P, LNatAdd.add_zero(P)) : {1n+Nat.add(LNatMisc.Q(P), Nat.add(3n+_, Nat.mul(U, LNatMisc.Q(P)))) == 2n+Nat.mul(2n+U, 2n+P) : Nat}
  %Equal.sym(Nat, Nat.add(P, Nat.add(3n, Y)), Nat.add(3n, Nat.add(P, Y)), LNatAdd.add_lcomm(P, 3n, Y)) : {3n+_ == 2n+Nat.mul(2n+U, 2n+P) : Nat}
  %Equal.sym(Nat, Nat.add(P, Nat.add(2n, Y)), Nat.add(2n, Nat.add(P, Y)), LNatAdd.add_lcomm(P, 2n, Y)) : {6n+Nat.add(P, Y) == 4n+_ : Nat}
  {==}

# bound(cfg) is M at the start
def bound_m(+cfg: Rn.Cfg) -> {Rn.bound(cfg) == LNatMisc.M(cfg, Rn.init(cfg)) : Nat}:
  match cfg:
    case Rn.Cfg{cap, pp, aa, nn}:
      +U = Nat.add(aa, nn)
      +gp = LNatMisc.gen(pp, Rn.Prepare{}, 1n, U, 0n)
      +r0 = Nat.sub(cap, 1n)
      %G_eq(pp, U) : {Nat.mul(Nat.max(cap, 1n), _) == LNatMisc.M(Rn.Cfg{cap, pp, aa, nn}, Rn.init(Rn.Cfg{cap, pp, aa, nn})) : Nat}
      %Equal.sym(Nat, Nat.max(cap, 1n), 1n+r0, LA.max1(cap)) : {Nat.mul(_, LNatMisc.G(pp, U)) == LNatMisc.M(Rn.Cfg{cap, pp, aa, nn}, Rn.init(Rn.Cfg{cap, pp, aa, nn})) : Nat}
      %LNatAdd.add_succ(gp, Nat.mul(r0, LNatMisc.G(pp, U))) : {_ == Nat.add(gp, 1n+Nat.mul(r0, LNatMisc.G(pp, U))) : Nat}
      {==}

def run_append(xs: List<&2, Rn.Ev>, -ys: List<&2, Rn.Ev>, +cfg: Rn.Cfg, +s: Rn.St) -> {Rn.run.go(List.append(&2, Rn.Ev, xs, ys), cfg, s) == Rn.run.go(ys, cfg, Rn.run.go(xs, cfg, s)) : Rn.St}:
  match xs:
    case Nil{}:
      {==}
    case e <> rest:
      run_append(rest, ys, cfg, Rn.step(cfg, s, e))

# The laws
# --------

def run_ends(+cfg: Rn.Cfg, +xs: List<&2, Rn.Ev>, h: {List.length(&2, Rn.Ev, xs) == Rn.bound(cfg) : Nat}, +more: List<&2, Rn.Ev>) -> {Rn.done(Rn.run(cfg, List.append(&2, Rn.Ev, xs, more))) == True{} : Bool}:
  %Equal.sym(Rn.St, Rn.run.go(List.append(&2, Rn.Ev, xs, more), cfg, Rn.init(cfg)), Rn.run.go(more, cfg, Rn.run.go(xs, cfg, Rn.init(cfg))), run_append(xs, more, cfg, Rn.init(cfg))) : {Rn.done(_) == True{} : Bool}
  LRun.stays_done(more, cfg, Rn.run.go(xs, cfg, Rn.init(cfg)), LRun.ends(xs, cfg, Rn.init(cfg), 0n, Equal.trans(Nat, List.length(&2, Rn.Ev, xs), Rn.bound(cfg), LNatMisc.M(cfg, Rn.init(cfg)), h, bound_m(cfg))))

# (H4) Every run ends

def Run.run_ends(cfg, evs, long, more):
  run_ends(cfg, evs, long, more)
