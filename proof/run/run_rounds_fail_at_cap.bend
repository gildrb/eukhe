# eukhe: the proof of LAW run_rounds_fail_at_cap

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws
import ./base.bend as LA

# a run the cap failed made max(cap, 1) rounds
def caps_of(+cfg: Rn.Cfg, +s: Rn.St, +k: Nat, i: LA.InvS(cfg, s, k)) -> Or({Rn.capped(s) == False{} : Bool}, {k == Nat.max(Rn.Cfg.cap(cfg), 1n) : Nat}):
  (cp, co) = i
  cp

def rounds_fail_at_cap(+cfg: Rn.Cfg, +evs: List<&2, Rn.Ev>) -> Or({Rn.capped(Rn.run(cfg, evs)) == False{} : Bool}, {Rn.rounds(cfg, evs) == Nat.max(Rn.Cfg.cap(cfg), 1n) : Nat}):
  caps_of(cfg, Rn.run(cfg, evs), Rn.rounds(cfg, evs), LA.inv_run(evs, cfg, Rn.init(cfg), 0n, LA.inv_init(cfg)))

def Laws.run_rounds_fail_at_cap(cfg, evs):
  rounds_fail_at_cap(cfg, evs)
