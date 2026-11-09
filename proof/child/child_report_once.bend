# eukhe: the proof of LAW child_report_once

import Base
import ../../bend/child.bend as Ch
import ../../spec/child.bend as ChS
import ../../laws/child.bend as Child
import ./base.bend as LA

def pc.le1_placed(f: Ch.Fate) -> {Nat.is_le(Nat.add(ChS.Fate.placed(f), 0n), 1n) == True{} : Bool}:
  match f:
    case Ch.Queued{}:
      {==}
    case Ch.Withdrawn{}:
      {==}
    case Ch.Placed{}:
      {==}

def pc.placed_le(inbox: List<&2, ChS.Sub>, kin: {LA.pc.Kin(inbox) == True{} : Bool}) -> {Nat.is_le(ChS.placed(inbox), 1n) == True{} : Bool}:
  match inbox:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case ChS.Sub{+m, f}:
          %LA.pc.old_placed(rest, m, kin) : {Nat.is_le(Nat.add(ChS.Fate.placed(f), _), 1n) == True{} : Bool}
          pc.le1_placed(f)

def pc.report_once(+cfg: Ch.Cfg, +w: Ch.W, +evs: List<&2, ChS.Ev>) -> {Nat.is_le(ChS.St.placed(ChS.run(evs, cfg, ChS.St.init(w))), 1n) == True{} : Bool}:
  pc.placed_le(ChS.St.inbox(ChS.run(evs, cfg, ChS.St.init(w))), LA.pc.Kin_of(ChS.run(evs, cfg, ChS.St.init(w)), LA.pc.K_run(evs, cfg, ChS.St.init(w), {==})))

def Child.child_report_once(cfg, w, evs):
  pc.report_once(cfg, w, evs)
