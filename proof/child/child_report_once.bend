# eukhe: the proof of LAW child_report_once

import Base
import ../../bend/child.bend as Ch
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pc.le1_placed(f: Ch.Fate) -> {Nat.is_le(Nat.add(Ch.Fate.placed(f), 0n), 1n) == True{} : Bool}:
  match f:
    case Ch.Queued{}:
      {==}
    case Ch.Withdrawn{}:
      {==}
    case Ch.Placed{}:
      {==}

def pc.placed_le(inbox: List<&2, Ch.Sub>, kin: {LA.pc.Kin(inbox) == True{} : Bool}) -> {Nat.is_le(Ch.placed(inbox), 1n) == True{} : Bool}:
  match inbox:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Ch.Sub{+m, f}:
          %LA.pc.old_placed(rest, m, kin) : {Nat.is_le(Nat.add(Ch.Fate.placed(f), _), 1n) == True{} : Bool}
          pc.le1_placed(f)

def pc.report_once(+cfg: Ch.Cfg, +evs: List<&2, Ch.Ev>) -> {Nat.is_le(Ch.St.placed(Ch.run(evs, cfg, Ch.St.init(cfg))), 1n) == True{} : Bool}:
  pc.placed_le(Ch.St.inbox(Ch.run(evs, cfg, Ch.St.init(cfg))), LA.pc.Kin_of(Ch.run(evs, cfg, Ch.St.init(cfg)), LA.pc.K_run(evs, cfg, Ch.St.init(cfg), {==})))

def Laws.child_report_once(cfg, evs):
  pc.report_once(cfg, evs)
