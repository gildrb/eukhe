# eukhe: the proof of LAW child_one_live

import Base
import ../../bend/child.bend as Ch
import ../../spec/child.bend as ChS
import ../../laws/child.bend as Child
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def pc.old_live(rest: List<&2, ChS.Sub>, +m: Nat, o: {LA.pc.Old(rest, m) == True{} : Bool}) -> {0n == ChS.live(rest) : Nat}:
  match rest:
    case Nil{}:
      {==}
    case s <> r:
      match s:
        case ChS.Sub{+j, f}:
          match f:
            case Ch.Queued{}:
              LLogicLogic.child.pc.absurd({0n == ChS.live(ChS.Sub{j, Ch.Queued{}} <> r) : Nat}, o)
            case Ch.Withdrawn{}:
              pc.old_live(r, j, LA.pc.and_r(Nat.is_le(1n+j, m), LA.pc.Old(r, j), o))
            case Ch.Placed{}:
              LLogicLogic.child.pc.absurd({0n == ChS.live(ChS.Sub{j, Ch.Placed{}} <> r) : Nat}, o)

# one_live, report_once: only the newest submission may be live
def pc.le1_live(f: Ch.Fate) -> {Nat.is_le(Nat.add(ChS.Fate.live(f), 0n), 1n) == True{} : Bool}:
  match f:
    case Ch.Queued{}:
      {==}
    case Ch.Withdrawn{}:
      {==}
    case Ch.Placed{}:
      {==}

def pc.live_le(inbox: List<&2, ChS.Sub>, kin: {LA.pc.Kin(inbox) == True{} : Bool}) -> {Nat.is_le(ChS.live(inbox), 1n) == True{} : Bool}:
  match inbox:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case ChS.Sub{+m, f}:
          %pc.old_live(rest, m, kin) : {Nat.is_le(Nat.add(ChS.Fate.live(f), _), 1n) == True{} : Bool}
          pc.le1_live(f)

def pc.one_live(+cfg: Ch.Cfg, +w: Ch.W, +evs: List<&2, ChS.Ev>) -> {Nat.is_le(ChS.live(ChS.St.inbox(ChS.run(evs, cfg, ChS.St.init(w)))), 1n) == True{} : Bool}:
  pc.live_le(ChS.St.inbox(ChS.run(evs, cfg, ChS.St.init(w))), LA.pc.Kin_of(ChS.run(evs, cfg, ChS.St.init(w)), LA.pc.K_run(evs, cfg, ChS.St.init(w), {==})))

def Child.child_one_live(cfg, w, evs):
  pc.one_live(cfg, w, evs)
