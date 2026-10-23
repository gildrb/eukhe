# eukhe: the proof of LAW child_one_live

import Base
import ../../bend/child.bend as Ch
import ../../laws/child.bend as Child
import ../base/bool/misc.bend as LBoolMisc
import ./base.bend as LA

def pc.old_live(rest: List<&2, Ch.Sub>, +m: Nat, o: {LA.pc.Old(rest, m) == True{} : Bool}) -> {0n == Ch.live(rest) : Nat}:
  match rest:
    case Nil{}:
      {==}
    case s <> r:
      match s:
        case Ch.Sub{+j, f}:
          match f:
            case Ch.Queued{}:
              LBoolMisc.child.pc.absurd({0n == Ch.live(Ch.Sub{j, Ch.Queued{}} <> r) : Nat}, o)
            case Ch.Withdrawn{}:
              pc.old_live(r, j, LA.pc.and_r(Nat.is_le(1n+j, m), LA.pc.Old(r, j), o))
            case Ch.Placed{}:
              LBoolMisc.child.pc.absurd({0n == Ch.live(Ch.Sub{j, Ch.Placed{}} <> r) : Nat}, o)

# one_live, report_once: only the newest submission may be live
def pc.le1_live(f: Ch.Fate) -> {Nat.is_le(Nat.add(Ch.Fate.live(f), 0n), 1n) == True{} : Bool}:
  match f:
    case Ch.Queued{}:
      {==}
    case Ch.Withdrawn{}:
      {==}
    case Ch.Placed{}:
      {==}

def pc.live_le(inbox: List<&2, Ch.Sub>, kin: {LA.pc.Kin(inbox) == True{} : Bool}) -> {Nat.is_le(Ch.live(inbox), 1n) == True{} : Bool}:
  match inbox:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Ch.Sub{+m, f}:
          %pc.old_live(rest, m, kin) : {Nat.is_le(Nat.add(Ch.Fate.live(f), _), 1n) == True{} : Bool}
          pc.le1_live(f)

def pc.one_live(+cfg: Ch.Cfg, +evs: List<&2, Ch.Ev>) -> {Nat.is_le(Ch.live(Ch.St.inbox(Ch.run(evs, cfg, Ch.St.init(cfg)))), 1n) == True{} : Bool}:
  pc.live_le(Ch.St.inbox(Ch.run(evs, cfg, Ch.St.init(cfg))), LA.pc.Kin_of(Ch.run(evs, cfg, Ch.St.init(cfg)), LA.pc.K_run(evs, cfg, Ch.St.init(cfg), {==})))

def Child.child_one_live(cfg, evs):
  pc.one_live(cfg, evs)
