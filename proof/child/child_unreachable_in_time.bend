# eukhe: the proof of LAW child_unreachable_in_time

import Base
import ../../bend/child.bend as Ch
import ../../spec/child.bend as ChS
import ../../laws/child.bend as Child
import ../base/child.bend as LChild
import ../base/logic/logic.bend as LLogicLogic

# from the clock spend(r, tok, 1 + q), failed polls ds, more than q of
# them, end the watch
def pc.miss(ds: List<&2, Nat>, +cfg: Ch.Cfg, +r: Nat, +tok: Maybe<&2, Nat>, +q: Nat, long: {Nat.is_le(1n+q, List.length(&2, Nat, ds)) == True{} : Bool}) -> {ChS.watches(ChS.hush(ChS.misses(ds), cfg, Ch.spend(r, tok, 1n+q))) == False{} : Bool}:
  match ds:
    case Nil{}:
      LLogicLogic.child.pc.absurd({ChS.watches(ChS.hush(Nil{}, cfg, Ch.spend(r, tok, 1n+q))) == False{} : Bool}, long)
    case +d <> +t:
      match r:
        case 0n:
          LChild.pc.owe_stops(ChS.misses(d <> t), cfg, Ch.Stalled{})
        case 1n+p:
          match q:
            case 0n:
              LChild.pc.owe_stops(ChS.misses(t), cfg, Ch.Unreachable{})
            case 1n+u:
              pc.miss(t, cfg, Nat.sub(p, d), tok, u, long)

def pc.unreachable_in_time(+cfg: Ch.Cfg, +tok: Maybe<&2, Nat>, +l: Nat, +n: Nat, +d: Nat, +ds: List<&2, Nat>, long: {Nat.is_le(n, List.length(&2, Nat, d <> ds)) == True{} : Bool}) -> {ChS.watches(ChS.hush(ChS.misses(d <> ds), cfg, Ch.Watch{Ch.W{tok, l, n}})) == False{} : Bool}:
  match n:
    case 0n:
      LChild.pc.owe_stops(ChS.misses(ds), cfg, Ch.Unreachable{})
    case 1n+q:
      match q:
        case 0n:
          LChild.pc.owe_stops(ChS.misses(ds), cfg, Ch.Unreachable{})
        case 1n+u:
          pc.miss(ds, cfg, Nat.sub(l, 1n+d), tok, u, long)

def Child.child_unreachable_in_time(cfg, tok, l, n, d, ds, long):
  pc.unreachable_in_time(cfg, tok, l, n, d, ds, long)
