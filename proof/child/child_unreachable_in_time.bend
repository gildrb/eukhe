# eukhe: the proof of LAW child_unreachable_in_time

import Base
import ../../bend/child.bend as Ch
import ../../laws/child.bend as Child
import ../base/child.bend as LChild
import ../base/logic/logic.bend as LLogicLogic

# from the clock spend(r, tok, 1 + q), failed polls ds, more than q of
# them, end the watch
def pc.miss(ds: List<&2, Nat>, +cfg: Ch.Cfg, +r: Nat, +tok: Maybe<&2, Nat>, +q: Nat, long: {Nat.is_le(1n+q, List.length(&2, Nat, ds)) == True{} : Bool}) -> {Ch.Next.watching(Ch.hush(Ch.misses(ds), cfg, Ch.spend(r, tok, 1n+q))) == False{} : Bool}:
  match ds:
    case Nil{}:
      LLogicLogic.child.pc.absurd({Ch.Next.watching(Ch.hush(Nil{}, cfg, Ch.spend(r, tok, 1n+q))) == False{} : Bool}, long)
    case +d <> +t:
      match r:
        case 0n:
          LChild.pc.owe_stops(Ch.misses(d <> t), cfg, Ch.Stalled{})
        case 1n+p:
          match q:
            case 0n:
              LChild.pc.owe_stops(Ch.misses(t), cfg, Ch.Unreachable{})
            case 1n+u:
              pc.miss(t, cfg, Nat.sub(p, d), tok, u, long)

def pc.unreachable_in_time(+cfg: Ch.Cfg, +w: Ch.W, +d: Nat, +ds: List<&2, Nat>, long: {Nat.is_le(Ch.W.tries(w), List.length(&2, Nat, d <> ds)) == True{} : Bool}) -> {Ch.Next.watching(Ch.hush(Ch.misses(d <> ds), cfg, Ch.Watch{w})) == False{} : Bool}:
  match w:
    case Ch.W{+tok, +l, +n}:
      match n:
        case 0n:
          LChild.pc.owe_stops(Ch.misses(ds), cfg, Ch.Unreachable{})
        case 1n+q:
          match q:
            case 0n:
              LChild.pc.owe_stops(Ch.misses(ds), cfg, Ch.Unreachable{})
            case 1n+u:
              pc.miss(ds, cfg, Nat.sub(l, 1n+d), tok, u, long)

def Child.child_unreachable_in_time(cfg, w, d, ds, long):
  pc.unreachable_in_time(cfg, w, d, ds, long)
