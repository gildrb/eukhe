# eukhe: lemmas the proofs of two or more areas share: child

import Base
import ../../bend/child.bend as Ch
import ../../spec/child.bend as ChS
import ./logic/logic.bend as LLogicLogic
import ./nat.bend as LNat

# The watch
# ---------

# an owed report stays owed through any more polls
def pc.owe_stops(hs: List<&2, ChS.Hush>, +cfg: Ch.Cfg, +k: Ch.Report) -> {ChS.watches(ChS.hush(hs, cfg, Ch.Owe{k})) == False{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case h <> t:
      pc.owe_stops(t, cfg, k)

# the token the watch holds is no progress
def pc.moved_self(+tok: Maybe<&2, Nat>) -> {False{} == Ch.moved(tok, tok) : Bool}:
  match tok:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, LNat.child.pc.eq_refl(x)) : {False{} == Bool.not(_) : Bool}
      {==}

# from the clock spend(r, tok, n), quiet polls hs, at least r of them,
# end the watch: each takes 1 ms or more off the r ms left
def pc.stall(hs: List<&2, ChS.Hush>, +cfg: Ch.Cfg, +r: Nat, +tok: Maybe<&2, Nat>, +n: Nat, long: {Nat.is_le(r, List.length(&2, ChS.Hush, hs)) == True{} : Bool}) -> {ChS.watches(ChS.hush(hs, cfg, Ch.spend(r, tok, n))) == False{} : Bool}:
  match hs:
    case Nil{}:
      match r:
        case 0n:
          {==}
        case 1n+p:
          LLogicLogic.child.pc.absurd({ChS.watches(ChS.hush(Nil{}, cfg, Ch.spend(1n+p, tok, n))) == False{} : Bool}, long)
    case h <> +t:
      match h:
        case ChS.Same{+dt}:
          match r:
            case 0n:
              pc.owe_stops(t, cfg, Ch.Stalled{})
            case 1n+p:
              %pc.moved_self(tok) : {ChS.watches(ChS.hush(t, cfg, Ch.busy(_, cfg, Ch.W{tok, 1n+p, n}, tok, 1n+dt))) == False{} : Bool}
              pc.stall(t, cfg, Nat.sub(p, dt), tok, Ch.Cfg.fails(cfg), LNat.child.pc.le_trans(Nat.sub(p, dt), p, List.length(&2, ChS.Hush, t), LNat.pc.sub_le(p, dt), long))
        case ChS.Miss{+dt}:
          match r:
            case 0n:
              pc.owe_stops(t, cfg, Ch.Stalled{})
            case 1n+p:
              match n:
                case 0n:
                  pc.owe_stops(t, cfg, Ch.Unreachable{})
                case 1n+q:
                  match q:
                    case 0n:
                      pc.owe_stops(t, cfg, Ch.Unreachable{})
                    case 1n+u:
                      pc.stall(t, cfg, Nat.sub(p, dt), tok, 1n+u, LNat.child.pc.le_trans(Nat.sub(p, dt), p, List.length(&2, ChS.Hush, t), LNat.pc.sub_le(p, dt), long))

# a clock with nothing left ends at the next quiet poll
def pc.spent(h: ChS.Hush, hs: List<&2, ChS.Hush>, +cfg: Ch.Cfg, +tok: Maybe<&2, Nat>, +n: Nat) -> {ChS.watches(ChS.hush(h <> hs, cfg, Ch.Watch{Ch.W{tok, 0n, n}})) == False{} : Bool}:
  match h:
    case ChS.Same{+dt}:
      %pc.moved_self(tok) : {ChS.watches(ChS.hush(hs, cfg, Ch.busy(_, cfg, Ch.W{tok, 0n, n}, tok, 1n+dt))) == False{} : Bool}
      pc.owe_stops(hs, cfg, Ch.Stalled{})
    case ChS.Miss{+dt}:
      match n:
        case 0n:
          pc.owe_stops(hs, cfg, Ch.Unreachable{})
        case 1n+q:
          match q:
            case 0n:
              pc.owe_stops(hs, cfg, Ch.Unreachable{})
            case 1n+u:
              pc.owe_stops(hs, cfg, Ch.Stalled{})

def pc.stalls_in_time(+cfg: Ch.Cfg, +tok: Maybe<&2, Nat>, +l: Nat, +n: Nat, +h: ChS.Hush, +hs: List<&2, ChS.Hush>, long: {Nat.is_le(l, List.length(&2, ChS.Hush, h <> hs)) == True{} : Bool}) -> {ChS.watches(ChS.hush(h <> hs, cfg, Ch.Watch{Ch.W{tok, l, n}})) == False{} : Bool}:
  match l:
    case 0n:
      pc.spent(h, hs, cfg, tok, n)
    case 1n+p:
      pc.stall(h <> hs, cfg, 1n+p, tok, n, long)

# a busy poll whose token x moved from the held one is progress: the
# clock full from the settings
def pc.progress(+s: Nat, +f: Nat, +tok: Maybe<&2, Nat>, +l: Nat, +n: Nat, +e: Nat, +x: Nat, news: {Ch.moved(tok, Some{x}) == True{} : Bool}) -> {Ch.look(Ch.Cfg{s, f}, Ch.W{tok, l, n}, e, Ch.Busy{Some{x}}) == Ch.Watch{Ch.W{Some{x}, s, f}} : Ch.Next}:
  %Equal.sym(Bool, Ch.moved(tok, Some{x}), True{}, news) : {Ch.busy(_, Ch.Cfg{s, f}, Ch.W{tok, l, n}, Some{x}, e) == Ch.Watch{Ch.W{Some{x}, s, f}} : Ch.Next}
  {==}
