# eukhe: lemmas the proofs of two or more areas share: child

import Base
import ../../bend/child.bend as Ch
import ./logic/logic.bend as LLogicLogic
import ./nat.bend as LNat

# The watch
# ---------

# an owed report stays owed through any more polls
def pc.owe_stops(hs: List<&2, Ch.Hush>, +cfg: Ch.Cfg, +k: Ch.Report) -> {Ch.Next.watching(Ch.hush(hs, cfg, Ch.Owe{k})) == False{} : Bool}:
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
def pc.stall(hs: List<&2, Ch.Hush>, +cfg: Ch.Cfg, +r: Nat, +tok: Maybe<&2, Nat>, +n: Nat, long: {Nat.is_le(r, List.length(&2, Ch.Hush, hs)) == True{} : Bool}) -> {Ch.Next.watching(Ch.hush(hs, cfg, Ch.spend(r, tok, n))) == False{} : Bool}:
  match hs:
    case Nil{}:
      match r:
        case 0n:
          {==}
        case 1n+p:
          LLogicLogic.child.pc.absurd({Ch.Next.watching(Ch.hush(Nil{}, cfg, Ch.spend(1n+p, tok, n))) == False{} : Bool}, long)
    case h <> +t:
      match h:
        case Ch.Same{+dt}:
          match r:
            case 0n:
              pc.owe_stops(t, cfg, Ch.Stalled{})
            case 1n+p:
              %pc.moved_self(tok) : {Ch.Next.watching(Ch.hush(t, cfg, Ch.busy(_, cfg, Ch.W{tok, 1n+p, n}, tok, 1n+dt))) == False{} : Bool}
              pc.stall(t, cfg, Nat.sub(p, dt), tok, Ch.Cfg.fails(cfg), LNat.child.pc.le_trans(Nat.sub(p, dt), p, List.length(&2, Ch.Hush, t), LNat.pc.sub_le(p, dt), long))
        case Ch.Miss{+dt}:
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
                      pc.stall(t, cfg, Nat.sub(p, dt), tok, 1n+u, LNat.child.pc.le_trans(Nat.sub(p, dt), p, List.length(&2, Ch.Hush, t), LNat.pc.sub_le(p, dt), long))

# a clock with nothing left ends at the next quiet poll
def pc.spent(h: Ch.Hush, hs: List<&2, Ch.Hush>, +cfg: Ch.Cfg, +tok: Maybe<&2, Nat>, +n: Nat) -> {Ch.Next.watching(Ch.hush(h <> hs, cfg, Ch.Watch{Ch.W{tok, 0n, n}})) == False{} : Bool}:
  match h:
    case Ch.Same{+dt}:
      %pc.moved_self(tok) : {Ch.Next.watching(Ch.hush(hs, cfg, Ch.busy(_, cfg, Ch.W{tok, 0n, n}, tok, 1n+dt))) == False{} : Bool}
      pc.owe_stops(hs, cfg, Ch.Stalled{})
    case Ch.Miss{+dt}:
      match n:
        case 0n:
          pc.owe_stops(hs, cfg, Ch.Unreachable{})
        case 1n+q:
          match q:
            case 0n:
              pc.owe_stops(hs, cfg, Ch.Unreachable{})
            case 1n+u:
              pc.owe_stops(hs, cfg, Ch.Stalled{})

def pc.stalls_in_time(+cfg: Ch.Cfg, +w: Ch.W, +h: Ch.Hush, +hs: List<&2, Ch.Hush>, long: {Nat.is_le(Ch.W.left(w), List.length(&2, Ch.Hush, h <> hs)) == True{} : Bool}) -> {Ch.Next.watching(Ch.hush(h <> hs, cfg, Ch.Watch{w})) == False{} : Bool}:
  match w:
    case Ch.W{+tok, +l, +n}:
      match l:
        case 0n:
          pc.spent(h, hs, cfg, tok, n)
        case 1n+p:
          pc.stall(h <> hs, cfg, 1n+p, tok, n, long)

def pc.progress_is_not_a_stall(+cfg: Ch.Cfg, +w: Ch.W, +e: Nat, +x: Nat, news: {Ch.moved(Ch.W.tok(w), Some{x}) == True{} : Bool}) -> {Ch.look(cfg, w, e, Ch.Busy{Some{x}}) == Ch.Watch{Ch.W.fresh(cfg, Some{x})} : Ch.Next}:
  %Equal.sym(Bool, Ch.moved(Ch.W.tok(w), Some{x}), True{}, news) : {Ch.busy(_, cfg, w, Some{x}, e) == Ch.Watch{Ch.W.fresh(cfg, Some{x})} : Ch.Next}
  {==}
