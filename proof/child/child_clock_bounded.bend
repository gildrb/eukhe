# eukhe: the proof of LAW child_clock_bounded

import Base
import ../../bend/child.bend as Ch
import ../../laws/child.bend as Child
import ../base/nat.bend as LNat
import ./base.bend as LA

def pc.spend_within(+cfg: Ch.Cfg, +r: Nat, +tok: Maybe<&2, Nat>, +n: Nat, er: {Nat.is_le(r, Ch.Cfg.stall(cfg)) == True{} : Bool}, en: {Nat.is_le(n, Ch.Cfg.fails(cfg)) == True{} : Bool}) -> {Ch.within(cfg, Ch.spend(r, tok, n)) == True{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      LA.pc.and_in(Nat.is_le(1n+p, Ch.Cfg.stall(cfg)), Nat.is_le(n, Ch.Cfg.fails(cfg)), er, en)

def pc.busy_within(b: Bool, +cfg: Ch.Cfg, +w: Ch.W, +t: Maybe<&2, Nat>, +e: Nat, full: {Ch.within(cfg, Ch.Watch{w}) == True{} : Bool}) -> {Ch.within(cfg, Ch.busy(b, cfg, w, t, e)) == True{} : Bool}:
  match b:
    case True{}:
      LA.pc.and_in(Nat.is_le(Ch.Cfg.stall(cfg), Ch.Cfg.stall(cfg)), Nat.is_le(Ch.Cfg.fails(cfg), Ch.Cfg.fails(cfg)), LNat.child.pc.le_refl(Ch.Cfg.stall(cfg)), LNat.child.pc.le_refl(Ch.Cfg.fails(cfg)))
    case False{}:
      match w:
        case Ch.W{+tok, +l, +n}:
          pc.spend_within(cfg, Nat.sub(l, e), tok, Ch.Cfg.fails(cfg), LNat.child.pc.le_trans(Nat.sub(l, e), l, Ch.Cfg.stall(cfg), LNat.pc.sub_le(l, e), LA.pc.and_l(Nat.is_le(l, Ch.Cfg.stall(cfg)), Nat.is_le(n, Ch.Cfg.fails(cfg)), full)), LNat.child.pc.le_refl(Ch.Cfg.fails(cfg)))

def pc.look_within(o: Ch.Obs, +cfg: Ch.Cfg, +w: Ch.W, +e: Nat, +full: {Ch.within(cfg, Ch.Watch{w}) == True{} : Bool}) -> {Ch.within(cfg, Ch.look(cfg, w, e, o)) == True{} : Bool}:
  match o:
    case Ch.Busy{+t}:
      pc.busy_within(Ch.moved(Ch.W.tok(w), t), cfg, w, t, e, full)
    case Ch.Lost{}:
      match w:
        case Ch.W{+tok, +l, +n}:
          match n:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+u:
                  pc.spend_within(cfg, Nat.sub(l, e), tok, 1n+u, LNat.child.pc.le_trans(Nat.sub(l, e), l, Ch.Cfg.stall(cfg), LNat.pc.sub_le(l, e), LA.pc.and_l(Nat.is_le(l, Ch.Cfg.stall(cfg)), Nat.is_le(2n+u, Ch.Cfg.fails(cfg)), full)), LA.pc.le_pred(1n+u, Ch.Cfg.fails(cfg), LA.pc.and_r(Nat.is_le(l, Ch.Cfg.stall(cfg)), Nat.is_le(2n+u, Ch.Cfg.fails(cfg)), full)))
    case Ch.Answered{r}:
      match r:
        case True{}:
          {==}
        case False{}:
          {==}
    case Ch.Broke{}:
      {==}
    case Ch.Gone{}:
      {==}

def pc.clock_bounded(+cfg: Ch.Cfg, +w: Ch.W, +e: Nat, o: Ch.Obs, full: {Ch.within(cfg, Ch.Watch{w}) == True{} : Bool}) -> {Ch.within(cfg, Ch.look(cfg, w, e, o)) == True{} : Bool}:
  pc.look_within(o, cfg, w, e, full)

def Child.child_clock_bounded(cfg, w, e, o, full):
  pc.clock_bounded(cfg, w, e, o, full)
