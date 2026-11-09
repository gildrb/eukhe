# eukhe: the proof of LAW child_clock_bounded

import Base
import ../../bend/child.bend as Ch
import ../../spec/child.bend as ChS
import ../../laws/child.bend as Child
import ../base/nat.bend as LNat
import ./base.bend as LA

def pc.spend_within(+s: Nat, +f: Nat, +r: Nat, +tok: Maybe<&2, Nat>, +n: Nat, er: {Nat.is_le(r, s) == True{} : Bool}, en: {Nat.is_le(n, f) == True{} : Bool}) -> {ChS.within(s, f, Ch.spend(r, tok, n)) == True{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      LA.pc.and_in(Nat.is_le(1n+p, s), Nat.is_le(n, f), er, en)

def pc.busy_within(b: Bool, +s: Nat, +f: Nat, +tok: Maybe<&2, Nat>, +l: Nat, +n: Nat, +t: Maybe<&2, Nat>, +e: Nat, full: {Bool.and(Nat.is_le(l, s), Nat.is_le(n, f)) == True{} : Bool}) -> {ChS.within(s, f, Ch.busy(b, Ch.Cfg{s, f}, Ch.W{tok, l, n}, t, e)) == True{} : Bool}:
  match b:
    case True{}:
      LA.pc.and_in(Nat.is_le(s, s), Nat.is_le(f, f), LNat.child.pc.le_refl(s), LNat.child.pc.le_refl(f))
    case False{}:
      pc.spend_within(s, f, Nat.sub(l, e), tok, f, LNat.child.pc.le_trans(Nat.sub(l, e), l, s, LNat.pc.sub_le(l, e), LA.pc.and_l(Nat.is_le(l, s), Nat.is_le(n, f), full)), LNat.child.pc.le_refl(f))

def pc.look_within(o: Ch.Obs, +s: Nat, +f: Nat, +tok: Maybe<&2, Nat>, +l: Nat, +n: Nat, +e: Nat, +full: {Bool.and(Nat.is_le(l, s), Nat.is_le(n, f)) == True{} : Bool}) -> {ChS.within(s, f, Ch.look(Ch.Cfg{s, f}, Ch.W{tok, l, n}, e, o)) == True{} : Bool}:
  match o:
    case Ch.Busy{+t}:
      pc.busy_within(Ch.moved(tok, t), s, f, tok, l, n, t, e, full)
    case Ch.Lost{}:
      match n:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+u:
              pc.spend_within(s, f, Nat.sub(l, e), tok, 1n+u, LNat.child.pc.le_trans(Nat.sub(l, e), l, s, LNat.pc.sub_le(l, e), LA.pc.and_l(Nat.is_le(l, s), Nat.is_le(2n+u, f), full)), LA.pc.le_pred(1n+u, f, LA.pc.and_r(Nat.is_le(l, s), Nat.is_le(2n+u, f), full)))
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

def Child.child_clock_bounded(s, f, tok, l, n, e, o, full):
  pc.look_within(o, s, f, tok, l, n, e, full)
