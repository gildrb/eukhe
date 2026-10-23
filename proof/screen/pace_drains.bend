# eukhe: the proof of LAW pace_drains

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen.bend as Screen
import ../base/bool/misc.bend as LBoolMisc
import ../base/nat/is_le.bend as LNatIsLe
import ./base.bend as LA

def ps.sub_le(+n: Nat, +m: Nat) -> {Nat.is_le(Nat.sub(n, m), n) == True{} : Bool}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      LNatIsLe.screen.ps.le_refl(1n+np)
    case 1n+np 1n+mp:
      LNatIsLe.screen.ps.le_trans(Nat.sub(np, mp), np, 1n+np, ps.sub_le(np, mp), LNatIsLe.screen.ps.le_succ(np))

def ps.sub_sub(c: Nat, k: Nat, +n: Nat) -> {Nat.sub(Nat.sub(c, k), n) == Nat.sub(c, Nat.add(k, n)) : Nat}:
  match c k:
    case 0n _:
      {==}
    case 1n+cp 0n:
      {==}
    case 1n+cp 1n+kp:
      ps.sub_sub(cp, kp, n)

# a maximum with a positive side is positive
def ps.max_ge(min: Nat, x: Nat, one: {Nat.is_le(1n, min) == True{} : Bool}) -> {Nat.is_le(1n, Nat.max(min, x)) == True{} : Bool}:
  match min x:
    case 0n _:
      LBoolMisc.screen.ps.absurdF({Nat.is_le(1n, Nat.max(0n, x)) == True{} : Bool}, one)
    case 1n+mp 0n:
      LNatIsLe.ps.le0(mp)
    case 1n+mp 1n+xp:
      LNatIsLe.ps.le0(Nat.max(mp, xp))

def ps.eq_of(s: Nat, r: Nat, h1: {Nat.is_le(s, r) == True{} : Bool}, h2: {Nat.is_le(Nat.sub(r, s), 0n) == True{} : Bool}) -> {s == r : Nat}:
  match s r:
    case 0n 0n:
      {==}
    case 0n 1n+rp:
      LBoolMisc.screen.ps.absurdF({0n == 1n+rp : Nat}, h2)
    case 1n+sp 0n:
      LBoolMisc.screen.ps.absurdF({1n+sp == 0n : Nat}, h1)
    case 1n+sp 1n+rp:
      %ps.eq_of(sp, rp, h1, h2) : {1n+sp == 1n+_ : Nat}
      {==}

# a frame with a positive step takes at least one character off a
# backlog of at most 1 + m
def ps.drop(+b: Nat, +m: Nat, +x: Nat, hb: {Nat.is_le(b, 1n+m) == True{} : Bool}, hx: {Nat.is_le(1n, x) == True{} : Bool}) -> {Nat.is_le(Nat.sub(b, Nat.min(b, x)), m) == True{} : Bool}:
  match b x:
    case 0n _:
      LNatIsLe.ps.le0(m)
    case 1n+bp 0n:
      LBoolMisc.screen.ps.absurdF({Nat.is_le(Nat.sub(1n+bp, Nat.min(1n+bp, 0n)), m) == True{} : Bool}, hx)
    case 1n+bp 1n+xp:
      LNatIsLe.screen.ps.le_trans(Nat.sub(bp, Nat.min(bp, xp)), bp, m, ps.sub_le(bp, Nat.min(bp, xp)), hb)

def ps.drop_after(+r: Nat, +s: Nat, +m: Nat, +x: Nat, hb: {Nat.is_le(Nat.sub(r, s), 1n+m) == True{} : Bool}, hx: {Nat.is_le(1n, x) == True{} : Bool}) -> {Nat.is_le(Nat.sub(r, Nat.add(s, Nat.min(Nat.sub(r, s), x))), m) == True{} : Bool}:
  %ps.sub_sub(r, s, Nat.min(Nat.sub(r, s), x)) : {Nat.is_le(_, m) == True{} : Bool}
  ps.drop(Nat.sub(r, s), m, x, hb, hx)

def ps.drains_go(+n: Nat, +min: Nat, +k: Nat, +p: Sc.Pace, +one: {Nat.is_le(1n, min) == True{} : Bool}, behind: {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.recv(p)) == True{} : Bool}, enough: {Nat.is_le(Nat.sub(Sc.Pace.recv(p), Sc.Pace.shown(p)), n) == True{} : Bool}) -> {Sc.Pace.shown(Sc.pace.run(Sc.frames(n), min, k, p)) == Sc.Pace.recv(p) : Nat}:
  match n:
    case 0n:
      match p:
        case Sc.Pace{r, s}:
          ps.eq_of(s, r, behind, enough)
    case 1n+m:
      match p:
        case Sc.Pace{+r, +s}:
          +x = Nat.max(min, Sc.share(k, Nat.sub(r, s)))
          ps.drains_go(m, min, k, Sc.Pace{r, Nat.add(s, Nat.min(Nat.sub(r, s), x))}, one, LA.ps.bound(s, r, x, behind), ps.drop_after(r, s, m, x, enough, ps.max_ge(min, Sc.share(k, Nat.sub(r, s)), one)))

def ps.pace_drains(+min: Nat, +k: Nat, +p: Sc.Pace, +n: Nat, one: {Nat.is_le(1n, min) == True{} : Bool}, behind: {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.recv(p)) == True{} : Bool}, enough: {Nat.is_le(Nat.sub(Sc.Pace.recv(p), Sc.Pace.shown(p)), n) == True{} : Bool}) -> {Sc.Pace.shown(Sc.pace.run(Sc.frames(n), min, k, p)) == Sc.Pace.recv(p) : Nat}:
  ps.drains_go(n, min, k, p, one, behind, enough)

def Screen.pace_drains(min, k, p, n, one, behind, enough):
  ps.pace_drains(min, k, p, n, one, behind, enough)
