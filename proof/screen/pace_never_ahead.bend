# eukhe: the proof of LAW pace_never_ahead

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen.bend as Screen
import ../base/bool/misc.bend as LBoolMisc
import ../base/nat/is_le.bend as LNatIsLe
import ./base.bend as LA

def ps.le_add_r(s: Nat, r: Nat, +n: Nat, h: {Nat.is_le(s, r) == True{} : Bool}) -> {Nat.is_le(s, Nat.add(r, n)) == True{} : Bool}:
  match s r:
    case 0n _:
      LNatIsLe.ps.le0(Nat.add(r, n))
    case 1n+sp 0n:
      LBoolMisc.screen.ps.absurdF({Nat.is_le(1n+sp, Nat.add(0n, n)) == True{} : Bool}, h)
    case 1n+sp 1n+rp:
      ps.le_add_r(sp, rp, n, h)

def ps.step_ahead(+min: Nat, +k: Nat, p: Sc.Pace, e: Sc.PEv, h: {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.recv(p)) == True{} : Bool}) -> {Nat.is_le(Sc.Pace.shown(Sc.pace.step(min, k, p, e)), Sc.Pace.recv(Sc.pace.step(min, k, p, e))) == True{} : Bool}:
  match p:
    case Sc.Pace{+r, +s}:
      match e:
        case Sc.Chunk{n}:
          ps.le_add_r(s, r, n, h)
        case Sc.Frame{}:
          LA.ps.bound(s, r, Nat.max(min, Sc.share(k, Nat.sub(r, s))), h)

def ps.run_ahead(es: List<&2, Sc.PEv>, +min: Nat, +k: Nat, +p: Sc.Pace, h: {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.recv(p)) == True{} : Bool}) -> {Nat.is_le(Sc.Pace.shown(Sc.pace.run(es, min, k, p)), Sc.Pace.recv(Sc.pace.run(es, min, k, p))) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      ps.run_ahead(rest, min, k, Sc.pace.step(min, k, p, e), ps.step_ahead(min, k, p, e, h))

def ps.pace_never_ahead(es: List<&2, Sc.PEv>, +min: Nat, +k: Nat) -> {Nat.is_le(Sc.Pace.shown(Sc.pace.run(es, min, k, Sc.Pace{0n, 0n})), Sc.Pace.recv(Sc.pace.run(es, min, k, Sc.Pace{0n, 0n}))) == True{} : Bool}:
  ps.run_ahead(es, min, k, Sc.Pace{0n, 0n}, {==})

def Screen.pace_never_ahead(es, min, k):
  ps.pace_never_ahead(es, min, k)
