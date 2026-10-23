# eukhe: the proof of LAW pace_never_back

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen.bend as Screen
import ../base/nat.bend as LNat

# s is at most s + x
def ps.le_add_self(s: Nat, +x: Nat) -> {Nat.is_le(s, Nat.add(s, x)) == True{} : Bool}:
  match s:
    case 0n:
      LNat.ps.le0(x)
    case 1n+p:
      ps.le_add_self(p, x)

def ps.pace_never_back(+min: Nat, +k: Nat, +p: Sc.Pace, e: Sc.PEv) -> {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.shown(Sc.pace.step(min, k, p, e))) == True{} : Bool}:
  match p:
    case Sc.Pace{+r, +s}:
      match e:
        case Sc.Chunk{n}:
          LNat.screen.ps.le_refl(s)
        case Sc.Frame{}:
          ps.le_add_self(s, Sc.reveal(min, k, Nat.sub(r, s)))

def Screen.pace_never_back(min, k, p, e):
  ps.pace_never_back(min, k, p, e)
