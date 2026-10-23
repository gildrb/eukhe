# eukhe: the proof of LAW layout_apart

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen.bend as Screen
import ../base/nat/is_le.bend as LNatIsLe
import ./base.bend as LA

def screen.ps.le_add_l(y: Nat, +a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(y, a), Nat.add(y, b)) == True{} : Bool}:
  match y:
    case 0n:
      h
    case 1n+p:
      screen.ps.le_add_l(p, a, b, h)

# children placed from row y keep apart from any row z at or above y
def ps.apart_go(hs: List<&2, Nat>, +y: Nat, +rows: Nat, +z: Nat, hz: {Nat.is_le(z, y) == True{} : Bool}) -> {Sc.apart(Sc.vstack(hs, y, rows), z) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      +m = Nat.min(h, Nat.sub(rows, y))
      LA.screen.ps.and_t(Nat.is_le(z, y), Sc.apart(Sc.vstack(rest, Nat.add(y, h), rows), Nat.add(y, m)), hz, ps.apart_go(rest, Nat.add(y, h), rows, Nat.add(y, m), screen.ps.le_add_l(y, m, h, LA.ps.min_le_l(h, Nat.sub(rows, y)))))

def ps.layout_apart(hs: List<&2, Nat>, +y: Nat, +rows: Nat) -> {Sc.apart(Sc.vstack(hs, y, rows), y) == True{} : Bool}:
  ps.apart_go(hs, y, rows, y, LNatIsLe.screen.ps.le_refl(y))

def Screen.layout_apart(hs, y, rows):
  ps.layout_apart(hs, y, rows)
