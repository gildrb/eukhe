# eukhe: the proof of LAW paint_picks_first_pass
#
# PROOF: each of the check results' cases computes to a frame compared with
# itself.

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen/interface.bend as Screen

def paint.refl(n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      paint.refl(p)

def paint.law(+f: Nat, +g: Nat, +h: Nat, +ok1: Bool, +ok2: Bool, +ok3: Bool) -> {Screen.paint_first_pass(f, g, h, ok1, ok2, ok3, Sc.resync(Sc.present(f, g, ok1, ok2), h, ok3)) == True{} : Bool}:
  match ok1 ok2 ok3:
    case True{} ok2 ok3:
      %paint.refl(f) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case False{} True{} ok3:
      %paint.refl(g) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case False{} False{} True{}:
      %paint.refl(h) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case False{} False{} False{}:
      %paint.refl(f) : {Bool.and(_, True{}) == True{} : Bool}
      {==}

def Screen.paint_picks_first_pass(f, g, h, ok1, ok2, ok3):
  paint.law(f, g, h, ok1, ok2, ok3)
