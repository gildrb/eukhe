# eukhe: the proof of LAW launcher_adopt_own_build
#
# Nat.is_eq(n, n) is True (induction on n), so adoption picks Adopt.

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def lao.refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lao.refl(p)

def Launcher.launcher_adopt_own_build(sup):
  %Equal.sym(Bool, Nat.is_eq(sup, sup), True{}, lao.refl(sup)) : {La.adopt.put(_) == La.Adopt{} : La.Adoption}
  {==}
