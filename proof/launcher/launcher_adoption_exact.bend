# eukhe: the proof of LAW launcher_adoption_exact

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher

def lae.pick(b: Bool) -> {La.adopt.put(b) == Launcher.adoption_spec.pick(b) : La.Adoption}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Launcher.launcher_adoption_exact(sup, w):
  match w:
    case None{}:
      {==}
    case Some{b}:
      lae.pick(Nat.is_eq(b, sup))
