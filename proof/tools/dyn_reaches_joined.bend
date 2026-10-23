# eukhe: the proof of LAW dyn_reaches_joined

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def pl.elem_cons(d: List<&2, Nat>, +t: Nat) -> {Tl.elem(t <> d, t) == True{} : Bool}:
  %LA.tools.pl.eq_refl(t) : {Bool.or(_, Tl.elem(d, t)) == True{} : Bool}
  {==}

def pl.dyn_reaches_joined(+s: Tl.Sess, +t: Nat) -> {Tl.dyn_call(Tl.step(s, Tl.Join{t}), t) == True{} : Bool}:
  match s:
    case Tl.Sess{r, d, x}:
      pl.elem_cons(d, t)

def Tools.dyn_reaches_joined(s, t):
  pl.dyn_reaches_joined(s, t)
