# eukhe: the proof of LAW secret_needs_a_secret_path

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def ps.secret_needs_a_secret_path(+xs: List<&2, Tl.Part>, has: {Tl.elem(Tl.join(Tl.parts.effs(xs)), 6n) == True{} : Bool}) -> {Tl.parts.secret(xs) == True{} : Bool}:
  Equal.trans(Bool, Tl.parts.secret(xs), Tl.elem(Tl.join(Tl.parts.effs(xs)), 6n), True{}, Equal.sym(Bool, Tl.elem(Tl.join(Tl.parts.effs(xs)), 6n), Tl.parts.secret(xs), LA.ps.secret_iff(xs)), has)

def Tools.secret_needs_a_secret_path(ps, has):
  ps.secret_needs_a_secret_path(ps, has)
