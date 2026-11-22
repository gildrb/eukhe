# eukhe: the proof of LAW secret_needs_a_secret_path
#
# PROOF: a step has the secret effect exactly when some part's secret
# field is True (LA.ps.secret_iff, by induction on the parts).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def ps.secret_needs_a_secret_path(+xs: List<&2, Tl.Part>, has: {Tl.elem(Tl.join(Tl.parts.effs(xs)), 6n) == True{} : Bool}) -> {Tools.tools_some_secret(xs) == True{} : Bool}:
  Equal.trans(Bool, Tools.tools_some_secret(xs), Tl.elem(Tl.join(Tl.parts.effs(xs)), 6n), True{}, Equal.sym(Bool, Tl.elem(Tl.join(Tl.parts.effs(xs)), 6n), Tools.tools_some_secret(xs), LA.ps.secret_iff(xs)), has)

def Tools.secret_needs_a_secret_path(ps, has):
  ps.secret_needs_a_secret_path(ps, has)
