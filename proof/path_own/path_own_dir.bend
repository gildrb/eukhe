# eukhe: the proof of LAW path_own_dir
#
# PROOF: the directory is its own path (LAR.pc.ids_refl), and the parent
# of n <> p is p, so the rule names both.

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/path_own.bend as Po
import ../../bend/tools.bend as Tl
import ../../laws/path_own.bend as PathOwn
import ../path_policy/base/root.bend as LAR
import ../irreversible/base.bend as LIr

def pod.self(+p: List<&2, Nat>, -c: Pp.Cls) -> {Po.class([Po.Dir{p}], p, c, True{}) == Po.Own{0n} : Po.Wc}:
  %Equal.sym(Bool, Tl.ids.eq(p, p), True{}, LAR.pc.ids_refl(p)) : {Po.of(Po.first.pick(Bool.or(_, Pp.parent_is(p, p)), 0n, None{}), c) == Po.Own{0n} : Po.Wc}
  {==}

def pod.entry(+n: Nat, +p: List<&2, Nat>, -c: Pp.Cls) -> {Po.class([Po.Dir{p}], n <> p, c, True{}) == Po.Own{0n} : Po.Wc}:
  %Equal.sym(Bool, Tl.ids.eq(p, p), True{}, LAR.pc.ids_refl(p)) : {Po.of(Po.first.pick(Bool.or(Tl.ids.eq(n <> p, p), _), 0n, None{}), c) == Po.Own{0n} : Po.Wc}
  %Equal.sym(Bool, Bool.or(Tl.ids.eq(n <> p, p), True{}), True{}, LIr.irb.or_true_r(Tl.ids.eq(n <> p, p))) : {Po.of(Po.first.pick(_, 0n, None{}), c) == Po.Own{0n} : Po.Wc}
  {==}

def PathOwn.path_own_dir(n, p, c):
  (pod.self(p, c), pod.entry(n, p, c))
