# eukhe: the proof of LAW glob_class_negated
#
# PROOF: a negated set is the not of its set test. `.` is every byte, as
# the negated empty set; `[^/]` is x != 47, and the set of 47..47 is
# 47 <= x <= 47, which is x == 47 (GL.gl.in_one).

import Base
import ../../bend/glob/items.bend as GItems
import ../../bend/glob/match.bend as GMatch
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL

def cng.not(fold: Bool, +rs: List<&2, GItems.BR>, +x: U32) -> {GMatch.bc(GItems.BSet{True{}, fold, rs}, x) == Bool.not(GMatch.bc(GItems.BSet{False{}, fold, rs}, x)) : Bool}:
  match fold:
    case True{}:
      {==}
    case False{}:
      {==}

def cng.slash(+x: U32) -> {(GMatch.bc(GItems.BAny{}, x), GMatch.bc(GItems.BNotSl{}, x)) == (GMatch.bc(GItems.BSet{True{}, False{}, Nil{}}, x), GMatch.bc(GItems.BSet{True{}, False{}, [GItems.BR{47, 47}]}, x)) : Bool & Bool}:
  %Equal.sym(Bool, Bool.or(Bool.and(U32.is_le(47, x), U32.is_le(x, 47)), False{}), U32.is_eq(x, 47), GL.gl.in_one(47, x)) : {(True{}, Bool.not(U32.is_eq(x, 47))) == (True{}, Bool.not(_)) : Bool & Bool}
  {==}

def Glob.glob_class_negated(fold, rs, x):
  (cng.not(fold, rs, x), cng.slash(x))
