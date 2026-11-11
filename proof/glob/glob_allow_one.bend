# eukhe: the proof of LAW glob_allow_one
#
# PROOF: a list of one pattern decides as the pattern (GA.al.single); the
# pattern is trimmed to p (GA.al.trim: White_Space dropped at the start,
# then, reversed, at the end); then blank, wildcard and plain patterns
# decide as sp_allow says (GA.al.e).

import Base
import ../../bend/glob/queries.bend as GQuery
import ../../laws/glob.bend as Glob
import ./base/allow.bend as GA
import ./base/logic.bend as GL

def gao.go(+sel: String, +w1: String, +p: String, +w2: String, +h: {Bool.and(Glob.sp_all_ws(w1), Bool.and(Glob.sp_trimmed(p), Glob.sp_all_ws(w2))) == True{} : Bool}) -> {GQuery.allowed(sel, [String.append(w1, String.append(p, w2))]) == Glob.sp_allow(sel, p) : Bool}:
  +x = String.append(w1, String.append(p, w2))
  +h1 = GL.gl.and_l(Glob.sp_all_ws(w1), Bool.and(Glob.sp_trimmed(p), Glob.sp_all_ws(w2)), h)
  +hr = GL.gl.and_r(Glob.sp_all_ws(w1), Bool.and(Glob.sp_trimmed(p), Glob.sp_all_ws(w2)), h)
  +hp = GL.gl.and_l(Glob.sp_trimmed(p), Glob.sp_all_ws(w2), hr)
  +h2 = GL.gl.and_r(Glob.sp_trimmed(p), Glob.sp_all_ws(w2), hr)
  Equal.trans(Bool, GQuery.allowed(sel, [x]), GQuery.allow1(sel, x), Glob.sp_allow(sel, p), GA.al.single(sel, x), Equal.trans(Bool, GQuery.allow.e(String.is_empty(GQuery.trim(x)), sel, GQuery.trim(x)), GQuery.allow.e(String.is_empty(p), sel, p), Glob.sp_allow(sel, p), Equal.cong(String, Bool, z => GQuery.allow.e(String.is_empty(z), sel, z), GQuery.trim(x), p, GA.al.trim(w1, p, w2, h1, hp, h2)), GA.al.e(String.is_empty(p), sel, p)))

def Glob.glob_allow_one(sel, w1, p, w2, h):
  gao.go(sel, w1, p, w2, h)
