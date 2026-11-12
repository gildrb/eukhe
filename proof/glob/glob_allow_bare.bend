# eukhe: the proof of LAW glob_allow_bare
#
# PROOF: by induction on the text before the first `/`: no char of it is
# `/`, so the search for the first `/` goes past it to the `/` before b;
# with no `/` at all it finds none and the selector is kept.

import Base
import ../../bend/glob/queries.bend as GQuery
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL

def gab.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      GL.gl.ft({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def gab.after(a: String, +b: String, +h: {Glob.sp_no_slash(a) == True{} : Bool}) -> {GQuery.after_slash(String.append(a, SCon{Chr{47}, b})) == Some{b} : Maybe<&2, String>}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          +h1 = gab.not_t(U32.is_eq(x, 47), GL.gl.and_l(Bool.not(U32.is_eq(x, 47)), Glob.sp_no_slash(t), h))
          +h2 = GL.gl.and_r(Bool.not(U32.is_eq(x, 47)), Glob.sp_no_slash(t), h)
          %Equal.sym(Bool, U32.is_eq(x, 47), False{}, h1) : {GQuery.after_slash.k(_, String.append(t, SCon{Chr{47}, b}), GQuery.after_slash(String.append(t, SCon{Chr{47}, b}))) == Some{b} : Maybe<&2, String>}
          gab.after(t, b, h2)

def gab.none(s: String, +h: {Glob.sp_no_slash(s) == True{} : Bool}) -> {GQuery.after_slash(s) == None{} : Maybe<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          +h1 = gab.not_t(U32.is_eq(x, 47), GL.gl.and_l(Bool.not(U32.is_eq(x, 47)), Glob.sp_no_slash(t), h))
          +h2 = GL.gl.and_r(Bool.not(U32.is_eq(x, 47)), Glob.sp_no_slash(t), h)
          %Equal.sym(Bool, U32.is_eq(x, 47), False{}, h1) : {GQuery.after_slash.k(_, t, GQuery.after_slash(t)) == None{} : Maybe<&2, String>}
          gab.none(t, h2)

def gab.go(+a: String, +b: String, +s: String, +h: {Bool.and(Glob.sp_no_slash(a), Glob.sp_no_slash(s)) == True{} : Bool}) -> {(GQuery.bare(String.append(a, SCon{Chr{47}, b})), GQuery.bare(s)) == (b, s) : String & String}:
  +x = String.append(a, SCon{Chr{47}, b})
  %Equal.sym(Maybe<&2, String>, GQuery.after_slash(x), Some{b}, gab.after(a, b, GL.gl.and_l(Glob.sp_no_slash(a), Glob.sp_no_slash(s), h))) : {(GQuery.bare.k(x, _), GQuery.bare(s)) == (b, s) : String & String}
  %Equal.sym(Maybe<&2, String>, GQuery.after_slash(s), None{}, gab.none(s, GL.gl.and_r(Glob.sp_no_slash(a), Glob.sp_no_slash(s), h))) : {(b, GQuery.bare.k(s, _)) == (b, s) : String & String}
  {==}

def Glob.glob_allow_bare(a, b, s, h):
  gab.go(a, b, s, h)
