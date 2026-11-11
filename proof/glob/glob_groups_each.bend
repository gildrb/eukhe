# eukhe: the proof of LAW glob_groups_each
#
# PROOF: by induction on the sizes and j: the first answer searches the
# first k texts; the (j + 1)-th is the j-th of the texts after the first
# k (drop of a drop is one drop); a search over texts is the or of the
# patterns' matches (GQ.gq.texts).

import Base
import ../../bend/glob/items.bend as GItems
import ../../bend/glob/queries.bend as GQuery
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL
import ./base/query.bend as GQ

def gge.get(ks: List<&2, Nat>, +xs: List<&2, List<&2, GItems.It>>, +ss: List<&2, String>, j: Nat, h: {Nat.is_lt(j, List.length(&2, Nat, ks)) == True{} : Bool}) -> {List.get(&2, Bool, GQuery.groups(ks, xs, ss), j) == Some{GQuery.hit_any(Glob.sp_group(ss, ks, j), xs)} : Maybe<&2, Bool>}:
  match ks j:
    case Nil{} 0n:
      GL.gl.ft({List.get(&2, Bool, GQuery.groups(Nil{}, xs, ss), 0n) == Some{GQuery.hit_any(Glob.sp_group(ss, Nil{}, 0n), xs)} : Maybe<&2, Bool>}, h)
    case Nil{} 1n+m:
      GL.gl.ft({List.get(&2, Bool, GQuery.groups(Nil{}, xs, ss), 1n+m) == Some{GQuery.hit_any(Glob.sp_group(ss, Nil{}, 1n+m), xs)} : Maybe<&2, Bool>}, h)
    case +k <> r 0n:
      %Equal.sym(List<&2, String>, List.drop(&2, String, ss, 0n), ss, GQ.gq.drop0(ss)) : {Some{GQuery.hit_any(List.take(&2, String, ss, k), xs)} == Some{GQuery.hit_any(List.take(&2, String, _, k), xs)} : Maybe<&2, Bool>}
      {==}
    case +k <> +r 1n++m:
      +n = Glob.sp_sum(List.take(&2, Nat, r, m))
      %Equal.sym(Maybe<&2, Bool>, List.get(&2, Bool, GQuery.groups(r, xs, List.drop(&2, String, ss, k)), m), Some{GQuery.hit_any(Glob.sp_group(List.drop(&2, String, ss, k), r, m), xs)}, gge.get(r, xs, List.drop(&2, String, ss, k), m, h)) : {_ == Some{GQuery.hit_any(Glob.sp_group(ss, k <> r, 1n+m), xs)} : Maybe<&2, Bool>}
      %GQ.gq.drop_drop(ss, k, n) : {Some{GQuery.hit_any(Glob.sp_group(List.drop(&2, String, ss, k), r, m), xs)} == Some{GQuery.hit_any(List.take(&2, String, _, Maybe.default(&2, Nat, List.get(&2, Nat, r, m), 0n)), xs)} : Maybe<&2, Bool>}
      {==}

def Glob.glob_groups_each(o, ps, ss, ks, j, h):
  +xs = GQuery.compile(o, ps)
  +g = Glob.sp_group(ss, ks, j)
  Equal.trans(Maybe<&2, Bool>, List.get(&2, Bool, GQuery.groups(ks, xs, ss), j), Some{GQuery.hit_any(g, xs)}, Some{Glob.sp_texts_hit(o, ps, g)}, gge.get(ks, xs, ss, j, h), Equal.cong(Bool, Maybe<&2, Bool>, z => Some{z}, GQuery.hit_any(g, xs), Glob.sp_texts_hit(o, ps, g), GQ.gq.texts(o, ps, g)))
