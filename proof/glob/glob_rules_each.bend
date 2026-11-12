# eukhe: the proof of LAW glob_rules_each
#
# PROOF: by induction on the sizes and j: the first answer searches the
# texts with the first k patterns; the (j + 1)-th is the j-th of the
# patterns after the first k (drop of a drop is one drop); a search over
# texts is the or of the patterns' matches (GQ.gq.texts).

import Base
import ../../bend/glob/items.bend as GItems
import ../../bend/glob/queries.bend as GQuery
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL
import ./base/query.bend as GQ

def gre.get(ks: List<&2, Nat>, +o: GItems.Opts, +ps: List<&2, String>, +ss: List<&2, String>, j: Nat, h: {Nat.is_lt(j, List.length(&2, Nat, ks)) == True{} : Bool}) -> {List.get(&2, Bool, GQuery.rules(ks, o, ps, ss), j) == Some{GQuery.hit_any(ss, GQuery.compile(o, Glob.sp_group(ps, ks, j)))} : Maybe<&2, Bool>}:
  match ks j:
    case Nil{} 0n:
      GL.gl.ft({List.get(&2, Bool, GQuery.rules(Nil{}, o, ps, ss), 0n) == Some{GQuery.hit_any(ss, GQuery.compile(o, Glob.sp_group(ps, Nil{}, 0n)))} : Maybe<&2, Bool>}, h)
    case Nil{} 1n+m:
      GL.gl.ft({List.get(&2, Bool, GQuery.rules(Nil{}, o, ps, ss), 1n+m) == Some{GQuery.hit_any(ss, GQuery.compile(o, Glob.sp_group(ps, Nil{}, 1n+m)))} : Maybe<&2, Bool>}, h)
    case +k <> r 0n:
      %Equal.sym(List<&2, String>, List.drop(&2, String, ps, 0n), ps, GQ.gq.drop0(ps)) : {Some{GQuery.hit_any(ss, GQuery.compile(o, List.take(&2, String, ps, k)))} == Some{GQuery.hit_any(ss, GQuery.compile(o, List.take(&2, String, _, k)))} : Maybe<&2, Bool>}
      {==}
    case +k <> +r 1n++m:
      +n = Glob.sp_sum(List.take(&2, Nat, r, m))
      +dp = List.drop(&2, String, ps, k)
      %Equal.sym(Maybe<&2, Bool>, List.get(&2, Bool, GQuery.rules(r, o, dp, ss), m), Some{GQuery.hit_any(ss, GQuery.compile(o, Glob.sp_group(dp, r, m)))}, gre.get(r, o, dp, ss, m, h)) : {_ == Some{GQuery.hit_any(ss, GQuery.compile(o, Glob.sp_group(ps, k <> r, 1n+m)))} : Maybe<&2, Bool>}
      %GQ.gq.drop_drop(ps, k, n) : {Some{GQuery.hit_any(ss, GQuery.compile(o, Glob.sp_group(dp, r, m)))} == Some{GQuery.hit_any(ss, GQuery.compile(o, List.take(&2, String, _, Maybe.default(&2, Nat, List.get(&2, Nat, r, m), 0n))))} : Maybe<&2, Bool>}
      {==}

def Glob.glob_rules_each(ks, o, ps, ss, j, h):
  +g = Glob.sp_group(ps, ks, j)
  Equal.trans(Maybe<&2, Bool>, List.get(&2, Bool, GQuery.rules(ks, o, ps, ss), j), Some{GQuery.hit_any(ss, GQuery.compile(o, g))}, Some{Glob.sp_texts_hit(o, g, ss)}, gre.get(ks, o, ps, ss, j, h), Equal.cong(Bool, Maybe<&2, Bool>, z => Some{z}, GQuery.hit_any(ss, GQuery.compile(o, g)), Glob.sp_texts_hit(o, g, ss), GQ.gq.texts(o, g, ss)))
