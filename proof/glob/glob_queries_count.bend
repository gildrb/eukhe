# eukhe: the proof of LAW glob_queries_count
#
# PROOF: both queries answer once per size, by induction on the sizes.

import Base
import ../../bend/glob/items.bend as GItems
import ../../bend/glob/queries.bend as GQuery
import ../../laws/glob.bend as Glob

def gqc.groups(ks: List<&2, Nat>, +xs: List<&2, List<&2, GItems.It>>, +ss: List<&2, String>) -> {List.length(&2, Bool, GQuery.groups(ks, xs, ss)) == List.length(&2, Nat, ks) : Nat}:
  match ks:
    case Nil{}:
      {==}
    case +k <> r:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Bool, GQuery.groups(r, xs, List.drop(&2, String, ss, k))), List.length(&2, Nat, r), gqc.groups(r, xs, List.drop(&2, String, ss, k)))

def gqc.rules(ks: List<&2, Nat>, +o: GItems.Opts, +ps: List<&2, String>, +ss: List<&2, String>) -> {List.length(&2, Bool, GQuery.rules(ks, o, ps, ss)) == List.length(&2, Nat, ks) : Nat}:
  match ks:
    case Nil{}:
      {==}
    case +k <> r:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Bool, GQuery.rules(r, o, List.drop(&2, String, ps, k), ss)), List.length(&2, Nat, r), gqc.rules(r, o, List.drop(&2, String, ps, k), ss))

def Glob.glob_queries_count(o, ps, ss, ks):
  %Equal.sym(Nat, List.length(&2, Bool, GQuery.groups(ks, GQuery.compile(o, ps), ss)), List.length(&2, Nat, ks), gqc.groups(ks, GQuery.compile(o, ps), ss)) : {(_, List.length(&2, Bool, GQuery.rules(ks, o, ps, ss))) == (List.length(&2, Nat, ks), List.length(&2, Nat, ks)) : Nat & Nat}
  %Equal.sym(Nat, List.length(&2, Bool, GQuery.rules(ks, o, ps, ss)), List.length(&2, Nat, ks), gqc.rules(ks, o, ps, ss)) : {(List.length(&2, Nat, ks), _) == (List.length(&2, Nat, ks), List.length(&2, Nat, ks)) : Nat & Nat}
  {==}
