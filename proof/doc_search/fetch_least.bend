# eukhe: the proof of LAW fetch_least
#
# PROOF: x covers every range, so the last line any range needs, or maxb
# + 1, is at most x (ds.top_or): min(top, maxb + 1) is at most x; and p +
# 1 is at most x: so is their max, the fetch.

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LA

def fl.go(+r: Sr.Range, +rs: List<&2, Sr.Range>, +p: Nat, +maxb: Nat, +x: Nat, +hx: {Bool.and(Nat.is_le(1n+p, x), DocSearch.ds_covers(r <> rs, x, 1n+p, maxb)) == True{} : Bool}) -> {Nat.is_le(Nat.max(1n+p, Nat.min(Sr.reach.top(r <> rs, 1n+p), 1n+maxb)), x) == True{} : Bool}:
  +top = Sr.reach.top(r <> rs, 1n+p)
  +h1 = LA.ds.and_l(Nat.is_le(1n+p, x), DocSearch.ds_covers(r <> rs, x, 1n+p, maxb), hx)
  +hc = LA.ds.and_r(Nat.is_le(1n+p, x), DocSearch.ds_covers(r <> rs, x, 1n+p, maxb), hx)
  LA.ds.max_le(1n+p, Nat.min(top, 1n+maxb), x, h1, LA.ds.or_min_le(top, 1n+maxb, x, LA.ds.top_or(r <> rs, x, 1n+p, maxb, hc)))

def DocSearch.fetch_least(r, rs, p, rem, maxb, x, hx):
  fl.go(r, rs, p, maxb, x, hx)
