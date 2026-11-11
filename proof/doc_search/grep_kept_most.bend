# eukhe: the proof of LAW grep_kept_most
#
# PROOF: x below h, p and rem is below min(p, rem), then below
# min(h, min(p, rem)), what the file keeps.

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LA

def gkm.go(+h: Nat, +p: Nat, +rem: Nat, +x: Nat, +hx: {Bool.and(Nat.is_le(x, h), Bool.and(Nat.is_le(x, p), Nat.is_le(x, rem))) == True{} : Bool}) -> {Nat.is_le(x, Nat.min(h, Nat.min(p, rem))) == True{} : Bool}:
  +hr = LA.ds.and_r(Nat.is_le(x, h), Bool.and(Nat.is_le(x, p), Nat.is_le(x, rem)), hx)
  LA.ds.le_min(x, h, Nat.min(p, rem), LA.ds.and_l(Nat.is_le(x, h), Bool.and(Nat.is_le(x, p), Nat.is_le(x, rem)), hx), LA.ds.le_min(x, p, rem, LA.ds.and_l(Nat.is_le(x, p), Nat.is_le(x, rem), hr), LA.ds.and_r(Nat.is_le(x, p), Nat.is_le(x, rem), hr)))

def DocSearch.grep_kept_most(i, h, big, p, rem, x, hx):
  gkm.go(h, p, rem, x, hx)
