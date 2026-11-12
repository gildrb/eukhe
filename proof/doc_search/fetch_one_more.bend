# eukhe: the proof of LAW fetch_one_more
#
# PROOF: with no range the fetch is 1 + min(p, rem); a file keeps
# min(h, min(p, rem)), at most min(p, rem), so less than the fetch; and
# min(p, rem) is at most p and at most rem.

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LA

def DocSearch.fetch_one_more(h, big, p, rem, maxb):
  +m = Nat.min(p, rem)
  LA.ds.and_t(Nat.is_lt(Nat.min(h, m), 1n+m), Bool.and(Nat.is_le(1n+m, 1n+p), Nat.is_le(1n+m, 1n+rem)), LA.ds.le_lt_succ(Nat.min(h, m), m, LA.ds.min_le_r(h, m)), LA.ds.and_t(Nat.is_le(1n+m, 1n+p), Nat.is_le(1n+m, 1n+rem), LA.ds.min_le_l(p, rem), LA.ds.min_le_r(p, rem)))
