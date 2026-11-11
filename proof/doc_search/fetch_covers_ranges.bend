# eukhe: the proof of LAW fetch_covers_ranges
#
# PROOF: the fetch is max(p + 1, min(top, maxb + 1)), top the last line
# any range needs: at least p + 1; and at least min(top, maxb + 1), so top
# or maxb + 1 is at most the fetch (ds.min_le_or), which covers every
# range (ds.covers_or).

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LA

def DocSearch.fetch_covers_ranges(r, rs, p, rem, maxb):
  +top = Sr.reach.top(r <> rs, 1n+p)
  +m = Nat.min(top, 1n+maxb)
  +f = Nat.max(1n+p, m)
  LA.ds.and_t(Nat.is_le(1n+p, f), DocSearch.ds_covers(r <> rs, f, 1n+p, maxb), LA.ds.le_max_l(1n+p, m), LA.ds.covers_or(r <> rs, f, 1n+p, maxb, LA.ds.min_le_or(top, 1n+maxb, f, LA.ds.le_max_r(1n+p, m))))
