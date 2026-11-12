# eukhe: the proof of LAW grep_kept_caps
#
# PROOF: an opened file keeps min(h, min(p, rem)), below each of the
# three (min is below both its sides, and <= is transitive); a skip keeps
# 0 and leaves rem; an opened file leaves rem - kept, and kept <= rem.

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LA

def kc.caps(+h: Nat, +p: Nat, +rem: Nat) -> {Bool.and(Nat.is_le(Nat.min(h, Nat.min(p, rem)), h), Bool.and(Nat.is_le(Nat.min(h, Nat.min(p, rem)), p), Nat.is_le(Nat.min(h, Nat.min(p, rem)), rem))) == True{} : Bool}:
  +m = Nat.min(p, rem)
  +x = Nat.min(h, m)
  LA.ds.and_t(Nat.is_le(x, h), Bool.and(Nat.is_le(x, p), Nat.is_le(x, rem)), LA.ds.min_le_l(h, m),
    LA.ds.and_t(Nat.is_le(x, p), Nat.is_le(x, rem), LA.ds.le_trans(x, m, p, LA.ds.min_le_r(h, m), LA.ds.min_le_l(p, rem)), LA.ds.le_trans(x, m, rem, LA.ds.min_le_r(h, m), LA.ds.min_le_r(p, rem))))

# what an entry keeps and leaves add up to rem
def kc.sum(+i: Nat, f: Sr.Form, +p: Nat, +rem: Nat) -> {Nat.add(Sr.kept(Sr.Ent{i, f}, p, rem), Sr.left(Sr.Ent{i, f}, p, rem)) == rem : Nat}:
  match f:
    case Sr.Opened{+h, big}:
      +m = Nat.min(p, rem)
      +x = Nat.min(h, m)
      LA.ds.add_sub(x, rem, LA.ds.le_trans(x, m, rem, LA.ds.min_le_r(h, m), LA.ds.min_le_r(p, rem)))
    case Sr.Skip{w}:
      {==}

def kc.pair(+i: Nat, +w: Sr.Reason, +f: Sr.Form, +p: Nat, +rem: Nat) -> {(Sr.kept(Sr.Ent{i, Sr.Skip{w}}, p, rem), Nat.add(Sr.kept(Sr.Ent{i, f}, p, rem), Sr.left(Sr.Ent{i, f}, p, rem))) == (0n, rem) : Nat & Nat}:
  %kc.sum(i, f, p, rem) : {(0n, Nat.add(Sr.kept(Sr.Ent{i, f}, p, rem), Sr.left(Sr.Ent{i, f}, p, rem))) == (0n, _) : Nat & Nat}
  {==}

def DocSearch.grep_kept_caps(i, h, big, w, f, p, rem):
  (kc.caps(h, p, rem), kc.pair(i, w, f, p, rem))
