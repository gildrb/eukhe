# eukhe: lemmas the proofs of area tree share: tree/within

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/bool.bend as LBool
import ../../../base/logic/bool.bend as LLogicBool
import ../../../base/nat.bend as LNat
import ./above.bend as LATreeAbove
import ./get.bend as LATreeGet
import ./same.bend as LATreeSame

# a node above every node of s does not change what s holds
def pt.within_cons(s: List<&2, Tr.Ent>, +h: Tr.Ent, +r: List<&2, Tr.Ent>, +w: {Tr.within(s, r) == True{} : Bool}, +al: {Tr.above(Tr.Ent.k(h), s) == True{} : Bool}, +st: {Tr.sorted(s) == True{} : Bool}) -> {Tr.within(s, h <> r) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      +i = Tr.same(Tr.get(r, Tr.Ent.k(e)), Some{e})
      +gm = LATreeGet.pt.get_miss(h, r, Tr.Ent.k(e), LNat.pt.lt_ne(Tr.Ent.k(h), Tr.Ent.k(e), al))
      +hd = Equal.trans(Bool, Tr.same(Tr.get(h <> r, Tr.Ent.k(e)), Some{e}), i, True{}, Equal.cong(Maybe<&2, Tr.Ent>, Bool, m => Tr.same(m, Some{e}), Tr.get(h <> r, Tr.Ent.k(e)), Tr.get(r, Tr.Ent.k(e)), gm), LLogicBool.tree.pt.and_l(i, Tr.within(rest, r), w))
      LBool.tree.pt.and_t(Tr.same(Tr.get(h <> r, Tr.Ent.k(e)), Some{e}), Tr.within(rest, h <> r), hd, pt.within_cons(rest, h, r, LLogicBool.tree.pt.and_r(i, Tr.within(rest, r), w), LATreeAbove.pt.above_tail(Tr.Ent.k(h), e, rest, al, st), LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(e), rest), Tr.sorted(rest), st)))

# a sorted tree holds each of its nodes
def pt.within_self(t: List<&2, Tr.Ent>, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.within(t, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      +sr = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
      +hd = Equal.trans(Bool, Tr.same(Tr.get(h <> r, Tr.Ent.k(h)), Some{h}), Tr.same(Some{h}, Some{h}), True{}, Equal.cong(Maybe<&2, Tr.Ent>, Bool, m => Tr.same(m, Some{h}), Tr.get(h <> r, Tr.Ent.k(h)), Some{h}, LATreeGet.pt.get_head(h, r)), LATreeSame.pt.same_refl(h))
      LBool.tree.pt.and_t(Tr.same(Tr.get(h <> r, Tr.Ent.k(h)), Some{h}), Tr.within(r, h <> r), hd, pt.within_cons(r, h, r, pt.within_self(r, sr), LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st), sr))
