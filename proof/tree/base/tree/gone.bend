# eukhe: lemmas the proofs of area tree share: tree/gone

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/bool.bend as LBool
import ../../../base/logic/bool.bend as LLogicBool
import ../bool.bend as LABool
import ../logic.bend as LALogic
import ./above.bend as LATreeAbove
import ./elem.bend as LATreeElem

# a delete's walk over the nodes it may remove drops the keys of the walk
# over every node
def tc.drops_fx(s: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +eh: {Tr.gone.at(s, gone) == hit : Bool}, +x: Nat, +ng: {LALogic.tc.nall(gone, x) == True{} : Bool}, +g: {LALogic.tc.gb(gone, x, s) == True{} : Bool}, +st: {Tr.sorted(s) == True{} : Bool}, +dk: {LALogic.tc.desc(s) == True{} : Bool}) -> {LALogic.tc.dgo(s, gone, hit) == LALogic.tc.dgo(LALogic.tc.fx(s, x), gone, Tr.gone.at(LALogic.tc.fx(s, x), gone)) : List<&2, Nat>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      +pk = LLogicBool.tree.pt.and_l(Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)), LALogic.tc.desc(r), dk)
      +dr = LLogicBool.tree.pt.and_r(Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)), LALogic.tc.desc(r), dk)
      +sr = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
      +ar = LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
      +g1 = LATreeAbove.tc.gb_tail(gone, x, e, r, g, st)
      +g2 = LBool.tree.pt.and_t(Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Tr.above(Tr.Ent.k(e), r)), LALogic.tc.gb(gone, x, r), LABool.pt.or_tr(Nat.is_eq(Tr.Ent.k(e), x), Tr.above(Tr.Ent.k(e), r), ar), g1)
      +ih1 = tc.drops_fx(r, gone, Tr.gone.at(r, gone), {==}, x, ng, g1, sr, dr)
      LATreeElem.tc.fd_at(e, r, gone, hit, eh, x, Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), {==}, ng, g, pk, ih1, kx => tc.drops_fx(r, Tr.Ent.k(e) <> gone, Tr.gone.at(r, Tr.Ent.k(e) <> gone), {==}, x, LALogic.tc.nall_cons(Tr.Ent.k(e), gone, x, kx, ng), g2, sr, dr))
