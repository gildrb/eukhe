# eukhe: lemmas the proofs of area tree share: tree/elem

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/logic/bool.bend as LLogicBool
import ../../../base/nat.bend as LNat
import ../bool.bend as LABool
import ../logic.bend as LALogic
import ../nat.bend as LANat

def tc.elem_none(gone: List<&2, Nat>, +x: Nat, +y: Nat, +ng: {LALogic.tc.nall(gone, x) == True{} : Bool}, +yx: {Nat.is_lt(y, x) == True{} : Bool}) -> {Tr.elem(gone, y) == False{} : Bool}:
  match gone:
    case Nil{}:
      {==}
    case +g <> +rest:
      +gx = LLogicBool.pt.not_f(Nat.is_lt(g, x), LLogicBool.tree.pt.and_l(Bool.not(Nat.is_lt(g, x)), LALogic.tc.nall(rest, x), ng))
      +ne = LNat.pt.lt_ne_r(y, g, LNat.tc.lt_le(y, x, g, yx, gx))
      %Equal.sym(Bool, Nat.is_eq(g, y), False{}, ne) : {Bool.or(_, Tr.elem(rest, y)) == False{} : Bool}
      tc.elem_none(rest, x, y, LLogicBool.tree.pt.and_r(Bool.not(Nat.is_lt(g, x)), LALogic.tc.nall(rest, x), ng), yx)

# a key that is not x is not gone, while gone holds x and keys below it
def tc.gb_elem(gone: List<&2, Nat>, +x: Nat, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +g: {LALogic.tc.gb(gone, x, e <> r) == True{} : Bool}, +kx: {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}) -> {Tr.elem(gone, Tr.Ent.k(e)) == False{} : Bool}:
  match gone:
    case Nil{}:
      {==}
    case +z <> +rest:
      +hd = LLogicBool.tree.pt.and_l(Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r)), LALogic.tc.gb(rest, x, e <> r), g)
      +tl = LLogicBool.tree.pt.and_r(Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r)), LALogic.tc.gb(rest, x, e <> r), g)
      +ne = LANat.tc.gb_hd(Nat.is_eq(z, x), z, x, Tr.Ent.k(e), {==}, hd, kx)
      %Equal.sym(Bool, Nat.is_eq(z, Tr.Ent.k(e)), False{}, ne) : {Bool.or(_, Tr.elem(rest, Tr.Ent.k(e))) == False{} : Bool}
      tc.gb_elem(rest, x, e, r, tl, kx)

def tc.fd_at(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +eh: {Tr.gone.at(e <> r, gone) == hit : Bool}, +x: Nat, c: Bool, +ec: {Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))) == c : Bool}, +ng: {LALogic.tc.nall(gone, x) == True{} : Bool}, +g: {LALogic.tc.gb(gone, x, e <> r) == True{} : Bool}, +pk: {Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)) == True{} : Bool}, +ih1: {LALogic.tc.dgo(r, gone, Tr.gone.at(r, gone)) == LALogic.tc.dgo(LALogic.tc.fx(r, x), gone, Tr.gone.at(LALogic.tc.fx(r, x), gone)) : List<&2, Nat>}, ih2: {Nat.is_lt(Tr.Ent.k(e), x) == False{} : Bool} -> {LALogic.tc.dgo(r, Tr.Ent.k(e) <> gone, Tr.gone.at(r, Tr.Ent.k(e) <> gone)) == LALogic.tc.dgo(LALogic.tc.fx(r, x), Tr.Ent.k(e) <> gone, Tr.gone.at(LALogic.tc.fx(r, x), Tr.Ent.k(e) <> gone)) : List<&2, Nat>}) -> {LALogic.tc.dgo(e <> r, gone, hit) == LALogic.tc.dgo(LALogic.tc.fx.at(c, e, LALogic.tc.fx(r, x)), gone, Tr.gone.at(LALogic.tc.fx.at(c, e, LALogic.tc.fx(r, x)), gone)) : List<&2, Nat>}:
  match c:
    case True{}:
      +G = Bool.or(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e)))
      +kx = LANat.tc.kept_ge(e, x, Nat.is_eq(Tr.Ent.k(e), x), {==}, ec, pk)
      %Equal.sym(Bool, G, hit, eh) : {LALogic.tc.dgo(e <> r, gone, hit) == LALogic.tc.dgo(e <> LALogic.tc.fx(r, x), gone, _) : List<&2, Nat>}
      LALogic.tc.dg_ge(hit, e, r, LALogic.tc.fx(r, x), gone, ih1, ih2(kx))
    case False{}:
      +ne = LALogic.pt.or_l(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x)), ec)
      +px = LALogic.tc.not_ff(Nat.is_lt(Tr.Ent.p(e), x), LALogic.pt.or_r(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x)), ec))
      +nk = tc.gb_elem(gone, x, e, r, g, ne)
      +np = tc.elem_none(gone, x, Tr.Ent.p(e), ng, px)
      +o = LABool.tc.or_ff(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e)), nk, np)
      +hf = Equal.trans(Bool, hit, Bool.or(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e))), False{}, Equal.sym(Bool, Bool.or(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e))), hit, eh), o)
      %Equal.sym(Bool, hit, False{}, hf) : {LALogic.tc.dgo(e <> r, gone, _) == LALogic.tc.dgo(LALogic.tc.fx(r, x), gone, Tr.gone.at(LALogic.tc.fx(r, x), gone)) : List<&2, Nat>}
      ih1
