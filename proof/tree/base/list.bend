# eukhe: lemmas the proofs of area tree share: list

import Base
import ../../../bend/tree.bend as Tr
import ../../base/bool.bend as LBool
import ../../base/logic/bool.bend as LLogicBool
import ./logic.bend as LALogic

def pt.app_snoc(A: List<&2, Tr.Ent>, +e: Tr.Ent, +C: List<&2, Tr.Ent>) -> {List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, A, [e]), C) == List.append(&2, Tr.Ent, A, e <> C) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, l => a <> l, List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, r, [e]), C), List.append(&2, Tr.Ent, r, e <> C), pt.app_snoc(r, e, C))

def pt.cov_app(A: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +g: List<&2, Nat>, +ca: {LALogic.pt.cov(A, b, g) == True{} : Bool}, +cc: {LALogic.pt.cov(C, b, g) == True{} : Bool}) -> {LALogic.pt.cov(List.append(&2, Tr.Ent, A, C), b, g) == True{} : Bool}:
  match A:
    case Nil{}:
      cc
    case +a <> +r:
      +i = Bool.or(Tr.has(b, Tr.Ent.k(a)), Tr.elem(g, Tr.Ent.k(a)))
      LBool.tree.pt.and_t(i, LALogic.pt.cov(List.append(&2, Tr.Ent, r, C), b, g), LLogicBool.tree.pt.and_l(i, LALogic.pt.cov(r, b, g), ca), pt.cov_app(r, C, b, g, LLogicBool.tree.pt.and_r(i, LALogic.pt.cov(r, b, g), ca), cc))

def tc.app_assoc(a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +c: List<&2, Tr.Ent>) -> {List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, a, b), c) == List.append(&2, Tr.Ent, a, List.append(&2, Tr.Ent, b, c)) : List<&2, Tr.Ent>}:
  match a:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => h <> ys, List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, t, b), c), List.append(&2, Tr.Ent, t, List.append(&2, Tr.Ent, b, c)), tc.app_assoc(t, b, c))

def tc.ple_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +pa: {LALogic.tc.ple(A, b) == True{} : Bool}, +pb: {LALogic.tc.ple(B, b) == True{} : Bool}) -> {LALogic.tc.ple(List.append(&2, Tr.Ent, A, B), b) == True{} : Bool}:
  match A:
    case Nil{}:
      pb
    case +e <> +r:
      LBool.tree.pt.and_t(Nat.is_ge(b, Tr.Ent.p(e)), LALogic.tc.ple(List.append(&2, Tr.Ent, r, B), b), LLogicBool.tree.pt.and_l(Nat.is_ge(b, Tr.Ent.p(e)), LALogic.tc.ple(r, b), pa), tc.ple_app(r, B, b, LLogicBool.tree.pt.and_r(Nat.is_ge(b, Tr.Ent.p(e)), LALogic.tc.ple(r, b), pa), pb))

def tc.fx_at_app(c: Bool, +e: Tr.Ent, +X: List<&2, Tr.Ent>, +Y: List<&2, Tr.Ent>) -> {List.append(&2, Tr.Ent, LALogic.tc.fx.at(c, e, X), Y) == LALogic.tc.fx.at(c, e, List.append(&2, Tr.Ent, X, Y)) : List<&2, Tr.Ent>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def tc.fx_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +x: Nat) -> {LALogic.tc.fx(List.append(&2, Tr.Ent, A, B), x) == List.append(&2, Tr.Ent, LALogic.tc.fx(A, x), LALogic.tc.fx(B, x)) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      {==}
    case +e <> +r:
      +c = Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x)))
      +ih = tc.fx_app(r, B, x)
      %Equal.sym(List<&2, Tr.Ent>, LALogic.tc.fx(List.append(&2, Tr.Ent, r, B), x), List.append(&2, Tr.Ent, LALogic.tc.fx(r, x), LALogic.tc.fx(B, x)), ih) : {LALogic.tc.fx.at(c, e, _) == List.append(&2, Tr.Ent, LALogic.tc.fx.at(c, e, LALogic.tc.fx(r, x)), LALogic.tc.fx(B, x)) : List<&2, Tr.Ent>}
      Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, LALogic.tc.fx.at(c, e, LALogic.tc.fx(r, x)), LALogic.tc.fx(B, x)), LALogic.tc.fx.at(c, e, List.append(&2, Tr.Ent, LALogic.tc.fx(r, x), LALogic.tc.fx(B, x))), tc.fx_at_app(c, e, LALogic.tc.fx(r, x), LALogic.tc.fx(B, x)))

def tc.app_nil_rec(xs: List<&2, Tr.Rec>) -> {List.append(&2, Tr.Rec, xs, Nil{}) == xs : List<&2, Tr.Rec>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Tr.Rec>, List<&2, Tr.Rec>, ys => h <> ys, List.append(&2, Tr.Rec, t, Nil{}), t, tc.app_nil_rec(t))

def tc.rev_app(xs: List<&2, Tr.Rec>, +a: List<&2, Tr.Rec>, +b: List<&2, Tr.Rec>) -> {List.reverse.go(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, xs, a), b) == List.reverse.go(&2, Tr.Rec, a, List.append(&2, Tr.Rec, xs, b)) : List<&2, Tr.Rec>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      tc.rev_app(t, h <> a, b)

def tc.rev_rev(+xs: List<&2, Tr.Rec>) -> {List.reverse(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, xs, Nil{})) == xs : List<&2, Tr.Rec>}:
  Equal.trans(List<&2, Tr.Rec>, List.reverse.go(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, xs, Nil{}), Nil{}), List.append(&2, Tr.Rec, xs, Nil{}), xs, tc.rev_app(xs, Nil{}, Nil{}), tc.app_nil_rec(xs))

def pd.lt_all_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +m: Nat, +ha: {LALogic.pd.lt_all(A, m) == True{} : Bool}, hb: {LALogic.pd.lt_all(B, m) == True{} : Bool}) -> {LALogic.pd.lt_all(List.append(&2, Tr.Ent, A, B), m) == True{} : Bool}:
  match A:
    case Nil{}:
      hb
    case +e <> +r:
      LBool.tree.pt.and_t(Nat.is_lt(Tr.Ent.k(e), m), LALogic.pd.lt_all(List.append(&2, Tr.Ent, r, B), m), LLogicBool.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(e), m), LALogic.pd.lt_all(r, m), ha), pd.lt_all_app(r, B, m, LLogicBool.tree.pt.and_r(Nat.is_lt(Tr.Ent.k(e), m), LALogic.pd.lt_all(r, m), ha), hb))

def pt.look_app(xs: List<&2, Tr.Op>, +ys: List<&2, Tr.Op>, +m: Maybe<&2, Tr.Ent>, +x: Nat) -> {LALogic.pt.look(List.append(&2, Tr.Op, xs, ys), m, x) == LALogic.pt.look(ys, LALogic.pt.look(xs, m, x), x) : Maybe<&2, Tr.Ent>}:
  match xs:
    case Nil{}:
      {==}
    case +o <> +r:
      pt.look_app(r, ys, LALogic.pt.upd(o, m, x), x)
