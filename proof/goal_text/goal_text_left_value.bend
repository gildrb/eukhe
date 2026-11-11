# eukhe: the proof of LAW goal_text_left_value
#
# PROOF: canon of digit chars is the digits without leading zeros
# (lv.canon_D), worth as much (lv.V_cn). The code's `below` on them is
# the comparison of lengths, then of digits in order (lv.below_D); on
# canonical digits it is true only when the budget is worth at most the
# tokens used (lv.below_true): then the answer `0` reads back as 0, the
# saturated difference. Else the tokens used are worth at most the budget
# and have no more digits (lv.below_false); the code subtracts the
# reversed digits with a borrow (lv.sub_go), and the digits it answers
# plus the tokens used are worth the budget plus 10^n times the borrow
# left (lv.sub_value), which is 0 (lv.nob: the answer is worth less than
# 10^n, lv.L_bound); reversed and canon, the answer reads back as that
# difference (lv.rev_D, lv.read_D, lv.V_rev). Lemmas:
# proof/goal_text/goal_text_left_value/.

import Base
import ../../bend/goal_text.bend as Gt
import ../../laws/base.bend as LawsBase
import ../../laws/goal_text.bend as GoalText
import ./goal_text_left_value/nat.bend as LN
import ./goal_text_left_value/sub.bend as LS
import ./goal_text_left_value/value.bend as LV
import ./goal_text_left_value/compare.bend as LC

def lvf.le2(-a: Nat, -a2: Nat, -b: Nat, -b2: Nat, ea: {a2 == a : Nat}, eb: {b2 == b : Nat}, h: {Nat.is_le(a2, b2) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  %ea : {Nat.is_le(_, b) == True{} : Bool}
  %eb : {Nat.is_le(a2, _) == True{} : Bool}
  h

def lvf.at(+B: List<&2, Nat>, +U: List<&2, Nat>, z: Bool, +ez: {LC.lv.below(B, U) == z : Bool}, +hB: {LawsBase.wire_digits_all(B) == True{} : Bool}, +hU: {LawsBase.wire_digits_all(U) == True{} : Bool}, +okB: {LV.lv.ok(B) == True{} : Bool}, +okU: {LV.lv.ok(U) == True{} : Bool}) -> {GoalText.gt_read(Gt.left.of(z, LawsBase.wire_digit_chars(B, ""), LawsBase.wire_digit_chars(U, ""))) == Some{Nat.sub(GoalText.gt_value(B), GoalText.gt_value(U))} : Maybe<&2, Nat>}:
  match z:
    case True{}:
      +DB = LawsBase.wire_digit_chars(B, "")
      +DU = LawsBase.wire_digit_chars(U, "")
      +VB = GoalText.gt_value(B)
      +VU = GoalText.gt_value(U)
      %Equal.sym(Nat, Nat.sub(VB, VU), 0n, LN.lv.sub_le(VB, VU, LC.lv.below_true(B, U, hB, hU, okB, okU, ez))) : {GoalText.gt_read(Gt.left.of(True{}, DB, DU)) == Some{_} : Maybe<&2, Nat>}
      {==}
    case False{}:
      +DB = LawsBase.wire_digit_chars(B, "")
      +DU = LawsBase.wire_digit_chars(U, "")
      +VB = GoalText.gt_value(B)
      +VU = GoalText.gt_value(U)
      +rB = LV.lv.lrev(B, Nil{})
      +rU = LV.lv.lrev(U, Nil{})
      +hrB = LV.lv.rev_digits(B, Nil{}, hB, {==})
      +hrU = LV.lv.rev_digits(U, Nil{}, hU, {==})
      +hv = LS.lv.fst({Nat.is_le(VU, VB) == True{} : Bool}, {Nat.is_le(List.length(&2, Nat, U), List.length(&2, Nat, B)) == True{} : Bool}, LC.lv.below_false(B, U, hB, hU, okB, okU, ez))
      +hl = LS.lv.snd({Nat.is_le(VU, VB) == True{} : Bool}, {Nat.is_le(List.length(&2, Nat, U), List.length(&2, Nat, B)) == True{} : Bool}, LC.lv.below_false(B, U, hB, hU, okB, okU, ez))
      +hl2 = lvf.le2(List.length(&2, Nat, rU), List.length(&2, Nat, U), List.length(&2, Nat, rB), List.length(&2, Nat, B), Equal.sym(Nat, List.length(&2, Nat, rU), List.length(&2, Nat, U), LV.lv.rev_len0(U)), Equal.sym(Nat, List.length(&2, Nat, rB), List.length(&2, Nat, B), LV.lv.rev_len0(B)), hl)
      +hu2 = lvf.le2(LS.lv.L(rU), VU, LS.lv.L(rB), VB, Equal.sym(Nat, LS.lv.L(rU), VU, LV.lv.L_rev(U)), Equal.sym(Nat, LS.lv.L(rB), VB, LV.lv.L_rev(B)), hv)
      +res = LS.lv.sl(rB, rU, 0n)
      +hres = LS.lv.sl_digits(rB, rU, 0n, hrB, hrU, {==})
      +P = LS.lv.p10(List.length(&2, Nat, rB))
      +K = LS.lv.sub_value(rB, rU, 0n, hrB, hrU, {==}, hl2)
      +hb = lvf.le2(1n+LS.lv.L(res), 1n+LS.lv.L(res), P, LS.lv.p10(List.length(&2, Nat, res)), {==}, Equal.cong(Nat, Nat, w => LS.lv.p10(w), List.length(&2, Nat, res), List.length(&2, Nat, rB), LS.lv.sl_len(rB, rU, 0n)), LS.lv.L_bound(res, hres))
      +nobv = LS.lv.nob(LS.lv.L(res), LS.lv.L(rU), LS.lv.L(rB), P, LS.lv.bo(rB, rU, 0n), K, hb, hu2, LS.lv.bo_le(rB, rU, 0n, {==}))
      +hrr = LV.lv.rev_digits(res, Nil{}, hres, {==})
      +rr = LV.lv.lrev(res, Nil{})
      %Equal.sym(String, String.reverse.go(DB, LawsBase.wire_digit_chars(Nil{}, "")), LawsBase.wire_digit_chars(rB, ""), LV.lv.rev_D(B, Nil{})) : {GoalText.gt_read(Gt.canon(String.reverse(Gt.sub.go(_, String.reverse(DU), 0n)))) == Some{Nat.sub(VB, VU)} : Maybe<&2, Nat>}
      %Equal.sym(String, String.reverse.go(DU, LawsBase.wire_digit_chars(Nil{}, "")), LawsBase.wire_digit_chars(rU, ""), LV.lv.rev_D(U, Nil{})) : {GoalText.gt_read(Gt.canon(String.reverse(Gt.sub.go(LawsBase.wire_digit_chars(rB, ""), _, 0n)))) == Some{Nat.sub(VB, VU)} : Maybe<&2, Nat>}
      %Equal.sym(String, Gt.sub.go(LS.lv.D(rB), LS.lv.D(rU), 0n), LS.lv.D(res), LS.lv.sub_go(rB, rU, 0n, hrB, hrU, {==})) : {GoalText.gt_read(Gt.canon(String.reverse(_))) == Some{Nat.sub(VB, VU)} : Maybe<&2, Nat>}
      %Equal.sym(String, String.reverse.go(LawsBase.wire_digit_chars(res, ""), LawsBase.wire_digit_chars(Nil{}, "")), LawsBase.wire_digit_chars(rr, ""), LV.lv.rev_D(res, Nil{})) : {GoalText.gt_read(Gt.canon(_)) == Some{Nat.sub(VB, VU)} : Maybe<&2, Nat>}
      %Equal.sym(String, Gt.canon(LawsBase.wire_digit_chars(rr, "")), LawsBase.wire_digit_chars(LV.lv.cn(rr), ""), LV.lv.canon_D(rr, hrr)) : {GoalText.gt_read(_) == Some{Nat.sub(VB, VU)} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, GoalText.gt_read(LawsBase.wire_digit_chars(LV.lv.cn(rr), "")), Some{GoalText.gt_value(LV.lv.cn(rr))}, LV.lv.read_D(LV.lv.cn(rr), LV.lv.cn_digits(rr, hrr), LV.lv.cn_ok(rr))) : {_ == Some{Nat.sub(VB, VU)} : Maybe<&2, Nat>}
      %Equal.sym(Nat, GoalText.gt_value(LV.lv.cn(rr)), GoalText.gt_value(rr), LV.lv.V_cn(rr)) : {Some{_} == Some{Nat.sub(VB, VU)} : Maybe<&2, Nat>}
      %Equal.sym(Nat, GoalText.gt_value(rr), LS.lv.L(res), LV.lv.V_rev(res)) : {Some{_} == Some{Nat.sub(VB, VU)} : Maybe<&2, Nat>}
      %LV.lv.L_rev(B) : {Some{LS.lv.L(res)} == Some{Nat.sub(_, VU)} : Maybe<&2, Nat>}
      %LV.lv.L_rev(U) : {Some{LS.lv.L(res)} == Some{Nat.sub(LS.lv.L(rB), _)} : Maybe<&2, Nat>}
      Equal.cong(Nat, Maybe<&2, Nat>, w => Some{w}, LS.lv.L(res), Nat.sub(LS.lv.L(rB), LS.lv.L(rU)), Equal.sym(Nat, Nat.sub(LS.lv.L(rB), LS.lv.L(rU)), LS.lv.L(res), nobv))

def GoalText.goal_text_left_value(ds, es, hd0, he0):
  +hd = hd0
  +he = he0
  +B = LV.lv.cn(ds)
  +U = LV.lv.cn(es)
  +DE = LawsBase.wire_digit_chars(es, "")
  +DB = LawsBase.wire_digit_chars(B, "")
  +DU = LawsBase.wire_digit_chars(U, "")
  +hB = LV.lv.cn_digits(ds, hd)
  +hU = LV.lv.cn_digits(es, he)
  %Equal.sym(String, Gt.canon(LawsBase.wire_digit_chars(ds, "")), DB, LV.lv.canon_D(ds, hd)) : {GoalText.gt_read(Gt.left.of(Gt.below(_, Gt.canon(DE)), _, Gt.canon(DE))) == Some{Nat.sub(GoalText.gt_value(ds), GoalText.gt_value(es))} : Maybe<&2, Nat>}
  %Equal.sym(String, Gt.canon(DE), DU, LV.lv.canon_D(es, he)) : {GoalText.gt_read(Gt.left.of(Gt.below(DB, _), DB, _)) == Some{Nat.sub(GoalText.gt_value(ds), GoalText.gt_value(es))} : Maybe<&2, Nat>}
  %LV.lv.V_cn(ds) : {GoalText.gt_read(Gt.left.of(Gt.below(DB, DU), DB, DU)) == Some{Nat.sub(_, GoalText.gt_value(es))} : Maybe<&2, Nat>}
  %LV.lv.V_cn(es) : {GoalText.gt_read(Gt.left.of(Gt.below(DB, DU), DB, DU)) == Some{Nat.sub(GoalText.gt_value(B), _)} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Gt.below(DB, DU), LC.lv.below(B, U), LC.lv.below_D(B, U, hB, hU)) : {GoalText.gt_read(Gt.left.of(_, DB, DU)) == Some{Nat.sub(GoalText.gt_value(B), GoalText.gt_value(U))} : Maybe<&2, Nat>}
  lvf.at(B, U, LC.lv.below(B, U), {==}, hB, hU, LV.lv.cn_ok(ds), LV.lv.cn_ok(es))
