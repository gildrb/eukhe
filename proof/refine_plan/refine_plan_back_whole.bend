# eukhe: the proof of LAW refine_plan_back_whole
#
# PROOF: one more row puts its rollback edits first (rpk.each, from the
# code's forward fold and reverse), so the rows pre, then t, roll back as
# the spec's walk over t (rpk.fold); the texts are R5's with
# String.append(id, "") == id (rpk.str_nil).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/model.bend as RefinePlan
import ../../laws/refine_plan/plan.bend as RefinePlanPlan

def rpk.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, rpk.add_zero(p))

def rpk.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), rpk.add_succ(p, b))

def rpk.app_nil(a: List<&2, Rp.Pick>) -> {List.append(&2, Rp.Pick, a, []) == a : List<&2, Rp.Pick>}:
  match a:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Rp.Pick>, List<&2, Rp.Pick>, l => h <> l, List.append(&2, Rp.Pick, t, []), t, rpk.app_nil(t))

def rpk.app_assoc(a: List<&2, Rp.Pick>, -b: List<&2, Rp.Pick>, -c: List<&2, Rp.Pick>) -> {List.append(&2, Rp.Pick, List.append(&2, Rp.Pick, a, b), c) == List.append(&2, Rp.Pick, a, List.append(&2, Rp.Pick, b, c)) : List<&2, Rp.Pick>}:
  match a:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Rp.Pick>, List<&2, Rp.Pick>, l => h <> l, List.append(&2, Rp.Pick, List.append(&2, Rp.Pick, t, b), c), List.append(&2, Rp.Pick, t, List.append(&2, Rp.Pick, b, c)), rpk.app_assoc(t, b, c))

def rpk.pick(w: Rp.Was, +i: Nat) -> {Rp.back.pick(w, i) == RefinePlanPlan.rs_pick(w, i) : List<&2, Rp.Pick>}:
  match w:
    case Rp.Was{applied, before, after}:
      match applied:
        case False{}:
          {==}
        case True{}:
          match before:
            case True{}:
              match after:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match after:
                case True{}:
                  {==}
                case False{}:
                  {==}

# a row's rollback edits (none or one) read back to front are themselves
def rpk.small(w: Rp.Was, +i: Nat) -> {List.reverse.go(&2, Rp.Pick, RefinePlanPlan.rs_pick(w, i), []) == RefinePlanPlan.rs_pick(w, i) : List<&2, Rp.Pick>}:
  match w:
    case Rp.Was{applied, before, after}:
      match applied:
        case False{}:
          {==}
        case True{}:
          match before:
            case True{}:
              match after:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match after:
                case True{}:
                  {==}
                case False{}:
                  {==}

# one more row: its edits after the earlier rows', its index their count
def rpk.fwd(xs: List<&2, Rp.Was>, +w: Rp.Was, +k: Nat) -> {Rp.back.fwd(List.append(&2, Rp.Was, xs, [w]), k) == List.append(&2, Rp.Pick, Rp.back.fwd(xs, k), Rp.back.pick(w, Nat.add(k, List.length(&2, Rp.Was, xs)))) : List<&2, Rp.Pick>}:
  match xs:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(k, 0n), k, rpk.add_zero(k)) : {Rp.back.fwd([w], k) == Rp.back.pick(w, _) : List<&2, Rp.Pick>}
      rpk.app_nil(Rp.back.pick(w, k))
    case +x <> +t:
      +P = Rp.back.pick(x, k)
      +Fw = Rp.back.fwd(t, 1n+k)
      +Q = Rp.back.pick(w, 1n+Nat.add(k, List.length(&2, Rp.Was, t)))
      %Equal.sym(List<&2, Rp.Pick>, Rp.back.fwd(List.append(&2, Rp.Was, t, [w]), 1n+k), List.append(&2, Rp.Pick, Fw, Q), rpk.fwd(t, w, 1n+k)) : {List.append(&2, Rp.Pick, P, _) == List.append(&2, Rp.Pick, List.append(&2, Rp.Pick, P, Fw), Rp.back.pick(w, Nat.add(k, 1n+List.length(&2, Rp.Was, t)))) : List<&2, Rp.Pick>}
      %Equal.sym(Nat, Nat.add(k, 1n+List.length(&2, Rp.Was, t)), 1n+Nat.add(k, List.length(&2, Rp.Was, t)), rpk.add_succ(k, List.length(&2, Rp.Was, t))) : {List.append(&2, Rp.Pick, P, List.append(&2, Rp.Pick, Fw, Q)) == List.append(&2, Rp.Pick, List.append(&2, Rp.Pick, P, Fw), Rp.back.pick(w, _)) : List<&2, Rp.Pick>}
      Equal.sym(List<&2, Rp.Pick>, List.append(&2, Rp.Pick, List.append(&2, Rp.Pick, P, Fw), Q), List.append(&2, Rp.Pick, P, List.append(&2, Rp.Pick, Fw, Q)), rpk.app_assoc(P, Fw, Q))

def rpk.rev_app(a: List<&2, Rp.Pick>, -b: List<&2, Rp.Pick>, +acc: List<&2, Rp.Pick>) -> {List.reverse.go(&2, Rp.Pick, List.append(&2, Rp.Pick, a, b), acc) == List.reverse.go(&2, Rp.Pick, b, List.reverse.go(&2, Rp.Pick, a, acc)) : List<&2, Rp.Pick>}:
  match a:
    case Nil{}:
      {==}
    case h <> t:
      rpk.rev_app(t, b, h <> acc)

def rpk.rev_out(x: List<&2, Rp.Pick>, +acc: List<&2, Rp.Pick>) -> {List.reverse.go(&2, Rp.Pick, x, acc) == List.append(&2, Rp.Pick, List.reverse.go(&2, Rp.Pick, x, []), acc) : List<&2, Rp.Pick>}:
  match x:
    case Nil{}:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, Rp.Pick>, List.reverse.go(&2, Rp.Pick, t, h <> acc), List.append(&2, Rp.Pick, List.reverse.go(&2, Rp.Pick, t, []), h <> acc), List.append(&2, Rp.Pick, List.reverse.go(&2, Rp.Pick, t, [h]), acc), rpk.rev_out(t, h <> acc), Equal.trans(List<&2, Rp.Pick>, List.append(&2, Rp.Pick, List.reverse.go(&2, Rp.Pick, t, []), h <> acc), List.append(&2, Rp.Pick, List.append(&2, Rp.Pick, List.reverse.go(&2, Rp.Pick, t, []), [h]), acc), List.append(&2, Rp.Pick, List.reverse.go(&2, Rp.Pick, t, [h]), acc), Equal.sym(List<&2, Rp.Pick>, List.append(&2, Rp.Pick, List.append(&2, Rp.Pick, List.reverse.go(&2, Rp.Pick, t, []), [h]), acc), List.append(&2, Rp.Pick, List.reverse.go(&2, Rp.Pick, t, []), h <> acc), rpk.app_assoc(List.reverse.go(&2, Rp.Pick, t, []), [h], acc)), Equal.cong(List<&2, Rp.Pick>, List<&2, Rp.Pick>, l => List.append(&2, Rp.Pick, l, acc), List.append(&2, Rp.Pick, List.reverse.go(&2, Rp.Pick, t, []), [h]), List.reverse.go(&2, Rp.Pick, t, [h]), Equal.sym(List<&2, Rp.Pick>, List.reverse.go(&2, Rp.Pick, t, [h]), List.append(&2, Rp.Pick, List.reverse.go(&2, Rp.Pick, t, []), [h]), rpk.rev_out(t, [h])))))

def rpk.each(+id: String, +xs: List<&2, Rp.Was>, +w: Rp.Was) -> {RefinePlanPlan.rs_picks(Rp.back(id, List.append(&2, Rp.Was, xs, [w]))) == List.append(&2, Rp.Pick, RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, xs)), RefinePlanPlan.rs_picks(Rp.back(id, xs))) : List<&2, Rp.Pick>}:
  +F = Rp.back.fwd(xs, 0n)
  +P = Rp.back.pick(w, List.length(&2, Rp.Was, xs))
  %Equal.sym(List<&2, Rp.Pick>, Rp.back.fwd(List.append(&2, Rp.Was, xs, [w]), 0n), List.append(&2, Rp.Pick, F, P), rpk.fwd(xs, w, 0n)) : {List.reverse.go(&2, Rp.Pick, _, []) == List.append(&2, Rp.Pick, RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, xs)), List.reverse.go(&2, Rp.Pick, F, [])) : List<&2, Rp.Pick>}
  %Equal.sym(List<&2, Rp.Pick>, List.reverse.go(&2, Rp.Pick, List.append(&2, Rp.Pick, F, P), []), List.reverse.go(&2, Rp.Pick, P, List.reverse.go(&2, Rp.Pick, F, [])), rpk.rev_app(F, P, [])) : {_ == List.append(&2, Rp.Pick, RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, xs)), List.reverse.go(&2, Rp.Pick, F, [])) : List<&2, Rp.Pick>}
  %Equal.sym(List<&2, Rp.Pick>, List.reverse.go(&2, Rp.Pick, P, List.reverse.go(&2, Rp.Pick, F, [])), List.append(&2, Rp.Pick, List.reverse.go(&2, Rp.Pick, P, []), List.reverse.go(&2, Rp.Pick, F, [])), rpk.rev_out(P, List.reverse.go(&2, Rp.Pick, F, []))) : {_ == List.append(&2, Rp.Pick, RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, xs)), List.reverse.go(&2, Rp.Pick, F, [])) : List<&2, Rp.Pick>}
  %Equal.sym(List<&2, Rp.Pick>, P, RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, xs)), rpk.pick(w, List.length(&2, Rp.Was, xs))) : {List.append(&2, Rp.Pick, List.reverse.go(&2, Rp.Pick, _, []), List.reverse.go(&2, Rp.Pick, F, [])) == List.append(&2, Rp.Pick, RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, xs)), List.reverse.go(&2, Rp.Pick, F, [])) : List<&2, Rp.Pick>}
  %Equal.sym(List<&2, Rp.Pick>, List.reverse.go(&2, Rp.Pick, RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, xs)), []), RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, xs)), rpk.small(w, List.length(&2, Rp.Was, xs))) : {List.append(&2, Rp.Pick, _, List.reverse.go(&2, Rp.Pick, F, [])) == List.append(&2, Rp.Pick, RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, xs)), List.reverse.go(&2, Rp.Pick, F, [])) : List<&2, Rp.Pick>}
  {==}

# Rollback edits, row by row
# --------------------------

def rpk.len_snoc(xs: List<&2, Rp.Was>, -w: Rp.Was) -> {List.length(&2, Rp.Was, List.append(&2, Rp.Was, xs, [w])) == 1n+List.length(&2, Rp.Was, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Rp.Was, List.append(&2, Rp.Was, t, [w])), 1n+List.length(&2, Rp.Was, t), rpk.len_snoc(t, w))

def rpk.was_nil(a: List<&2, Rp.Was>) -> {List.append(&2, Rp.Was, a, []) == a : List<&2, Rp.Was>}:
  match a:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Rp.Was>, List<&2, Rp.Was>, l => h <> l, List.append(&2, Rp.Was, t, []), t, rpk.was_nil(t))

def rpk.was_snoc(a: List<&2, Rp.Was>, -w: Rp.Was, -t: List<&2, Rp.Was>) -> {List.append(&2, Rp.Was, List.append(&2, Rp.Was, a, [w]), t) == List.append(&2, Rp.Was, a, w <> t) : List<&2, Rp.Was>}:
  match a:
    case Nil{}:
      {==}
    case h <> r:
      Equal.cong(List<&2, Rp.Was>, List<&2, Rp.Was>, l => h <> l, List.append(&2, Rp.Was, List.append(&2, Rp.Was, r, [w]), t), List.append(&2, Rp.Was, r, w <> t), rpk.was_snoc(r, w, t))

def rpk.step(+id: String, +pre: List<&2, Rp.Was>, +w: Rp.Was, +r: List<&2, Rp.Was>) -> {RefinePlanPlan.rs_back.go(r, List.length(&2, Rp.Was, List.append(&2, Rp.Was, pre, [w])), RefinePlanPlan.rs_picks(Rp.back(id, List.append(&2, Rp.Was, pre, [w])))) == RefinePlanPlan.rs_back.go(r, 1n+List.length(&2, Rp.Was, pre), List.append(&2, Rp.Pick, RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, pre)), RefinePlanPlan.rs_picks(Rp.back(id, pre)))) : List<&2, Rp.Pick>}:
  +C = RefinePlanPlan.rs_back.go(r, 1n+List.length(&2, Rp.Was, pre), List.append(&2, Rp.Pick, RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, pre)), RefinePlanPlan.rs_picks(Rp.back(id, pre))))
  %Equal.sym(Nat, List.length(&2, Rp.Was, List.append(&2, Rp.Was, pre, [w])), 1n+List.length(&2, Rp.Was, pre), rpk.len_snoc(pre, w)) : {RefinePlanPlan.rs_back.go(r, _, RefinePlanPlan.rs_picks(Rp.back(id, List.append(&2, Rp.Was, pre, [w])))) == C : List<&2, Rp.Pick>}
  %Equal.sym(List<&2, Rp.Pick>, RefinePlanPlan.rs_picks(Rp.back(id, List.append(&2, Rp.Was, pre, [w]))), List.append(&2, Rp.Pick, RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, pre)), RefinePlanPlan.rs_picks(Rp.back(id, pre))), rpk.each(id, pre, w)) : {RefinePlanPlan.rs_back.go(r, 1n+List.length(&2, Rp.Was, pre), _) == C : List<&2, Rp.Pick>}
  {==}

# the rollback edits of the rows pre, then t: the spec's walk over t from
# those of pre
def rpk.fold(t: List<&2, Rp.Was>, +id: String, +pre: List<&2, Rp.Was>) -> {RefinePlanPlan.rs_picks(Rp.back(id, List.append(&2, Rp.Was, pre, t))) == RefinePlanPlan.rs_back.go(t, List.length(&2, Rp.Was, pre), RefinePlanPlan.rs_picks(Rp.back(id, pre))) : List<&2, Rp.Pick>}:
  match t:
    case Nil{}:
      %Equal.sym(List<&2, Rp.Was>, List.append(&2, Rp.Was, pre, []), pre, rpk.was_nil(pre)) : {RefinePlanPlan.rs_picks(Rp.back(id, _)) == RefinePlanPlan.rs_picks(Rp.back(id, pre)) : List<&2, Rp.Pick>}
      {==}
    case +w <> +r:
      %rpk.was_snoc(pre, w, r) : {RefinePlanPlan.rs_picks(Rp.back(id, _)) == RefinePlanPlan.rs_back.go(r, 1n+List.length(&2, Rp.Was, pre), List.append(&2, Rp.Pick, RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, pre)), RefinePlanPlan.rs_picks(Rp.back(id, pre)))) : List<&2, Rp.Pick>}
      Equal.trans(List<&2, Rp.Pick>, RefinePlanPlan.rs_picks(Rp.back(id, List.append(&2, Rp.Was, List.append(&2, Rp.Was, pre, [w]), r))), RefinePlanPlan.rs_back.go(r, List.length(&2, Rp.Was, List.append(&2, Rp.Was, pre, [w])), RefinePlanPlan.rs_picks(Rp.back(id, List.append(&2, Rp.Was, pre, [w])))), RefinePlanPlan.rs_back.go(r, 1n+List.length(&2, Rp.Was, pre), List.append(&2, Rp.Pick, RefinePlanPlan.rs_pick(w, List.length(&2, Rp.Was, pre)), RefinePlanPlan.rs_picks(Rp.back(id, pre)))), rpk.fold(r, id, List.append(&2, Rp.Was, pre, [w])), rpk.step(id, pre, w, r))

def rpk.str_nil(s: String) -> {String.append(s, "") == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, u => SCon{h, u}, String.append(t, ""), t, rpk.str_nil(t))

def rpk.whole(+id: String, +was: List<&2, Rp.Was>) -> {Rp.back(id, was) == Rp.Back{String.append("Rollback refinement ", id), String.append("Restores continual harness state snapshots from refinement ", String.append(id, ".")), "Faulty refinement edits are reverted.", String.append("Rollback ", id), RefinePlanPlan.rs_back_picks(was)} : Rp.Back}:
  %Equal.sym(String, String.append(id, ""), id, rpk.str_nil(id)) : {Rp.Back{String.append("Rollback refinement ", _), String.append("Restores continual harness state snapshots from refinement ", String.append(id, ".")), "Faulty refinement edits are reverted.", String.append("Rollback ", _), List.reverse(&2, Rp.Pick, Rp.back.fwd(was, 0n))} == Rp.Back{String.append("Rollback refinement ", id), String.append("Restores continual harness state snapshots from refinement ", String.append(id, ".")), "Faulty refinement edits are reverted.", String.append("Rollback ", id), RefinePlanPlan.rs_back_picks(was)} : Rp.Back}
  Equal.cong(List<&2, Rp.Pick>, Rp.Back, ps => Rp.Back{String.append("Rollback refinement ", id), String.append("Restores continual harness state snapshots from refinement ", String.append(id, ".")), "Faulty refinement edits are reverted.", String.append("Rollback ", id), ps}, List.reverse(&2, Rp.Pick, Rp.back.fwd(was, 0n)), RefinePlanPlan.rs_back_picks(was), rpk.fold(was, id, []))

def RefinePlanPlan.refine_plan_back_whole(id, was):
  rpk.whole(id, was)
