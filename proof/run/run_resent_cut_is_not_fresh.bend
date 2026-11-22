# eukhe: the proof of LAW run_resent_cut_is_not_fresh
#
# PROOF: a request is the same as itself (fr.is_refl), so the cut of q
# below a send of q is found (fr.cut) and that send is not fresh
# (fr.head); a log with a part that is not fresh is not fresh, whatever
# comes before (fr.pre, by induction on the entries before).

import Base
import ../../bend/run/request.bend as RnRequest
import ../../laws/run/model.bend as Run

def fr.eq_refl(+n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      fr.eq_refl(m)

def fr.is_refl(q: RnRequest.Req) -> {RnRequest.Req.is(q, q) == True{} : Bool}:
  match q:
    case RnRequest.Req{+c, +m}:
      %Equal.sym(Bool, Nat.is_eq(c, c), True{}, fr.eq_refl(c)) : {Bool.and(_, Nat.is_eq(m, m)) == True{} : Bool}
      fr.eq_refl(m)

def fr.or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def fr.and_false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the cut of q is found below any entries
def fr.cut(+q: RnRequest.Req, ys: List<&2, RnRequest.Sent>, +zs: List<&2, RnRequest.Sent>) -> {RnRequest.cut_in(q, List.append(&2, RnRequest.Sent, ys, RnRequest.Cut{q} <> zs)) == True{} : Bool}:
  match ys:
    case Nil{}:
      %Equal.sym(Bool, RnRequest.Req.is(q, q), True{}, fr.is_refl(q)) : {Bool.or(_, RnRequest.cut_in(q, zs)) == True{} : Bool}
      {==}
    case y <> +rest:
      match y:
        case RnRequest.Sent{p}:
          fr.cut(q, rest, zs)
        case RnRequest.Cut{+p}:
          %Equal.sym(Bool, RnRequest.cut_in(q, List.append(&2, RnRequest.Sent, rest, RnRequest.Cut{q} <> zs)), True{}, fr.cut(q, rest, zs)) : {Bool.or(RnRequest.Req.is(p, q), _) == True{} : Bool}
          fr.or_true(RnRequest.Req.is(p, q))

# a send of q above a cut of q is not fresh
def fr.head(+q: RnRequest.Req, +ys: List<&2, RnRequest.Sent>, +zs: List<&2, RnRequest.Sent>) -> {RnRequest.fresh(RnRequest.Sent{q} <> List.append(&2, RnRequest.Sent, ys, RnRequest.Cut{q} <> zs)) == False{} : Bool}:
  %Equal.sym(Bool, RnRequest.cut_in(q, List.append(&2, RnRequest.Sent, ys, RnRequest.Cut{q} <> zs)), True{}, fr.cut(q, ys, zs)) : {Bool.and(Bool.not(_), RnRequest.fresh(List.append(&2, RnRequest.Sent, ys, RnRequest.Cut{q} <> zs))) == False{} : Bool}
  {==}

# entries before a log that is not fresh leave it not fresh
def fr.pre(xs: List<&2, RnRequest.Sent>, +rest: List<&2, RnRequest.Sent>, h: {RnRequest.fresh(rest) == False{} : Bool}) -> {RnRequest.fresh(List.append(&2, RnRequest.Sent, xs, rest)) == False{} : Bool}:
  match xs:
    case Nil{}:
      h
    case x <> +t:
      match x:
        case RnRequest.Sent{+p}:
          %Equal.sym(Bool, RnRequest.fresh(List.append(&2, RnRequest.Sent, t, rest)), False{}, fr.pre(t, rest, h)) : {Bool.and(Bool.not(RnRequest.cut_in(p, List.append(&2, RnRequest.Sent, t, rest))), _) == False{} : Bool}
          fr.and_false(Bool.not(RnRequest.cut_in(p, List.append(&2, RnRequest.Sent, t, rest))))
        case RnRequest.Cut{p}:
          fr.pre(t, rest, h)

def Run.run_resent_cut_is_not_fresh(xs, q, ys, zs):
  fr.pre(xs, RnRequest.Sent{q} <> List.append(&2, RnRequest.Sent, ys, RnRequest.Cut{q} <> zs), fr.head(q, ys, zs))
