# eukhe: the proof of LAW gate_refusal_names_an_effect
#
# PROOF: not a yes, so the answer test is False and the auto test failed
# (pgr.no); a failed auto test over a list names the first effect whose
# bound or membership test fails (pgr.split, by induction on the list,
# carrying the tail's answer as a function of its premise); the model's
# membership is Base's (pg.elem_contains).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/gate.bend as PathPolicyGate
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA
import ./gate_unasked_only_granted.bend as PGateUnaskedOnlyGranted

# es splits at an effect that is not below 7 or not in the auto set
def pgr.Split(auto: List<&2, Nat>, es: List<&2, Nat>) -> Type:
  &xs: List<&2, Nat> -> &e: Nat -> &ys: List<&2, Nat> -> ({es == List.append(&2, Nat, xs, e <> ys) : List<&2, Nat>} & {Bool.and(Nat.is_lt(e, 7n), List.contains(~Nat, ~Nat.is_eq, auto, e)) == False{} : Bool})

# a or b fails: both fail
def pgr.or_f(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LLogicLogic.pp.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# the head's tests failed: the split is at the head
def pgr.here(+auto: List<&2, Nat>, +x: Nat, +rest: List<&2, Nat>, h: {Bool.and(Nat.is_lt(x, 7n), Tl.elem(auto, x)) == False{} : Bool}) -> pgr.Split(auto, x <> rest):
  +h2 = Equal.trans(Bool, Bool.and(Nat.is_lt(x, 7n), List.contains(~Nat, ~Nat.is_eq, auto, x)), Bool.and(Nat.is_lt(x, 7n), Tl.elem(auto, x)), False{}, Equal.cong(Bool, Bool, z => Bool.and(Nat.is_lt(x, 7n), z), List.contains(~Nat, ~Nat.is_eq, auto, x), Tl.elem(auto, x), Equal.sym(Bool, Tl.elem(auto, x), List.contains(~Nat, ~Nat.is_eq, auto, x), PGateUnaskedOnlyGranted.pg.elem_contains(auto, x))), h)
  (Nil{}, (x, (rest, ({==}, h2))))

# the split of the tail, one effect in front
def pgr.cons(+auto: List<&2, Nat>, +x: Nat, -rest: List<&2, Nat>, s: pgr.Split(auto, rest)) -> pgr.Split(auto, x <> rest):
  match s:
    case (+xs, t):
      match t:
        case (+e, u):
          match u:
            case (+ys, v):
              (pe, pf) = v
              (x <> xs, (e, (ys, (Equal.cong(List<&2, Nat>, List<&2, Nat>, z => x <> z, rest, List.append(&2, Nat, xs, e <> ys), pe), pf))))

# one step, by the head's bound g, the head's membership m and the tail's
# auto test r
def pgr.at(g: Bool, m: Bool, r: Bool, +auto: List<&2, Nat>, +x: Nat, +rest: List<&2, Nat>, eg: {Nat.is_lt(x, 7n) == g : Bool}, er: {Pp.allows(auto, rest) == r : Bool}, em: {Tl.elem(auto, x) == m : Bool}, h: {Bool.and(g, Bool.and(r, m)) == False{} : Bool}, ih: {Pp.allows(auto, rest) == False{} : Bool} -> pgr.Split(auto, rest)) -> pgr.Split(auto, x <> rest):
  match g:
    case False{}:
      pgr.here(auto, x, rest, Equal.cong(Bool, Bool, z => Bool.and(z, Tl.elem(auto, x)), Nat.is_lt(x, 7n), False{}, eg))
    case True{}:
      match m:
        case False{}:
          pgr.here(auto, x, rest, Equal.trans(Bool, Bool.and(Nat.is_lt(x, 7n), Tl.elem(auto, x)), Bool.and(True{}, False{}), False{}, Equal.trans(Bool, Bool.and(Nat.is_lt(x, 7n), Tl.elem(auto, x)), Bool.and(True{}, Tl.elem(auto, x)), Bool.and(True{}, False{}), Equal.cong(Bool, Bool, z => Bool.and(z, Tl.elem(auto, x)), Nat.is_lt(x, 7n), True{}, eg), Equal.cong(Bool, Bool, z => Bool.and(True{}, z), Tl.elem(auto, x), False{}, em)), {==}))
        case True{}:
          match r:
            case True{}:
              LLogicLogic.pp.absurd(pgr.Split(auto, x <> rest), h)
            case False{}:
              pgr.cons(auto, x, rest, ih(er))

# a failed auto test names a failing effect
def pgr.split(+auto: List<&2, Nat>, es: List<&2, Nat>) -> {Pp.allows(auto, es) == False{} : Bool} -> pgr.Split(auto, es):
  match es:
    case Nil{}:
      h => LLogicLogic.pp.absurd(pgr.Split(auto, Nil{}), h)
    case +x <> +rest:
      h => pgr.at(Nat.is_lt(x, 7n), Tl.elem(auto, x), Pp.allows(auto, rest), auto, x, rest, {==}, {==}, {==}, h, pgr.split(auto, rest))

def PathPolicyGate.gate_refusal_names_an_effect(c, a, auto, ans, no, refused):
  +es = Pp.effs(c, a)
  pgr.split(auto, es)(pgr.or_f(Pp.allows(auto, es), Pp.Ans.yes(ans), refused))
