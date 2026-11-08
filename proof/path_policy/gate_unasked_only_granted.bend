# eukhe: the proof of LAW gate_unasked_only_granted
#
# PROOF: not a yes, so the answer test is False and the auto test ran
# (pgu.ran); the auto test over xs ++ e::ys holds e's two tests
# (pgu.pick, by induction on xs); the model's membership is Base's
# (pg.elem_contains).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/gate.bend as PathPolicyGate
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# Empty proves anything
def pg.never(-A: Type, e: Empty) -> A:
  match e:

# an answer that is not a yes answers False to the model's yes test
def pg.no_yes(ans: Pp.Ans, no: {ans != Pp.Yes{} : Pp.Ans}) -> {Pp.Ans.yes(ans) == False{} : Bool}:
  match ans:
    case Pp.Yes{}:
      pg.never({True{} == False{} : Bool}, no({==}))
    case Pp.No{}:
      {==}
    case Pp.Gone{}:
      {==}

# one step of Base's membership, by the head test b
def pg.ec_step(b: Bool, -rest: List<&2, Nat>, -x: Nat, ih: {Tl.elem(rest, x) == List.contains(~Nat, ~Nat.is_eq, rest, x) : Bool}) -> {Bool.or(b, Tl.elem(rest, x)) == List.any.if(u => List.contains(~Nat, ~Nat.is_eq, rest, x), b) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the model's membership is Base's
def pg.elem_contains(xs: List<&2, Nat>, +x: Nat) -> {Tl.elem(xs, x) == List.contains(~Nat, ~Nat.is_eq, xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      pg.ec_step(Nat.is_eq(y, x), rest, x, pg.elem_contains(rest, x))

# a or b holds and b does not: a holds
def pgu.or_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}, nb: {b == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LA.pp.absurdF({False{} == True{} : Bool}, Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, nb), h))

# g and (r and m) gives g and m
def pgu.and_gm(g: Bool, r: Bool, -m: Bool, h: {Bool.and(g, Bool.and(r, m)) == True{} : Bool}) -> {Bool.and(g, m) == True{} : Bool}:
  match g:
    case True{}:
      match r:
        case True{}:
          h
        case False{}:
          LA.pp.absurdF({Bool.and(True{}, m) == True{} : Bool}, h)
    case False{}:
      LA.pp.absurdF({Bool.and(False{}, m) == True{} : Bool}, h)

# g and (r and m) gives r
def pgu.and_r(g: Bool, r: Bool, -m: Bool, h: {Bool.and(g, Bool.and(r, m)) == True{} : Bool}) -> {r == True{} : Bool}:
  match g:
    case True{}:
      match r:
        case True{}:
          {==}
        case False{}:
          LA.pp.absurdF({False{} == True{} : Bool}, h)
    case False{}:
      LA.pp.absurdF({r == True{} : Bool}, h)

# the auto test over xs ++ e::ys holds e's two tests
def pgu.pick(+auto: List<&2, Nat>, xs: List<&2, Nat>, +e: Nat, +ys: List<&2, Nat>, h: {Pp.allows(auto, List.append(&2, Nat, xs, e <> ys)) == True{} : Bool}) -> {Bool.and(Nat.is_lt(e, 6n), Tl.elem(auto, e)) == True{} : Bool}:
  match xs:
    case Nil{}:
      pgu.and_gm(Nat.is_lt(e, 6n), Pp.allows(auto, ys), Tl.elem(auto, e), h)
    case +x <> +rest:
      pgu.pick(auto, rest, e, ys, pgu.and_r(Nat.is_lt(x, 6n), Pp.allows(auto, List.append(&2, Nat, rest, e <> ys)), Tl.elem(auto, x), h))

def PathPolicyGate.gate_unasked_only_granted(c, a, auto, ans, xs, e, ys, no, eff, ran):
  +ny = pg.no_yes(ans, no)
  +al = pgu.or_l(Pp.allows(auto, Pp.effs(c, a)), Pp.Ans.yes(ans), ran, ny)
  +al2 = Equal.trans(Bool, Pp.allows(auto, List.append(&2, Nat, xs, e <> ys)), Pp.allows(auto, Pp.effs(c, a)), True{}, Equal.cong(List<&2, Nat>, Bool, z => Pp.allows(auto, z), List.append(&2, Nat, xs, e <> ys), Pp.effs(c, a), Equal.sym(List<&2, Nat>, Pp.effs(c, a), List.append(&2, Nat, xs, e <> ys), eff)), al)
  %pg.elem_contains(auto, e) : {Bool.and(Nat.is_lt(e, 6n), _) == True{} : Bool}
  pgu.pick(auto, xs, e, ys, al2)
