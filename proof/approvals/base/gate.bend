# eukhe: lemmas the proofs of the gate laws of laws/approvals/route.bend
# share (G5.5): the step's own test of one effect is the laws' gt_allowed
# (gd.ok: `grantable` is a code below 7, `elem` is sp_has), and `within`
# over the effects walked by induction

import Base
import ../../../bend/approvals.bend as Am
import ../../../bend/tools.bend as Tl
import ../../../laws/approvals/desk.bend as ApprovalsDesk
import ../../../laws/approvals/route.bend as Approvals
import ./desk.bend as LAD

def gd.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def gd.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : gd.BD(_, A, Unit)
  Unit{}

def gd.and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# every effect may be in an auto set: exactly the codes below 7
def gd.grantable(x: Nat) -> {Tl.grantable(x) == Nat.is_lt(x, 7n) : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      match e:
                        case 0n:
                          {==}
                        case 1n+f:
                          match f:
                            case 0n:
                              {==}
                            case 1n+g:
                              match g:
                                case 0n:
                                  {==}
                                case 1n+h:
                                  {==}

# the step's test of one effect is the laws' gt_allowed
def gd.ok(+auto: List<&2, Nat>, +x: Nat) -> {Bool.and(Tl.grantable(x), Tl.elem(auto, x)) == Approvals.gt_allowed(auto, x) : Bool}:
  %gd.grantable(x) : {Bool.and(Tl.grantable(x), Tl.elem(auto, x)) == Bool.and(_, ApprovalsDesk.sp_has(auto, x)) : Bool}
  %LAD.ap.has(auto, x) : {Bool.and(Tl.grantable(x), Tl.elem(auto, x)) == Bool.and(Tl.grantable(x), _) : Bool}
  {==}

# an effect the auto set does not run unasked, wherever it sits, makes
# the step not within the auto set
def gd.within_no(pre: List<&2, Nat>, +x: Nat, +post: List<&2, Nat>, +auto: List<&2, Nat>, no: {Approvals.gt_allowed(auto, x) == False{} : Bool}) -> {Tl.within(List.append(&2, Nat, pre, x <> post), auto) == False{} : Bool}:
  match pre:
    case Nil{}:
      +e = Equal.trans(Bool, Bool.and(Tl.grantable(x), Tl.elem(auto, x)), Approvals.gt_allowed(auto, x), False{}, gd.ok(auto, x), no)
      %Equal.sym(Bool, Bool.and(Tl.grantable(x), Tl.elem(auto, x)), False{}, e) : {Bool.and(_, Tl.within(post, auto)) == False{} : Bool}
      {==}
    case +y <> rest:
      %Equal.sym(Bool, Tl.within(List.append(&2, Nat, rest, x <> post), auto), False{}, gd.within_no(rest, x, post, auto, no)) : {Bool.and(Bool.and(Tl.grantable(y), Tl.elem(auto, y)), _) == False{} : Bool}
      gd.and_false(Bool.and(Tl.grantable(y), Tl.elem(auto, y)))

# a disallowed effect of rest is one of y <> rest
def gd.cons(+y: Nat, +rest: List<&2, Nat>, +auto: List<&2, Nat>, h: Approvals.gt_has_disallowed(auto, rest)) -> Approvals.gt_has_disallowed(auto, y <> rest):
  (pre, hx) = h
  (x, hp) = hx
  (post, he) = hp
  (eq, f) = he
  (y <> pre, (x, (post, (Equal.cong(List<&2, Nat>, List<&2, Nat>, z => y <> z, rest, List.append(&2, Nat, pre, x <> post), eq), f))))

# the test of the first effect y decides: it fails, and y is the effect;
# it holds, and the rest is not within the auto set (ih: the rest's effect)
def gd.some.at(+y: Nat, +rest: List<&2, Nat>, +auto: List<&2, Nat>, b: Bool, eb: {Bool.and(Tl.grantable(y), Tl.elem(auto, y)) == b : Bool}, w: {Bool.and(b, Tl.within(rest, auto)) == False{} : Bool}, ih: @w2: {Tl.within(rest, auto) == False{} : Bool} -> Approvals.gt_has_disallowed(auto, rest)) -> Approvals.gt_has_disallowed(auto, y <> rest):
  match b:
    case False{}:
      +f = Equal.trans(Bool, Approvals.gt_allowed(auto, y), Bool.and(Tl.grantable(y), Tl.elem(auto, y)), False{}, Equal.sym(Bool, Bool.and(Tl.grantable(y), Tl.elem(auto, y)), Approvals.gt_allowed(auto, y), gd.ok(auto, y)), eb)
      (Nil{}, (y, (rest, ({==}, f))))
    case True{}:
      gd.cons(y, rest, auto, ih(w))

# a step not within the auto set has an effect the auto set does not run
# unasked (by induction on the effects)
def gd.some(es: List<&2, Nat>, +auto: List<&2, Nat>, w: {Tl.within(es, auto) == False{} : Bool}) -> Approvals.gt_has_disallowed(auto, es):
  match es:
    case Nil{}:
      gd.absurd(Approvals.gt_has_disallowed(auto, Nil{}), Equal.sym(Bool, True{}, False{}, w))
    case +y <> +rest:
      gd.some.at(y, rest, auto, Bool.and(Tl.grantable(y), Tl.elem(auto, y)), {==}, w, w2 => gd.some(rest, auto, w2))
