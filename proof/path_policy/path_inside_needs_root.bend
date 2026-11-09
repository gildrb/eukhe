# eukhe: the proof of LAW path_inside_needs_root
#
# PROOF: the class is the model's class of the real path (pcc.cls_eq); it
# is Inside only when the model found a root (pin.found), that is when
# some root is at or above the path (pc.has_root); that root splits the
# roots (pin.find) and is a suffix of the path (pin.usplit), both by
# induction carrying the tail's answer as a function of its premise.

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA
import ./base/lemmas.bend as LAE
import ./base/root.bend as LAR
import ./base/class.bend as LAC

# the class picked is Inside only when a root was found
def pin.found(s: Bool, p: Bool, i: Bool, -l: Bool, h: {Pp.demote(Pp.cls.pick(s, p, i), l) == Pp.Inside{} : Pp.Cls}) -> {i == True{} : Bool}:
  match s:
    case True{}:
      %h : LLogicLogic.pp.CM(_, {i == True{} : Bool})
      Unit{}
    case False{}:
      match p:
        case True{}:
          %h : LLogicLogic.pp.CM(_, {i == True{} : Bool})
          Unit{}
        case False{}:
          match i:
            case True{}:
              {==}
            case False{}:
              %h : LLogicLogic.pp.CM(_, {False{} == True{} : Bool})
              Unit{}

# p is a suffix of at
def pin.Suf(p: List<&2, Nat>, at: List<&2, Nat>) -> Type:
  &k: List<&2, Nat> -> {at == List.append(&2, Nat, k, p) : List<&2, Nat>}

def pin.suf_cons(+x: Nat, -r: List<&2, Nat>, -p: List<&2, Nat>, s: pin.Suf(p, r)) -> pin.Suf(p, x <> r):
  match s:
    case (+k, e):
      (x <> k, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => x <> z, r, List.append(&2, Nat, k, p), e))

def pin.u_at(b: Bool, +p: List<&2, Nat>, +x: Nat, +r: List<&2, Nat>, eb: {Tl.ids.eq(p, x <> r) == b : Bool}, h: {Bool.or(b, Pp.under(p, r)) == True{} : Bool}, ih: {Pp.under(p, r) == True{} : Bool} -> pin.Suf(p, r)) -> pin.Suf(p, x <> r):
  match b:
    case True{}:
      (Nil{}, Equal.sym(List<&2, Nat>, p, x <> r, LAE.pp.ids_sound(p, x <> r, eb)))
    case False{}:
      pin.suf_cons(x, r, p, ih(h))

# a path at or above at is a suffix of it
def pin.usplit(+p: List<&2, Nat>, at: List<&2, Nat>) -> {Pp.under(p, at) == True{} : Bool} -> pin.Suf(p, at):
  match at:
    case Nil{}:
      h => (Nil{}, Equal.sym(List<&2, Nat>, p, Nil{}, LAE.pp.ids_sound(p, Nil{}, h)))
    case +x <> +r:
      h => pin.u_at(Tl.ids.eq(p, x <> r), p, x, r, {==}, h, pin.usplit(p, r))

# a root of ro is at or above at
def pin.Goal(ro: List<&2, List<&2, Nat>>, at: List<&2, Nat>) -> Type:
  &ro1: List<&2, List<&2, Nat>> -> &q: List<&2, Nat> -> &ro2: List<&2, List<&2, Nat>> -> &k: List<&2, Nat> -> ({ro == List.append(&2, List<&2, Nat>, ro1, q <> ro2) : List<&2, List<&2, Nat>>} & {at == List.append(&2, Nat, k, q) : List<&2, Nat>})

def pin.here(+p: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, -at: List<&2, Nat>, s: pin.Suf(p, at)) -> pin.Goal(p <> rest, at):
  match s:
    case (+k, e):
      (Nil{}, (p, (rest, (k, ({==}, e)))))

def pin.cons(+p: List<&2, Nat>, -rest: List<&2, List<&2, Nat>>, -at: List<&2, Nat>, g: pin.Goal(rest, at)) -> pin.Goal(p <> rest, at):
  match g:
    case (+ro1, g1):
      match g1:
        case (+q, g2):
          match g2:
            case (+ro2, g3):
              match g3:
                case (+k, g4):
                  (e1, e2) = g4
                  (p <> ro1, (q, (ro2, (k, (Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, z => p <> z, rest, List.append(&2, List<&2, Nat>, ro1, q <> ro2), e1), e2)))))

def pin.f_at(u: Bool, +p: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, eu: {Pp.under(p, at) == u : Bool}, h: {Bool.or(u, Pp.any_under(rest, at)) == True{} : Bool}, ih: {Pp.any_under(rest, at) == True{} : Bool} -> pin.Goal(rest, at)) -> pin.Goal(p <> rest, at):
  match u:
    case True{}:
      pin.here(p, rest, at, pin.usplit(p, at)(eu))
    case False{}:
      pin.cons(p, rest, at, ih(h))

# a root at or above at splits the roots
def pin.find(ro: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> {Pp.any_under(ro, at) == True{} : Bool} -> pin.Goal(ro, at):
  match ro:
    case Nil{}:
      h => LA.pp.absurdF(pin.Goal(Nil{}, at), h)
    case +p <> +rest:
      h => pin.f_at(Pp.under(p, at), p, rest, at, {==}, h, pin.find(rest, at))

def PathPolicy.path_inside_needs_root(ro, ru, se, ls, segs, at, l, res, inside):
  +pol = {Pp.Pol{ro, ru, se} : Pp.Pol}
  +i = Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(ro, at))
  +hc = Equal.trans(Pp.Cls, Pp.demote(Pp.class_of(pol, at), l), Pp.class(pol, ls, segs), Pp.Inside{}, Equal.sym(Pp.Cls, Pp.class(pol, ls, segs), Pp.demote(Pp.class_of(pol, at), l), LAC.pcc.cls_eq(pol, ls, segs, at, l, res)), inside)
  +hi = pin.found(Pp.any_under(se, at), Pp.protects(pol, at), i, l, hc)
  pin.find(ro, at)(Equal.trans(Bool, Pp.any_under(ro, at), i, True{}, Equal.sym(Bool, i, Pp.any_under(ro, at), LAR.pc.has_root(ro, at)), hi))
