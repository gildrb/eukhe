# eukhe: the proof of LAW path_rule_never_unprotects
#
# PROOF: a Protected class is a class with no secret over the path and a
# protected test that holds (pnu.sp); a rule added at any position keeps
# every cover of the others (pnu.cov_ins) and every entry of theirs
# (pnu.anc_ins, by the kinds of the rules before it), so the protected test
# still holds and the class stays Protected.

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA

# A at Protected, Unit elsewhere: refutes {c == Protected} for c not Protected
def pnu.PM(c: Pp.Cls, A: Type) -> Type:
  match c:
    case Pp.Inside{}:
      Unit
    case Pp.Outside{}:
      Unit
    case Pp.Protected{}:
      A
    case Pp.Secret{}:
      Unit

# Protected: no secret, and protected
def pnu.sp(s: Bool, p: Bool, i: Bool, l: Bool, h: {Pp.demote(Pp.cls.pick(s, p, i), l) == Pp.Protected{} : Pp.Cls}) -> {Bool.and(Bool.not(s), p) == True{} : Bool}:
  match s:
    case True{}:
      %h : pnu.PM(_, {False{} == True{} : Bool})
      Unit{}
    case False{}:
      match p:
        case True{}:
          {==}
        case False{}:
          match i:
            case True{}:
              match l:
                case True{}:
                  %h : pnu.PM(_, {False{} == True{} : Bool})
                  Unit{}
                case False{}:
                  %h : pnu.PM(_, {False{} == True{} : Bool})
                  Unit{}
            case False{}:
              %h : pnu.PM(_, {False{} == True{} : Bool})
              Unit{}

# no secret and protected: Protected
def pnu.back(s: Bool, p: Bool, -i: Bool, -l: Bool, h: {Bool.and(Bool.not(s), p) == True{} : Bool}) -> {Pp.demote(Pp.cls.pick(s, p, i), l) == Pp.Protected{} : Pp.Cls}:
  match s:
    case True{}:
      LA.pp.absurdF({Pp.demote(Pp.cls.pick(True{}, p, i), l) == Pp.Protected{} : Pp.Cls}, h)
    case False{}:
      match p:
        case True{}:
          {==}
        case False{}:
          LA.pp.absurdF({Pp.demote(Pp.cls.pick(False{}, False{}, i), l) == Pp.Protected{} : Pp.Cls}, h)

# an entry list with the added rule's entry in front keeps the ancestor test
def pnu.anc(x: Pp.Rule, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, h: {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(ru), se), at) == True{} : Bool}) -> {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(x <> ru), se), at) == True{} : Bool}:
  match x:
    case Pp.Tree{+p}:
      LA.pp.or_tr(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(ru), se), at), h)
    case Pp.Dir{+p}:
      LA.pp.or_tr(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(ru), se), at), h)
    case Pp.Named{n}:
      h

# a or b holds, and b gives c: a or c holds
def pnu.or_step(a: Bool, -b: Bool, -c: Bool, h: {Bool.or(a, b) == True{} : Bool}, f: {b == True{} : Bool} -> {c == True{} : Bool}) -> {Bool.or(a, c) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(h)

# a rule x added after ru1 keeps every cover of ru1 ++ ru2
def pnu.cov_ins(ru1: List<&2, Pp.Rule>, +x: Pp.Rule, +ru2: List<&2, Pp.Rule>, +at: List<&2, Nat>, +low: List<&2, Nat>) -> {Pp.any_covers(List.append(&2, Pp.Rule, ru1, ru2), at, low) == True{} : Bool} -> {Pp.any_covers(List.append(&2, Pp.Rule, ru1, x <> ru2), at, low) == True{} : Bool}:
  match ru1:
    case Nil{}:
      h => LA.pp.or_tr(Pp.covers(x, at, low), Pp.any_covers(ru2, at, low), h)
    case +r <> +rest:
      h => pnu.or_step(Pp.covers(r, at, low), Pp.any_covers(List.append(&2, Pp.Rule, rest, ru2), at, low), Pp.any_covers(List.append(&2, Pp.Rule, rest, x <> ru2), at, low), h, pnu.cov_ins(rest, x, ru2, at, low))

# one rule r before the insertion point keeps the ancestor test, given the
# rules after it do (ih)
def pnu.anc_rule(r: Pp.Rule, +rest: List<&2, Pp.Rule>, +x: Pp.Rule, +ru2: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, h: {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(r <> List.append(&2, Pp.Rule, rest, ru2)), se), at) == True{} : Bool}, ih: {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(List.append(&2, Pp.Rule, rest, ru2)), se), at) == True{} : Bool} -> {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(List.append(&2, Pp.Rule, rest, x <> ru2)), se), at) == True{} : Bool}) -> {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(r <> List.append(&2, Pp.Rule, rest, x <> ru2)), se), at) == True{} : Bool}:
  match r:
    case Pp.Tree{+p}:
      pnu.or_step(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(List.append(&2, Pp.Rule, rest, ru2)), se), at), Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(List.append(&2, Pp.Rule, rest, x <> ru2)), se), at), h, ih)
    case Pp.Dir{+p}:
      pnu.or_step(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(List.append(&2, Pp.Rule, rest, ru2)), se), at), Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(List.append(&2, Pp.Rule, rest, x <> ru2)), se), at), h, ih)
    case Pp.Named{n}:
      ih(h)

# a rule x added after ru1 keeps every entry ancestor of ru1 ++ ru2
def pnu.anc_ins(ru1: List<&2, Pp.Rule>, +x: Pp.Rule, +ru2: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(List.append(&2, Pp.Rule, ru1, ru2)), se), at) == True{} : Bool} -> {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(List.append(&2, Pp.Rule, ru1, x <> ru2)), se), at) == True{} : Bool}:
  match ru1:
    case Nil{}:
      h => pnu.anc(x, ru2, se, at, h)
    case +r <> +rest:
      h => pnu.anc_rule(r, rest, x, ru2, se, at, h, pnu.anc_ins(rest, x, ru2, se, at))

# the protected test with a rule added after ru1, by the old cover test a
def pnu.p2(a: Bool, +x: Pp.Rule, +ro: List<&2, List<&2, Nat>>, +ru1: List<&2, Pp.Rule>, +ru2: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, ea: {Pp.any_covers(List.append(&2, Pp.Rule, ru1, ru2), at, Pp.below(ro, at)) == a : Bool}, h: {Bool.or(a, Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(List.append(&2, Pp.Rule, ru1, ru2)), se), at)) == True{} : Bool}) -> {Pp.protects(Pp.Pol{ro, List.append(&2, Pp.Rule, ru1, x <> ru2), se}, at) == True{} : Bool}:
  match a:
    case True{}:
      +hc = pnu.cov_ins(ru1, x, ru2, at, Pp.below(ro, at))(ea)
      %Equal.sym(Bool, Pp.any_covers(List.append(&2, Pp.Rule, ru1, x <> ru2), at, Pp.below(ro, at)), True{}, hc) : {Bool.or(_, Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(List.append(&2, Pp.Rule, ru1, x <> ru2)), se), at)) == True{} : Bool}
      {==}
    case False{}:
      LA.pp.or_tr(Pp.any_covers(List.append(&2, Pp.Rule, ru1, x <> ru2), at, Pp.below(ro, at)), Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(List.append(&2, Pp.Rule, ru1, x <> ru2)), se), at), pnu.anc_ins(ru1, x, ru2, se, at)(h))

# no secret: not s and True holds
def pnu.not_t(s: Bool, -p: Bool, h: {Bool.and(Bool.not(s), p) == True{} : Bool}) -> {Bool.and(Bool.not(s), True{}) == True{} : Bool}:
  match s:
    case True{}:
      LA.pp.absurdF({Bool.and(Bool.not(True{}), True{}) == True{} : Bool}, h)
    case False{}:
      {==}

def pnu.res(+ro: List<&2, List<&2, Nat>>, +ru1: List<&2, Pp.Rule>, +x: Pp.Rule, +ru2: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, r: Pp.Res, h: {Pp.class_res(Pp.Pol{ro, List.append(&2, Pp.Rule, ru1, ru2), se}, r) == Pp.Protected{} : Pp.Cls}) -> {Pp.class_res(Pp.Pol{ro, List.append(&2, Pp.Rule, ru1, x <> ru2), se}, r) == Pp.Protected{} : Pp.Cls}:
  match r:
    case Pp.Res{+at, +l}:
      +ru = List.append(&2, Pp.Rule, ru1, ru2)
      +rx = List.append(&2, Pp.Rule, ru1, x <> ru2)
      +s = Pp.any_under(se, at)
      +i = Pp.any_under(ro, at)
      +sp = pnu.sp(s, Pp.protects(Pp.Pol{ro, ru, se}, at), i, l, h)
      +p1 = LA.pp.and_r(Bool.not(s), Pp.protects(Pp.Pol{ro, ru, se}, at), sp)
      +p2 = pnu.p2(Pp.any_covers(ru, at, Pp.below(ro, at)), x, ro, ru1, ru2, se, at, {==}, p1)
      +ns = Equal.trans(Bool, Bool.and(Bool.not(s), Pp.protects(Pp.Pol{ro, rx, se}, at)), Bool.and(Bool.not(s), True{}), True{}, Equal.cong(Bool, Bool, z => Bool.and(Bool.not(s), z), Pp.protects(Pp.Pol{ro, rx, se}, at), True{}, p2), pnu.not_t(s, Pp.protects(Pp.Pol{ro, ru, se}, at), sp))
      pnu.back(s, Pp.protects(Pp.Pol{ro, rx, se}, at), i, l, ns)

def PathPolicy.path_rule_never_unprotects(ro, ru1, r, ru2, se, ls, segs, prot):
  pnu.res(ro, ru1, r, ru2, se, Pp.real(ls, segs), prot)
