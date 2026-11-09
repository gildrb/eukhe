# eukhe: lemmas of area path_policy on the class of a path
#
# The class of a path through links is the model's class of the real path
# its resolution reaches (pcc.cls_eq); a protected test that holds makes
# the class Protected unless it is Secret (pcc.protects_class); a path
# under a list of paths, a rule among a list of rules (pcc.under_app,
# pcc.covers_app).

import Base
import ../../../bend/path_policy.bend as Pp
import ../../../bend/tools.bend as Tl
import ../../base/logic/logic.bend as LLogicLogic
import ../base.bend as LA
import ./root.bend as LAR

# Empty proves anything
def pcc.never(-A: Type, e: Empty) -> A:
  match e:

# the class of a path is the class of the real path it reaches
def pcc.cls_eq(+pol: Pp.Pol, +ls: List<&2, Pp.Link>, +segs: List<&2, Tl.Seg>, -at: List<&2, Nat>, -l: Bool, res: {Pp.real(ls, segs) == Pp.Res{at, l} : Pp.Res}) -> {Pp.class(pol, ls, segs) == Pp.demote(Pp.class_of(pol, at), l) : Pp.Cls}:
  Equal.cong(Pp.Res, Pp.Cls, r => Pp.class_res(pol, r), Pp.real(ls, segs), Pp.Res{at, l}, res)

# a path k ++ p is at or under p
def pcc.under_app(+p: List<&2, Nat>, k: List<&2, Nat>) -> {Pp.under(p, List.append(&2, Nat, k, p)) == True{} : Bool}:
  match k:
    case Nil{}:
      LAR.pc.under_refl(p)
    case +x <> +r:
      LA.pp.or_tr(Tl.ids.eq(p, x <> List.append(&2, Nat, r, p)), Pp.under(p, List.append(&2, Nat, r, p)), pcc.under_app(p, r))

# a rule that covers a path makes the rules around it cover it
def pcc.covers_app(ru1: List<&2, Pp.Rule>, +r: Pp.Rule, +ru2: List<&2, Pp.Rule>, +at: List<&2, Nat>, +low: List<&2, Nat>, h: {Pp.covers(r, at, low) == True{} : Bool}) -> {Pp.any_covers(List.append(&2, Pp.Rule, ru1, r <> ru2), at, low) == True{} : Bool}:
  match ru1:
    case Nil{}:
      %Equal.sym(Bool, Pp.covers(r, at, low), True{}, h) : {Bool.or(_, Pp.any_covers(ru2, at, low)) == True{} : Bool}
      {==}
    case +x <> +rest:
      LA.pp.or_tr(Pp.covers(x, at, low), Pp.any_covers(List.append(&2, Pp.Rule, rest, r <> ru2), at, low), pcc.covers_app(rest, r, ru2, at, low, h))

# a rule's cover makes the path protected
def pcc.prot_cover(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, h: {Pp.any_covers(ru, at, Pp.below(ro, at)) == True{} : Bool}) -> {Pp.protects(Pp.Pol{ro, ru, se}, at) == True{} : Bool}:
  %Equal.sym(Bool, Pp.any_covers(ru, at, Pp.below(ro, at)), True{}, h) : {Bool.or(_, Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(ru), se), at)) == True{} : Bool}
  {==}

# an entry below the path makes it protected
def pcc.prot_anc(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, h: {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(ru), se), at) == True{} : Bool}) -> {Pp.protects(Pp.Pol{ro, ru, se}, at) == True{} : Bool}:
  LA.pp.or_tr(Pp.any_covers(ru, at, Pp.below(ro, at)), Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(ru), se), at), h)

# protected, not secret: Protected
def pcc.pick_prot(s: Bool, -i: Bool, -l: Bool, ns: {Pp.demote(Pp.cls.pick(s, True{}, i), l) != Pp.Secret{} : Pp.Cls}) -> {Pp.demote(Pp.cls.pick(s, True{}, i), l) == Pp.Protected{} : Pp.Cls}:
  match s:
    case True{}:
      pcc.never({Pp.Secret{} == Pp.Protected{} : Pp.Cls}, ns({==}))
    case False{}:
      {==}

# a path the policy protects is Protected unless it is Secret
def pcc.protects_class(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +ls: List<&2, Pp.Link>, +segs: List<&2, Tl.Seg>, +at: List<&2, Nat>, +l: Bool, res: {Pp.real(ls, segs) == Pp.Res{at, l} : Pp.Res}, ns: {Pp.class(Pp.Pol{ro, ru, se}, ls, segs) != Pp.Secret{} : Pp.Cls}, hp: {Pp.protects(Pp.Pol{ro, ru, se}, at) == True{} : Bool}) -> {Pp.class(Pp.Pol{ro, ru, se}, ls, segs) == Pp.Protected{} : Pp.Cls}:
  +s = Pp.any_under(se, at)
  +i = Pp.any_under(ro, at)
  +eq = pcc.cls_eq(Pp.Pol{ro, ru, se}, ls, segs, at, l, res)
  +ep = Equal.cong(Bool, Pp.Cls, z => Pp.demote(Pp.cls.pick(s, z, i), l), Pp.protects(Pp.Pol{ro, ru, se}, at), True{}, hp)
  +ec = Equal.trans(Pp.Cls, Pp.class(Pp.Pol{ro, ru, se}, ls, segs), Pp.demote(Pp.cls.pick(s, Pp.protects(Pp.Pol{ro, ru, se}, at), i), l), Pp.demote(Pp.cls.pick(s, True{}, i), l), eq, ep)
  Equal.trans(Pp.Cls, Pp.class(Pp.Pol{ro, ru, se}, ls, segs), Pp.demote(Pp.cls.pick(s, True{}, i), l), Pp.Protected{}, ec, pcc.pick_prot(s, i, l, h => ns(Equal.trans(Pp.Cls, Pp.class(Pp.Pol{ro, ru, se}, ls, segs), Pp.demote(Pp.cls.pick(s, True{}, i), l), Pp.Secret{}, ec, h))))
