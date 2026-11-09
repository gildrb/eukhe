# eukhe: the proof of LAW path_entry_ancestor_protects
#
# PROOF: the entry e = m/k/at is under at (pcc.under_app) and is not at (a
# path is never the same as a longer one: pce.ne), so at is a strict
# ancestor of e (pce.head); e is an entry of the rules (pce.ents, by
# induction on the rules before it), so at is a strict ancestor of an
# entry (pc.anc_append), the policy protects it and, not Secret, it is
# Protected (pcc.protects_class).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./base/root.bend as LAR
import ./base/class.bend as LAC

def pce.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# j ++ (b, r) is (j ++ [b]) ++ r
def pce.snoc(j: List<&2, Nat>, +b: Nat, +r: List<&2, Nat>) -> {List.append(&2, Nat, j, b <> r) == List.append(&2, Nat, List.append(&2, Nat, j, [b]), r) : List<&2, Nat>}:
  match j:
    case Nil{}:
      {==}
    case +d <> +t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => d <> z, List.append(&2, Nat, t, b <> r), List.append(&2, Nat, List.append(&2, Nat, t, [b]), r), pce.snoc(t, b, r))

# a path is never the same as a path strictly under it
def pce.ne(r: List<&2, Nat>, +c: Nat, +j: List<&2, Nat>) -> {Tl.ids.eq(r, c <> List.append(&2, Nat, j, r)) == False{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case +b <> +t:
      match j:
        case Nil{}:
          %Equal.sym(Bool, Tl.ids.eq(t, b <> t), False{}, pce.ne(t, b, Nil{})) : {Bool.and(Nat.is_eq(b, c), _) == False{} : Bool}
          pce.and_f(Nat.is_eq(b, c))
        case +d <> +j2:
          +e1 = Equal.cong(List<&2, Nat>, Bool, z => Tl.ids.eq(t, d <> z), List.append(&2, Nat, j2, b <> t), List.append(&2, Nat, List.append(&2, Nat, j2, [b]), t), pce.snoc(j2, b, t))
          +e2 = Equal.trans(Bool, Tl.ids.eq(t, d <> List.append(&2, Nat, j2, b <> t)), Tl.ids.eq(t, d <> List.append(&2, Nat, List.append(&2, Nat, j2, [b]), t)), False{}, e1, pce.ne(t, d, List.append(&2, Nat, j2, [b])))
          %Equal.sym(Bool, Tl.ids.eq(t, d <> List.append(&2, Nat, j2, b <> t)), False{}, e2) : {Bool.and(Nat.is_eq(b, c), _) == False{} : Bool}
          pce.and_f(Nat.is_eq(b, c))

# at is a strict ancestor of m/k/at
def pce.strict(+at: List<&2, Nat>, +m: Nat, +k: List<&2, Nat>) -> {Bool.and(Pp.under(at, m <> List.append(&2, Nat, k, at)), Bool.not(Tl.ids.eq(at, m <> List.append(&2, Nat, k, at)))) == True{} : Bool}:
  +un = LA.pp.or_tr(Tl.ids.eq(at, m <> List.append(&2, Nat, k, at)), Pp.under(at, List.append(&2, Nat, k, at)), LAC.pcc.under_app(at, k))
  %Equal.sym(Bool, Pp.under(at, m <> List.append(&2, Nat, k, at)), True{}, un) : {Bool.and(_, Bool.not(Tl.ids.eq(at, m <> List.append(&2, Nat, k, at)))) == True{} : Bool}
  %Equal.sym(Bool, Tl.ids.eq(at, m <> List.append(&2, Nat, k, at)), False{}, pce.ne(at, m, k)) : {Bool.and(True{}, Bool.not(_)) == True{} : Bool}
  {==}

# at is a strict ancestor of an entry of the rules ru1 ++ R ++ ru2, R on e
def pce.ents(ru1: List<&2, Pp.Rule>, +tree: Bool, +m: Nat, +k: List<&2, Nat>, +at: List<&2, Nat>, +ru2: List<&2, Pp.Rule>) -> {Pp.any_ancestor(Pp.entries(List.append(&2, Pp.Rule, ru1, PathPolicy.pp_entry_rule(tree, m <> List.append(&2, Nat, k, at)) <> ru2)), at) == True{} : Bool}:
  match ru1:
    case Nil{}:
      match tree:
        case True{}:
          %Equal.sym(Bool, Bool.and(Pp.under(at, m <> List.append(&2, Nat, k, at)), Bool.not(Tl.ids.eq(at, m <> List.append(&2, Nat, k, at)))), True{}, pce.strict(at, m, k)) : {Bool.or(_, Pp.any_ancestor(Pp.entries(ru2), at)) == True{} : Bool}
          {==}
        case False{}:
          %Equal.sym(Bool, Bool.and(Pp.under(at, m <> List.append(&2, Nat, k, at)), Bool.not(Tl.ids.eq(at, m <> List.append(&2, Nat, k, at)))), True{}, pce.strict(at, m, k)) : {Bool.or(_, Pp.any_ancestor(Pp.entries(ru2), at)) == True{} : Bool}
          {==}
    case x <> +rest:
      match x:
        case Pp.Tree{+p}:
          LA.pp.or_tr(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Pp.any_ancestor(Pp.entries(List.append(&2, Pp.Rule, rest, PathPolicy.pp_entry_rule(tree, m <> List.append(&2, Nat, k, at)) <> ru2)), at), pce.ents(rest, tree, m, k, at, ru2))
        case Pp.Dir{+p}:
          LA.pp.or_tr(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Pp.any_ancestor(Pp.entries(List.append(&2, Pp.Rule, rest, PathPolicy.pp_entry_rule(tree, m <> List.append(&2, Nat, k, at)) <> ru2)), at), pce.ents(rest, tree, m, k, at, ru2))
        case Pp.Named{n}:
          pce.ents(rest, tree, m, k, at, ru2)

def PathPolicy.path_entry_ancestor_protects(ro, ru1, tree, m, k, ru2, se, ls, segs, at, l, res, ns):
  +ru = List.append(&2, Pp.Rule, ru1, PathPolicy.pp_entry_rule(tree, m <> List.append(&2, Nat, k, at)) <> ru2)
  +ea = Equal.trans(Bool, Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(ru), se), at), Bool.or(Pp.any_ancestor(Pp.entries(ru), at), Pp.any_ancestor(se, at)), True{}, LAR.pc.anc_append(Pp.entries(ru), se, at), Equal.cong(Bool, Bool, z => Bool.or(z, Pp.any_ancestor(se, at)), Pp.any_ancestor(Pp.entries(ru), at), True{}, pce.ents(ru1, tree, m, k, at, ru2)))
  LAC.pcc.protects_class(ro, ru, se, ls, segs, at, l, res, ns, LAC.pcc.prot_anc(ro, ru, se, at, ea))
