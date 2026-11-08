# eukhe: the proof of LAW path_judge_class_exact
#
# PROOF: the model's class is the spec's pick of three tests, each proved
# equal to the spec's: secret (LA.pp.any_under_spec), protected (the rule
# tests, the entries, the ancestor test over the entries and the secrets,
# and the names below the root: pc.below_root), and inside (a root holds
# the path: LA.pp.any_under_spec). pc.below_root walks up the path as the
# model does: the model's root test (`listed`) is the spec's pp_is_root
# (pc.listed_eq), so both stop at the same first root.

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA

# The names below the root
# ------------------------

def pc.nat_eq_sym(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case 1n+i:
      match b:
        case 0n:
          {==}
        case 1n+j:
          pc.nat_eq_sym(i, j)

# ids.eq is the spec's pp_same, the arguments swapped
def pc.ids_swap(xs: List<&2, Nat>, ys: List<&2, Nat>) -> {Tl.ids.eq(xs, ys) == PathPolicy.pp_same(ys, xs) : Bool}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case y <> yr:
          {==}
    case +x <> xr:
      match ys:
        case Nil{}:
          {==}
        case +y <> yr:
          %pc.nat_eq_sym(x, y) : {Bool.and(Nat.is_eq(x, y), Tl.ids.eq(xr, yr)) == Bool.and(_, PathPolicy.pp_same(yr, xr)) : Bool}
          %pc.ids_swap(xr, yr) : {Bool.and(Nat.is_eq(x, y), Tl.ids.eq(xr, yr)) == Bool.and(Nat.is_eq(x, y), _) : Bool}
          {==}

# the model's root test is the spec's
def pc.listed_eq(ps: List<&2, List<&2, Nat>>, +p: List<&2, Nat>) -> {Pp.listed(ps, p) == PathPolicy.pp_is_root(ps, p) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> rest:
      %pc.ids_swap(p, q) : {Bool.or(Tl.ids.eq(p, q), Pp.listed(rest, p)) == Bool.or(_, PathPolicy.pp_is_root(rest, p)) : Bool}
      %pc.listed_eq(rest, p) : {Bool.or(Tl.ids.eq(p, q), Pp.listed(rest, p)) == Bool.or(Tl.ids.eq(p, q), _) : Bool}
      {==}

def pc.below_pick_eq(b: Bool, +x: Nat, -l1: List<&2, Nat>, -l2: List<&2, Nat>, e: {l1 == l2 : List<&2, Nat>}) -> {Pp.below.pick(b, x, l1) == PathPolicy.pp_below_pick(b, x, l2) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(List<&2, Nat>, l1, l2, e) : {x <> _ == x <> l2 : List<&2, Nat>}
      {==}

# the names the model's Named test reads are the spec's
def pc.below_root(+ro: List<&2, List<&2, Nat>>, at: List<&2, Nat>) -> {Pp.below(ro, at) == PathPolicy.pp_below_root(ro, at) : List<&2, Nat>}:
  match at:
    case Nil{}:
      {==}
    case +x <> +r:
      %Equal.sym(Bool, Pp.listed(ro, x <> r), PathPolicy.pp_is_root(ro, x <> r), pc.listed_eq(ro, x <> r)) : {Pp.below.pick(_, x, Pp.below(ro, r)) == PathPolicy.pp_below_pick(PathPolicy.pp_is_root(ro, x <> r), x, PathPolicy.pp_below_root(ro, r)) : List<&2, Nat>}
      pc.below_pick_eq(PathPolicy.pp_is_root(ro, x <> r), x, Pp.below(ro, r), PathPolicy.pp_below_root(ro, r), pc.below_root(ro, r))

# The rules
# ---------

def pc.parent_eq(at: List<&2, Nat>, +p: List<&2, Nat>) -> {Pp.parent_is(at, p) == PathPolicy.pp_parent_is(at, p) : Bool}:
  match at:
    case Nil{}:
      {==}
    case x <> r:
      LA.pp.ids_same(r, p)

def pc.elem_eq(xs: List<&2, Nat>, +n: Nat) -> {Tl.elem(xs, n) == PathPolicy.pp_has_name(xs, n) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> rest:
      %pc.elem_eq(rest, n) : {Bool.or(Nat.is_eq(y, n), Tl.elem(rest, n)) == Bool.or(Nat.is_eq(y, n), _) : Bool}
      {==}

def pc.covers_eq(r: Pp.Rule, +at: List<&2, Nat>, +low: List<&2, Nat>) -> {Pp.covers(r, at, low) == PathPolicy.pp_covers(r, at, low) : Bool}:
  match r:
    case Pp.Tree{+p}:
      LA.pp.under_spec(p, at)
    case Pp.Dir{+p}:
      %LA.pp.ids_same(at, p) : {Bool.or(Tl.ids.eq(at, p), Pp.parent_is(at, p)) == Bool.or(_, PathPolicy.pp_parent_is(at, p)) : Bool}
      %pc.parent_eq(at, p) : {Bool.or(Tl.ids.eq(at, p), Pp.parent_is(at, p)) == Bool.or(Tl.ids.eq(at, p), _) : Bool}
      {==}
    case Pp.Named{+n}:
      pc.elem_eq(low, n)

def pc.covers_any_eq(rs: List<&2, Pp.Rule>, +at: List<&2, Nat>, +low: List<&2, Nat>) -> {Pp.any_covers(rs, at, low) == PathPolicy.pp_covers_any(rs, at, low) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %pc.covers_eq(r, at, low) : {Bool.or(Pp.covers(r, at, low), Pp.any_covers(rest, at, low)) == Bool.or(_, PathPolicy.pp_covers_any(rest, at, low)) : Bool}
      %pc.covers_any_eq(rest, at, low) : {Bool.or(Pp.covers(r, at, low), Pp.any_covers(rest, at, low)) == Bool.or(Pp.covers(r, at, low), _) : Bool}
      {==}

def pc.entries_eq(rs: List<&2, Pp.Rule>) -> {Pp.entries(rs) == PathPolicy.pp_entries(rs) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case Pp.Tree{+p}:
          %pc.entries_eq(rest) : {p <> Pp.entries(rest) == p <> _ : List<&2, List<&2, Nat>>}
          {==}
        case Pp.Dir{+p}:
          %pc.entries_eq(rest) : {p <> Pp.entries(rest) == p <> _ : List<&2, List<&2, Nat>>}
          {==}
        case Pp.Named{n}:
          pc.entries_eq(rest)

def pc.or_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pc.anc_append(xs: List<&2, List<&2, Nat>>, +ys: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> {Pp.any_ancestor(List.append(&2, List<&2, Nat>, xs, ys), at) == Bool.or(Pp.any_ancestor(xs, at), Pp.any_ancestor(ys, at)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +p <> +rest:
      %Equal.sym(Bool, Pp.any_ancestor(List.append(&2, List<&2, Nat>, rest, ys), at), Bool.or(Pp.any_ancestor(rest, at), Pp.any_ancestor(ys, at)), pc.anc_append(rest, ys, at)) : {Bool.or(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), _) == Bool.or(Bool.or(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Pp.any_ancestor(rest, at)), Pp.any_ancestor(ys, at)) : Bool}
      pc.or_assoc(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Pp.any_ancestor(rest, at), Pp.any_ancestor(ys, at))

# the model's protected test is the spec's
def pc.prot_eq(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(PathPolicy.pp_covers_any(ru, at, PathPolicy.pp_below_root(ro, at)), Bool.or(PathPolicy.pp_above_any(PathPolicy.pp_entries(ru), at), PathPolicy.pp_above_any(se, at))) : Bool}:
  %pc.below_root(ro, at) : {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(PathPolicy.pp_covers_any(ru, at, _), Bool.or(PathPolicy.pp_above_any(PathPolicy.pp_entries(ru), at), PathPolicy.pp_above_any(se, at))) : Bool}
  %pc.covers_any_eq(ru, at, Pp.below(ro, at)) : {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(_, Bool.or(PathPolicy.pp_above_any(PathPolicy.pp_entries(ru), at), PathPolicy.pp_above_any(se, at))) : Bool}
  %pc.entries_eq(ru) : {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(Pp.any_covers(ru, at, Pp.below(ro, at)), Bool.or(PathPolicy.pp_above_any(_, at), PathPolicy.pp_above_any(se, at))) : Bool}
  %LA.pp.any_ancestor_spec(Pp.entries(ru), at) : {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(Pp.any_covers(ru, at, Pp.below(ro, at)), Bool.or(_, PathPolicy.pp_above_any(se, at))) : Bool}
  %LA.pp.any_ancestor_spec(se, at) : {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(Pp.any_covers(ru, at, Pp.below(ro, at)), Bool.or(Pp.any_ancestor(Pp.entries(ru), at), _)) : Bool}
  %pc.anc_append(Pp.entries(ru), se, at) : {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(Pp.any_covers(ru, at, Pp.below(ro, at)), _) : Bool}
  {==}

# The class
# ---------

def pc.pick_eq(s: Bool, p: Bool, i: Bool, l: Bool) -> {Pp.demote(Pp.cls.pick(s, p, i), l) == PathPolicy.pp_cls_pick(s, p, Bool.and(i, Bool.not(l))) : Pp.Cls}:
  match s:
    case True{}:
      {==}
    case False{}:
      match p:
        case True{}:
          {==}
        case False{}:
          match i:
            case True{}:
              match l:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              {==}

def PathPolicy.path_judge_class_exact(ro, ru, se, at, l):
  %LA.pp.any_under_spec(se, at) : {Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l})) == PathPolicy.pp_cls_pick(_, Bool.or(PathPolicy.pp_covers_any(ru, at, PathPolicy.pp_below_root(ro, at)), Bool.or(PathPolicy.pp_above_any(PathPolicy.pp_entries(ru), at), PathPolicy.pp_above_any(se, at))), Bool.and(PathPolicy.pp_under_any(ro, at), Bool.not(l))) : Pp.Cls}
  %pc.prot_eq(ro, ru, se, at) : {Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l})) == PathPolicy.pp_cls_pick(Pp.any_under(se, at), _, Bool.and(PathPolicy.pp_under_any(ro, at), Bool.not(l))) : Pp.Cls}
  %LA.pp.any_under_spec(ro, at) : {Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l})) == PathPolicy.pp_cls_pick(Pp.any_under(se, at), Pp.protects(Pp.Pol{ro, ru, se}, at), Bool.and(_, Bool.not(l))) : Pp.Cls}
  pc.pick_eq(Pp.any_under(se, at), Pp.protects(Pp.Pol{ro, ru, se}, at), Pp.any_under(ro, at), l)
