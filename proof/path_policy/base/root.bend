# eukhe: lemmas of area path_policy on paths, the root the model picks and
# the names below it
#
# pc.below_root: the names the model's Named test reads are the names of
# the path below its deepest root (PathPolicy.pp_below_root): the model
# walks up the path to the first of its ancestors-or-self that is a root
# (`listed`), the spec's pp_is_root (pc.listed_eq), so both stop at the
# same first root.

import Base
import ../../../bend/path_policy.bend as Pp
import ../../../bend/tools.bend as Tl
import ../../../laws/path_policy/policy.bend as PathPolicy
import ../base.bend as LA

# Paths
# -----

def pc.nat_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      pc.nat_eq_refl(k)

def pc.ids_refl(xs: List<&2, Nat>) -> {Tl.ids.eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +xr:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, pc.nat_eq_refl(x)) : {Bool.and(_, Tl.ids.eq(xr, xr)) == True{} : Bool}
      pc.ids_refl(xr)

def pc.under_refl(at: List<&2, Nat>) -> {Pp.under(at, at) == True{} : Bool}:
  match at:
    case Nil{}:
      {==}
    case +x <> +r:
      %Equal.sym(Bool, Tl.ids.eq(x <> r, x <> r), True{}, pc.ids_refl(x <> r)) : {Bool.or(_, Pp.under(x <> r, r)) == True{} : Bool}
      {==}

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

# Lists of entries
# ----------------

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
