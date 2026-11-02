# eukhe: lemmas of area path_policy: the model's judgment is the spec's
# (laws/path_policy.bend, section the judgment, whole), helper by helper

import Base
import ../../../bend/path_policy.bend as Pp
import ../../../bend/tools.bend as Tl
import ../../../laws/path_policy.bend as PathPolicy

# congruences of the Bool connectives
def ps.or_eq(-a: Bool, -a2: Bool, -b: Bool, -b2: Bool, ea: {a == a2 : Bool}, eb: {b == b2 : Bool}) -> {Bool.or(a, b) == Bool.or(a2, b2) : Bool}:
  %Equal.sym(Bool, a, a2, ea) : {Bool.or(_, b) == Bool.or(a2, b2) : Bool}
  %Equal.sym(Bool, b, b2, eb) : {Bool.or(a2, _) == Bool.or(a2, b2) : Bool}
  {==}

def ps.and_eq(-a: Bool, -a2: Bool, -b: Bool, -b2: Bool, ea: {a == a2 : Bool}, eb: {b == b2 : Bool}) -> {Bool.and(a, b) == Bool.and(a2, b2) : Bool}:
  %Equal.sym(Bool, a, a2, ea) : {Bool.and(_, b) == Bool.and(a2, b2) : Bool}
  %Equal.sym(Bool, b, b2, eb) : {Bool.and(a2, _) == Bool.and(a2, b2) : Bool}
  {==}

def ps.not_eq(-a: Bool, -a2: Bool, ea: {a == a2 : Bool}) -> {Bool.not(a) == Bool.not(a2) : Bool}:
  %Equal.sym(Bool, a, a2, ea) : {Bool.not(_) == Bool.not(a2) : Bool}
  {==}

def ps.or_f(b: Bool) -> {b == Bool.or(b, False{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# path equality
def ps.same(a: List<&2, Nat>, b: List<&2, Nat>) -> {Tl.ids.eq(a, b) == PathPolicy.pp_same(a, b) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      {==}
    case x <> xr Nil{}:
      {==}
    case +x <> xr +y <> yr:
      Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(x, y), z), Tl.ids.eq(xr, yr), PathPolicy.pp_same(xr, yr), ps.same(xr, yr))

# p is at or an ancestor: p is in at's lineage
def ps.under(+p: List<&2, Nat>, at: List<&2, Nat>) -> {Pp.under(p, at) == PathPolicy.pp_in(p, PathPolicy.pp_lineage(at)) : Bool}:
  match at:
    case Nil{}:
      Equal.trans(Bool, Tl.ids.eq(p, Nil{}), PathPolicy.pp_same(p, Nil{}), Bool.or(PathPolicy.pp_same(p, Nil{}), False{}), ps.same(p, Nil{}), ps.or_f(PathPolicy.pp_same(p, Nil{})))
    case +x <> +r:
      ps.or_eq(Tl.ids.eq(p, x <> r), PathPolicy.pp_same(p, x <> r), Pp.under(p, r), PathPolicy.pp_in(p, PathPolicy.pp_lineage(r)), ps.same(p, x <> r), ps.under(p, r))

def ps.any_under(ps: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> {Pp.any_under(ps, at) == PathPolicy.pp_under_any(ps, at) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> rest:
      ps.or_eq(Pp.under(p, at), PathPolicy.pp_in(p, PathPolicy.pp_lineage(at)), Pp.any_under(rest, at), PathPolicy.pp_under_any(rest, at), ps.under(p, at), ps.any_under(rest, at))

def ps.any_ancestor(ps: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> {Pp.any_ancestor(ps, at) == PathPolicy.pp_above_any(ps, at) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> rest:
      ps.or_eq(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Bool.and(PathPolicy.pp_in(at, PathPolicy.pp_lineage(p)), Bool.not(PathPolicy.pp_same(at, p))), Pp.any_ancestor(rest, at), PathPolicy.pp_above_any(rest, at),
        ps.and_eq(Pp.under(at, p), PathPolicy.pp_in(at, PathPolicy.pp_lineage(p)), Bool.not(Tl.ids.eq(at, p)), Bool.not(PathPolicy.pp_same(at, p)), ps.under(at, p), ps.not_eq(Tl.ids.eq(at, p), PathPolicy.pp_same(at, p), ps.same(at, p))),
        ps.any_ancestor(rest, at))

def ps.entries(rs: List<&2, Pp.Rule>) -> {Pp.entries(rs) == PathPolicy.pp_entries(rs) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> rest:
      match r:
        case Pp.Tree{+p}:
          Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, z => p <> z, Pp.entries(rest), PathPolicy.pp_entries(rest), ps.entries(rest))
        case Pp.Dir{+p}:
          Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, z => p <> z, Pp.entries(rest), PathPolicy.pp_entries(rest), ps.entries(rest))
        case Pp.Named{n}:
          ps.entries(rest)

def ps.listed(ps: List<&2, List<&2, Nat>>, +p: List<&2, Nat>) -> {Pp.listed(ps, p) == PathPolicy.pp_in(p, ps) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> rest:
      ps.or_eq(Tl.ids.eq(p, q), PathPolicy.pp_same(p, q), Pp.listed(rest, p), PathPolicy.pp_in(p, rest), ps.same(p, q), ps.listed(rest, p))

def ps.below.pick(b: Bool, +x: Nat, -l1: List<&2, Nat>, -l2: List<&2, Nat>, e: {l1 == l2 : List<&2, Nat>}) -> {Pp.below.pick(b, x, l1) == PathPolicy.pp_below.at(b, x, l2) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(List<&2, Nat>, l1, l2, e) : {x <> _ == x <> l2 : List<&2, Nat>}
      {==}

def ps.below(+roots: List<&2, List<&2, Nat>>, at: List<&2, Nat>) -> {Pp.below(roots, at) == PathPolicy.pp_below(roots, at) : List<&2, Nat>}:
  match at:
    case Nil{}:
      {==}
    case +x <> +r:
      %Equal.sym(Bool, Pp.listed(roots, x <> r), PathPolicy.pp_in(x <> r, roots), ps.listed(roots, x <> r)) : {Pp.below.pick(_, x, Pp.below(roots, r)) == PathPolicy.pp_below.at(PathPolicy.pp_in(x <> r, roots), x, PathPolicy.pp_below(roots, r)) : List<&2, Nat>}
      ps.below.pick(PathPolicy.pp_in(x <> r, roots), x, Pp.below(roots, r), PathPolicy.pp_below(roots, r), ps.below(roots, r))

def ps.has(ns: List<&2, Nat>, +n: Nat) -> {Tl.elem(ns, n) == PathPolicy.pp_has(ns, n) : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +m <> rest:
      Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(m, n), z), Tl.elem(rest, n), PathPolicy.pp_has(rest, n), ps.has(rest, n))

def ps.parent(at: List<&2, Nat>, +p: List<&2, Nat>) -> {Pp.parent_is(at, p) == PathPolicy.pp_parent_is(at, p) : Bool}:
  match at:
    case Nil{}:
      {==}
    case x <> r:
      ps.same(r, p)

def ps.covers(r: Pp.Rule, +at: List<&2, Nat>, +low: List<&2, Nat>) -> {Pp.covers(r, at, low) == PathPolicy.pp_covers(r, at, low) : Bool}:
  match r:
    case Pp.Tree{p}:
      ps.under(p, at)
    case Pp.Dir{+p}:
      ps.or_eq(Tl.ids.eq(at, p), PathPolicy.pp_same(at, p), Pp.parent_is(at, p), PathPolicy.pp_parent_is(at, p), ps.same(at, p), ps.parent(at, p))
    case Pp.Named{n}:
      ps.has(low, n)

def ps.covers_any(rs: List<&2, Pp.Rule>, +at: List<&2, Nat>, +low: List<&2, Nat>) -> {Pp.any_covers(rs, at, low) == PathPolicy.pp_covers_any(rs, at, low) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> rest:
      ps.or_eq(Pp.covers(r, at, low), PathPolicy.pp_covers(r, at, low), Pp.any_covers(rest, at, low), PathPolicy.pp_covers_any(rest, at, low), ps.covers(r, at, low), ps.covers_any(rest, at, low))

def ps.pick(sec: Bool, prot: Bool, ins: Bool, l: Bool) -> {Pp.demote(Pp.cls.pick(sec, prot, ins), l) == PathPolicy.pp_pick(sec, prot, ins, l) : Pp.Cls}:
  match sec:
    case True{}:
      {==}
    case False{}:
      match prot:
        case True{}:
          {==}
        case False{}:
          match ins:
            case True{}:
              match l:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              {==}

def ps.class_eq(-a: Bool, a2: Bool, -b: Bool, b2: Bool, -c: Bool, c2: Bool, -d: Bool, d2: Bool, l: Bool, ea: {a == a2 : Bool}, eb: {b == b2 : Bool}, ec: {c == c2 : Bool}, ed: {d == d2 : Bool}) -> {Pp.demote(Pp.cls.pick(a, Bool.or(b, c), d), l) == PathPolicy.pp_pick(a2, Bool.or(b2, c2), d2, l) : Pp.Cls}:
  %Equal.sym(Bool, a, a2, ea) : {Pp.demote(Pp.cls.pick(_, Bool.or(b, c), d), l) == PathPolicy.pp_pick(a2, Bool.or(b2, c2), d2, l) : Pp.Cls}
  %Equal.sym(Bool, b, b2, eb) : {Pp.demote(Pp.cls.pick(a2, Bool.or(_, c), d), l) == PathPolicy.pp_pick(a2, Bool.or(b2, c2), d2, l) : Pp.Cls}
  %Equal.sym(Bool, c, c2, ec) : {Pp.demote(Pp.cls.pick(a2, Bool.or(b2, _), d), l) == PathPolicy.pp_pick(a2, Bool.or(b2, c2), d2, l) : Pp.Cls}
  %Equal.sym(Bool, d, d2, ed) : {Pp.demote(Pp.cls.pick(a2, Bool.or(b2, c2), _), l) == PathPolicy.pp_pick(a2, Bool.or(b2, c2), d2, l) : Pp.Cls}
  ps.pick(a2, Bool.or(b2, c2), d2, l)

def ps.class(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, l: Bool) -> {Pp.class_res(Pp.Pol{ro, ru, se}, Pp.Res{at, l}) == PathPolicy.pp_class(Pp.Pol{ro, ru, se}, Pp.Res{at, l}) : Pp.Cls}:
  +ecov = Equal.trans(Bool, Pp.any_covers(ru, at, Pp.below(ro, at)), PathPolicy.pp_covers_any(ru, at, Pp.below(ro, at)), PathPolicy.pp_covers_any(ru, at, PathPolicy.pp_below(ro, at)), ps.covers_any(ru, at, Pp.below(ro, at)), Equal.cong(List<&2, Nat>, Bool, low => PathPolicy.pp_covers_any(ru, at, low), Pp.below(ro, at), PathPolicy.pp_below(ro, at), ps.below(ro, at)))
  +eanc = Equal.trans(Bool, Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(ru), se), at), PathPolicy.pp_above_any(List.append(&2, List<&2, Nat>, Pp.entries(ru), se), at), PathPolicy.pp_above_any(List.append(&2, List<&2, Nat>, PathPolicy.pp_entries(ru), se), at), ps.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(ru), se), at), Equal.cong(List<&2, List<&2, Nat>>, Bool, xs => PathPolicy.pp_above_any(List.append(&2, List<&2, Nat>, xs, se), at), Pp.entries(ru), PathPolicy.pp_entries(ru), ps.entries(ru)))
  ps.class_eq(Pp.any_under(se, at), PathPolicy.pp_under_any(se, at), Pp.any_covers(ru, at, Pp.below(ro, at)), PathPolicy.pp_covers_any(ru, at, PathPolicy.pp_below(ro, at)), Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(ru), se), at), PathPolicy.pp_above_any(List.append(&2, List<&2, Nat>, PathPolicy.pp_entries(ru), se), at), Pp.any_under(ro, at), PathPolicy.pp_under_any(ro, at), l, ps.any_under(se, at), ecov, eanc, ps.any_under(ro, at))
