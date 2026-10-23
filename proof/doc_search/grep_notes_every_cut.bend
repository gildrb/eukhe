# eukhe: the proof of LAW grep_notes_every_cut

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def documents.ps.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      documents.ps.eq_refl(p)

# Grep: a notice for each cut file shown
# --------------------------------------

def ps.or_r(a: Bool, -y: Bool, h: {y == True{} : Bool}) -> {Bool.or(a, y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def ps.cut_keep(+i: Nat, +i2: Nat, c: Sr.Class, t: Bool, +l: List<&2, Nat>, h: {Sr.mem(i, l) == True{} : Bool}) -> {Sr.mem(i, Sr.cut.put(i2, c, t, l)) == True{} : Bool}:
  match c:
    case Sr.NoMatch{}:
      h
    case Sr.Shown{}:
      match t:
        case True{}:
          ps.or_r(Nat.is_eq(i2, i), Sr.mem(i, l), h)
        case False{}:
          h
    case Sr.PagedOut{}:
      h
    case Sr.Unsearched{}:
      h
    case Sr.Skipped{w}:
      h

# the law grep_notes_every_cut
def ps.notes_every_cut(pre: List<&2, Sr.Out>, +i: Nat, +pa: Bool, +post: List<&2, Sr.Out>) -> {Sr.mem(i, Sr.cuts(List.append(&2, Sr.Out, pre, Sr.Out{i, Sr.Shown{}, True{}, pa} <> post))) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(i, i), True{}, documents.ps.eq_refl(i)) : {Bool.or(_, Sr.mem(i, Sr.cuts(post))) == True{} : Bool}
      {==}
    case o <> +rest:
      match o:
        case Sr.Out{+i2, c, t, pa2}:
          ps.cut_keep(i, i2, c, t, Sr.cuts(List.append(&2, Sr.Out, rest, Sr.Out{i, Sr.Shown{}, True{}, pa} <> post)), ps.notes_every_cut(rest, i, pa, post))

def DocSearch.grep_notes_every_cut(pre, i, pa, post):
  ps.notes_every_cut(pre, i, pa, post)
