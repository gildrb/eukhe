# eukhe: the proof of LAW tag_line_at
#
# PROOF: index |xs| of xs ++ x <> ys is x (by induction on xs), so
# `is_line` there compares x with y.

import Base
import ../../bend/doc_tags.bend as Dt
import ../../laws/doc_tags.bend as DocTags

# the item after xs is x
def tla.get(xs: List<&2, Nat>, +x: Nat, +ys: List<&2, Nat>) -> {List.get(&2, Nat, List.append(&2, Nat, xs, x <> ys), List.length(&2, Nat, xs)) == Some{x} : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      tla.get(t, x, ys)

def DocTags.tag_line_at(xs, x, ys, y):
  %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, List.append(&2, Nat, xs, x <> ys), List.length(&2, Nat, xs)), Some{x}, tla.get(xs, x, ys)) : {Maybe.default(&2, Bool, Maybe.bind(&2, Nat, Bool, _, z => Some{Nat.is_eq(z, y)}), False{}) == Nat.is_eq(x, y) : Bool}
  {==}
