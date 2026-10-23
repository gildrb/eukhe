# eukhe: the proof of LAW tag_names_shown_text

import Base
import ../../bend/doc_tags.bend as Dt
import ../../LAWS.bend as Laws

# ==== tags ====
# proof_doc_tags: the tag law of LAWS.bend section documents (F3): the tag of a
# read or grep result names the text its rows come from.
def pdt.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pdt.eq_refl(p)

def pdt.app_assoc(xs: List<&2, Nat>, +ys: List<&2, Nat>, +zs: List<&2, Nat>) -> {List.append(&2, Nat, List.append(&2, Nat, xs, ys), zs) == List.append(&2, Nat, xs, List.append(&2, Nat, ys, zs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      %pdt.app_assoc(t, ys, zs) : {h <> List.append(&2, Nat, List.append(&2, Nat, t, ys), zs) == h <> _ : List<&2, Nat>}
      {==}

def pdt.len_snoc(pre: List<&2, Nat>, +x: Nat) -> {List.length(&2, Nat, List.append(&2, Nat, pre, [x])) == 1n+List.length(&2, Nat, pre) : Nat}:
  match pre:
    case Nil{}:
      {==}
    case h <> t:
      %pdt.len_snoc(t, x) : {1n+List.length(&2, Nat, List.append(&2, Nat, t, [x])) == 1n+_ : Nat}
      {==}

# the line after pre is x
def pdt.get_app(pre: List<&2, Nat>, +x: Nat, +rest: List<&2, Nat>) -> {List.get(&2, Nat, List.append(&2, Nat, pre, x <> rest), List.length(&2, Nat, pre)) == Some{x} : Maybe<&2, Nat>}:
  match pre:
    case Nil{}:
      {==}
    case h <> t:
      pdt.get_app(t, x, rest)

def pdt.line_at(+pre: List<&2, Nat>, +x: Nat, +rest: List<&2, Nat>) -> {Dt.is_line(List.append(&2, Nat, pre, x <> rest), 1n+List.length(&2, Nat, pre), x) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, List.append(&2, Nat, pre, x <> rest), List.length(&2, Nat, pre)), Some{x}, pdt.get_app(pre, x, rest)) : {Maybe.default(&2, Bool, Maybe.bind(&2, Nat, Bool, _, y => Some{Nat.is_eq(y, x)}), False{}) == True{} : Bool}
  pdt.eq_refl(x)

# a row of line 1 + |pre| kept or not: the rows stay lines of the text
def pdt.keep_ok(s: Bool, +pre: List<&2, Nat>, +x: Nat, +rest: List<&2, Nat>, +rs: List<&2, Dt.Row>, ih: {Dt.from_text(List.append(&2, Nat, pre, x <> rest), rs) == True{} : Bool}) -> {Dt.from_text(List.append(&2, Nat, pre, x <> rest), Dt.keep(s, Dt.Row{1n+List.length(&2, Nat, pre), x}, rs)) == True{} : Bool}:
  match s:
    case True{}:
      %Equal.sym(Bool, Dt.is_line(List.append(&2, Nat, pre, x <> rest), 1n+List.length(&2, Nat, pre), x), True{}, pdt.line_at(pre, x, rest)) : {Bool.and(_, Dt.from_text(List.append(&2, Nat, pre, x <> rest), rs)) == True{} : Bool}
      ih
    case False{}:
      ih

# the rows after line x, seen from pre ++ [x]
def pdt.shift(+rest: List<&2, Nat>, +more: List<&2, Bool>, +pre: List<&2, Nat>, +x: Nat, ih: {Dt.from_text(List.append(&2, Nat, List.append(&2, Nat, pre, [x]), rest), Dt.rows(rest, more, 1n+List.length(&2, Nat, List.append(&2, Nat, pre, [x])))) == True{} : Bool}) -> {Dt.from_text(List.append(&2, Nat, pre, x <> rest), Dt.rows(rest, more, 1n+(1n+List.length(&2, Nat, pre)))) == True{} : Bool}:
  %pdt.app_assoc(pre, [x], rest) : {Dt.from_text(_, Dt.rows(rest, more, 1n+(1n+List.length(&2, Nat, pre)))) == True{} : Bool}
  %pdt.len_snoc(pre, x) : {Dt.from_text(List.append(&2, Nat, List.append(&2, Nat, pre, [x]), rest), Dt.rows(rest, more, 1n+_)) == True{} : Bool}
  ih

# every row cut from the lines ts after the lines pre is a line of
# pre ++ ts
def pdt.rows_from(ts: List<&2, Nat>, sel: List<&2, Bool>, +pre: List<&2, Nat>) -> {Dt.from_text(List.append(&2, Nat, pre, ts), Dt.rows(ts, sel, 1n+List.length(&2, Nat, pre))) == True{} : Bool}:
  match ts:
    case Nil{}:
      {==}
    case +x <> +rest:
      match sel:
        case Nil{}:
          {==}
        case s <> +more:
          pdt.keep_ok(s, pre, x, rest, Dt.rows(rest, more, 1n+(1n+List.length(&2, Nat, pre))), pdt.shift(rest, more, pre, x, pdt.rows_from(rest, more, List.append(&2, Nat, pre, [x]))))

# the law tag_names_shown_text
def pdt.tag_names(+t: List<&2, Nat>, op: Dt.Op) -> {Dt.Shown.tag(Dt.show(t, op)) == t : List<&2, Nat>} & {Dt.from_text(t, Dt.Shown.rows(Dt.show(t, op))) == True{} : Bool}:
  match op:
    case Dt.Read{sel}:
      ({==}, pdt.rows_from(t, sel, Nil{}))
    case Dt.Grep{sel, later}:
      ({==}, pdt.rows_from(t, sel, Nil{}))

# (F3) Tags

def Laws.tag_names_shown_text(t, op):
  pdt.tag_names(t, op)
