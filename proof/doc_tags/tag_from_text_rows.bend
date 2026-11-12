# eukhe: the proof of LAW tag_from_text_rows
#
# PROOF: by induction on rs: the first row's test is anded before the
# rest (and is associative); one row is its test and True.

import Base
import ../../bend/doc_tags.bend as Dt
import ../../laws/doc_tags.bend as DocTags

def tft.assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def tft.and_true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def tft.app(+t: List<&2, Nat>, rs: List<&2, Dt.Row>, +qs: List<&2, Dt.Row>) -> {Dt.from_text(t, List.append(&2, Dt.Row, rs, qs)) == Bool.and(Dt.from_text(t, rs), Dt.from_text(t, qs)) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +more:
      match r:
        case Dt.Row{+n, +x}:
          %Equal.sym(Bool, Dt.from_text(t, List.append(&2, Dt.Row, more, qs)), Bool.and(Dt.from_text(t, more), Dt.from_text(t, qs)), tft.app(t, more, qs)) : {Bool.and(Dt.is_line(t, n, x), _) == Bool.and(Bool.and(Dt.is_line(t, n, x), Dt.from_text(t, more)), Dt.from_text(t, qs)) : Bool}
          tft.assoc(Dt.is_line(t, n, x), Dt.from_text(t, more), Dt.from_text(t, qs))

def tft.one(+t: List<&2, Nat>, +n: Nat, +x: Nat) -> {(Dt.from_text(t, Nil{}), Dt.from_text(t, [Dt.Row{n, x}])) == (True{}, Dt.is_line(t, n, x)) : Bool & Bool}:
  %tft.and_true(Dt.is_line(t, n, x)) : {(True{}, Bool.and(Dt.is_line(t, n, x), True{})) == (True{}, _) : Bool & Bool}
  {==}

def DocTags.tag_from_text_rows(t, rs, qs, n, x):
  (tft.app(t, rs, qs), tft.one(t, n, x))
