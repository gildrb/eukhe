# eukhe: the proof of LAW rows_view_shows

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/doc_rows.bend as Dr
import ../../laws/doc_rows.bend as DocRows
import ./rows_view_shows/count.bend as Cnt
import ./rows_view_shows/window.bend as Win
import ./rows_view_shows/ranges.bend as Rng

# a selector is raw for the code as for the rule
def rvs.raw(s: Dr.Sel) -> {Dr.Sel.raw(s) == DocRows.rows.Raw(s) : Bool}:
  match s:
    case Dr.Whole{}:
      {==}
    case Dr.Raw{}:
      {==}
    case Dr.Lines{xs, raw}:
      {==}

# what a selector shows of a file of t lines: the rule's spans and notices
def rvs.sel(s: Dr.Sel, +t: Nat) -> {Dr.view.sel(s, t) == DocRows.rows.Shown(s, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}:
  match s:
    case Dr.Whole{}:
      Win.rvs.at(1n, False{}, None{}, t)
    case Dr.Raw{}:
      %Equal.sym(List<&2, Dr.Span>, Dr.span.of(1n, t), DocRows.rows.Span(1n, t), Win.rvs.span_of(1n, t)) : {(_, Nil{}) == (DocRows.rows.Span(1n, t), Nil{}) : List<&2, Dr.Span> & List<&2, Dr.Note>}
      {==}
    case Dr.Lines{xs, +raw}:
      match xs:
        case Nil{}:
          Win.rvs.at(1n, raw, None{}, t)
        case x <> rest:
          match x:
            case Dr.Range{+st, +m}:
              match rest:
                case Nil{}:
                  Win.rvs.at(st, raw, m, t)
                case y <> more:
                  Rng.rvs.rng(Dr.Range{st, m} <> y <> more, raw, None{}, t)

# the view of the shown lines: the rule's notices and tag
def rvs.fin(+t: Nat, +raw: Bool, r: List<&2, Dr.Span> & List<&2, Dr.Note>, +utf8: Bool, over: Bool) -> {Dr.view.fin(t, raw, r, utf8, over) == DocRows.rows.View.fin(t, raw, utf8, over, r) : Dr.View}:
  match r:
    case (sp, ns):
      match over:
        case True{}:
          {==}
        case False{}:
          {==}

# the view of what a selector shows of a file of t lines
def rvs.fin_sel(+s: Dr.Sel, +t: Nat, +raw: Bool, +utf8: Bool, +over: Bool) -> {Dr.view.fin(t, raw, Dr.view.sel(s, t), utf8, over) == DocRows.rows.View.fin(t, raw, utf8, over, DocRows.rows.Shown(s, t)) : Dr.View}:
  %Equal.sym(List<&2, Dr.Span> & List<&2, Dr.Note>, Dr.view.sel(s, t), DocRows.rows.Shown(s, t), rvs.sel(s, t)) : {Dr.view.fin(t, raw, _, utf8, over) == DocRows.rows.View.fin(t, raw, utf8, over, DocRows.rows.Shown(s, t)) : Dr.View}
  rvs.fin(t, raw, DocRows.rows.Shown(s, t), utf8, over)

def DocRows.rows_view_shows(s, utf8, over, b, ls):
  %Equal.sym(Bool, Dr.Sel.raw(s), DocRows.rows.Raw(s), rvs.raw(s)) : {Dr.view.fin(Dr.total(_, ls), _, Dr.view.sel(s, Dr.total(_, ls)), utf8, over) == DocRows.rows.View(s, utf8, over, ls) : Dr.View}
  %Equal.sym(Nat, Dr.total(DocRows.rows.Raw(s), ls), DocRows.rows.If(Nat, DocRows.rows.Raw(s), List.length(&2, Dl.Line, ls), DocRows.rows.Count(ls)), Cnt.rvs.total(DocRows.rows.Raw(s), ls)) : {Dr.view.fin(_, DocRows.rows.Raw(s), Dr.view.sel(s, _), utf8, over) == DocRows.rows.View(s, utf8, over, ls) : Dr.View}
  rvs.fin_sel(s, DocRows.rows.If(Nat, DocRows.rows.Raw(s), List.length(&2, Dl.Line, ls), DocRows.rows.Count(ls)), DocRows.rows.Raw(s), utf8, over)
