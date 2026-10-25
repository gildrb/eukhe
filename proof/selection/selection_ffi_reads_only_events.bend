# eukhe: the proof of LAW selection_ffi_reads_only_events
#
# Every decoder answer says what it read (ro.P*: the input is the
# spelling of the value read and what follows, and the value fits), stage
# by stage from the wire's exactness laws (wire_nat_exact,
# wire_nat_decoded_fits). An answer without the error form read an input
# with nothing left over; that input is the spelling of the event, which
# fits, and the stepper answers the model's step on it (LAW
# selection_ffi_decides).

import Base
import ../../bend/selection.bend as M
import ../../bend/ffi_selection.bend as F
import ../../bend/wire.bend as Wr
import ../../laws/selection.bend as Selection
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/string.bend as LLogicString
import ../base/wire.bend as LWire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ./base.bend as LS
import ./selection_ffi_decides.bend as PSelectionFfiDecides

# Nat
# ---

def ro.Pnat(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{+n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ro.nat.k(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ro.Pnat(s, d):
  match d:
    case Wr.Got{+n, +r}:
      (Wire.wire_nat_exact(s, n, r, ed), Wire.wire_nat_decoded_fits(s, n, r, ed))
    case Wr.Bad{}:
      Unit{}

def ro.nat(+s: String) -> ro.Pnat(s, Wr.get_nat(s)):
  ro.nat.k(s, Wr.get_nat(s), {==})

# Cell
# ----

def ro.Pcell(s: String, d: Wr.Dec<M.Cell>) -> Type:
  match d:
    case Wr.Got{+c, r}:
      {s == Selection.sl_spell_cell(c, r) : String} & {Selection.sl_cell_fits(c) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ro.cell.col(-s: String, +row: Nat, -s1: String, fr: {LawsBase.wire_fits(row) == True{} : Bool}, e1: {s == Wr.put_nat(row, s1) : String}, d: Wr.Dec<Nat>, p: ro.Pnat(s1, d)) -> ro.Pcell(s, F.get_cell.col(row, d)):
  match d:
    case Wr.Got{+col, +s2}:
      (e2, f2) = p
      (Equal.trans(String, s, Wr.put_nat(row, s1), Wr.put_nat(row, Wr.put_nat(col, s2)), e1, Equal.cong(String, String, z => Wr.put_nat(row, z), s1, Wr.put_nat(col, s2), e2)), LS.ls.and_tt(LawsBase.wire_fits(row), LawsBase.wire_fits(col), fr, f2))
    case Wr.Bad{}:
      Unit{}

def ro.cell.row(+s: String, d: Wr.Dec<Nat>, p: ro.Pnat(s, d)) -> ro.Pcell(s, F.get_cell.row(d)):
  match d:
    case Wr.Got{+row, +s1}:
      (e1, f1) = p
      ro.cell.col(s, row, s1, f1, e1, Wr.get_nat(s1), ro.nat(s1))
    case Wr.Bad{}:
      Unit{}

def ro.cell(+s: String) -> ro.Pcell(s, F.get_cell(s)):
  ro.cell.row(s, Wr.get_nat(s), ro.nat(s))

# Glyphs
# ------

def ro.Pgs(s: String, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Selection.sl_spell_gs(xs, r) : String} & {Selection.sl_gs_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# what the item loop's answer says about its input s (m + 1 items)
def ro.Pl(s: String, m: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == LLogicString.wr_items(xs, r) : String} & ({List.length(&2, Nat, xs) == 1n+m : Nat} & {LawsBase.wire_nats_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def ro.gs.step(-s: String, +x: Nat, +s3: String, -k: Nat, ex: {s == Wr.put_nat(x, s3) : String}, fx: {LawsBase.wire_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ih: ro.Pl(s3, k, d)) -> ro.Pl(s, 1n+k, Wr.get_list.cons(Nat, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, rest) = ih
      (e2, e3) = rest
      (Equal.trans(String, s, Wr.put_nat(x, s3), Wr.put_nat(x, LLogicString.wr_items(ys, r)), ex, Equal.cong(String, String, z => Wr.put_nat(x, z), s3, LLogicString.wr_items(ys, r), e1)), (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Nat, ys), 1n+k, e2), LS.ls.and_tt(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def ro.gs.spec(m: Nat, cur: Wr.Dec<Nat>, +s: String, p: ro.Pnat(s, cur)) -> ro.Pl(s, m, Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = p
      (e, ({==}, LS.ls.and_tt(LawsBase.wire_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = p
      ro.gs.step(s, x, s3, k, e, f, Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(s3)), ro.gs.spec(k, Wr.get_nat(s3), s3, ro.nat(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def ro.gs.eq(+s: String, -s2: String, +m: Nat, +xs: List<&2, Nat>, +r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == LLogicString.wr_items(xs, r) : String}, e2: {List.length(&2, Nat, xs) == 1n+m : Nat}) -> {s == Selection.sl_spell_gs(xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, xs, r), Wr.put_nat(List.length(&2, Nat, xs), LLogicString.wr_items(xs, r)), LWire.wr_put_list(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e2) : {s == Wr.put_nat(_, LLogicString.wr_items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def ro.gs.fit(+m: Nat, +xs: List<&2, Nat>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Nat, xs) == 1n+m : Nat}, e3: {LawsBase.wire_nats_fit(xs) == True{} : Bool}) -> {Selection.sl_gs_fit(xs) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
  LS.ls.and_tt(LawsBase.wire_fits(1n+m), LawsBase.wire_nats_fit(xs), fn, e3)

def ro.gs.conv(+s: String, +s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, pl: ro.Pl(s2, m, d)) -> ro.Pgs(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, rest) = pl
      (e2, e3) = rest
      +he2 = e2
      (ro.gs.eq(s, s2, m, xs, r, en, e1, he2), ro.gs.fit(m, xs, fn, he2, e3))
    case Wr.Bad{}:
      Unit{}

def ro.gs.nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> ro.Pgs(s, Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      ro.gs.conv(s, s2, m, en, fn, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s2)), ro.gs.spec(m, Wr.get_nat(s2), s2, ro.nat(s2)))

def ro.gs.top(+s: String, d: Wr.Dec<Nat>, p: ro.Pnat(s, d)) -> ro.Pgs(s, Wr.get_list.start(~Nat, ~Wr.get_nat, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (en, fn) = p
      ro.gs.nat(s, n, s2, en, fn)
    case Wr.Bad{}:
      Unit{}

def ro.gs(+s: String) -> ro.Pgs(s, F.get_gs(s)):
  ro.gs.top(s, Wr.get_nat(s), ro.nat(s))

# Rows
# ----

def ro.Pwrap(s: String, d: Wr.Dec<M.Wrap>) -> Type:
  match d:
    case Wr.Got{+w, r}:
      {s == Selection.sl_spell_wrap(w, r) : String}
    case Wr.Bad{}:
      Unit

def ro.wrap.tag(n: Nat, -s: String, +s1: String, en: {s == Wr.put_nat(n, s1) : String}) -> ro.Pwrap(s, F.get_wrap.tag(n, s1)):
  match n:
    case 0n:
      en
    case 1n+a:
      match a:
        case 0n:
          en
        case 1n+b:
          match b:
            case 0n:
              en
            case 1n+c:
              Unit{}

def ro.wrap(+s: String, d: Wr.Dec<Nat>, p: ro.Pnat(s, d)) -> ro.Pwrap(s, F.get_wrap.go(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (en, fn) = p
      ro.wrap.tag(n, s, s1, en)
    case Wr.Bad{}:
      Unit{}

def ro.spell_row(row: M.Row, r: String) -> String:
  match row:
    case M.Row{w, gs}:
      Selection.sl_spell_wrap(w, Selection.sl_spell_gs(gs, r))

def ro.row_fit(row: M.Row) -> Bool:
  match row:
    case M.Row{w, gs}:
      Selection.sl_gs_fit(gs)

def ro.Prow(s: String, d: Wr.Dec<M.Row>) -> Type:
  match d:
    case Wr.Got{+row, r}:
      {s == ro.spell_row(row, r) : String} & {ro.row_fit(row) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ro.row.gs(-s: String, +w: M.Wrap, -s1: String, ew: {s == Selection.sl_spell_wrap(w, s1) : String}, d: Wr.Dec<List<&2, Nat>>, p: ro.Pgs(s1, d)) -> ro.Prow(s, F.get_row.gs(w, d)):
  match d:
    case Wr.Got{+gs, +r}:
      (eg, fg) = p
      (Equal.trans(String, s, Selection.sl_spell_wrap(w, s1), Selection.sl_spell_wrap(w, Selection.sl_spell_gs(gs, r)), ew, Equal.cong(String, String, z => Selection.sl_spell_wrap(w, z), s1, Selection.sl_spell_gs(gs, r), eg)), fg)
    case Wr.Bad{}:
      Unit{}

def ro.row.wrap(+s: String, d: Wr.Dec<M.Wrap>, p: ro.Pwrap(s, d)) -> ro.Prow(s, F.get_row.wrap(d)):
  match d:
    case Wr.Got{+w, +s1}:
      ro.row.gs(s, w, s1, p, F.get_gs(s1), ro.gs(s1))
    case Wr.Bad{}:
      Unit{}

def ro.row(+s: String) -> ro.Prow(s, F.get_row(s)):
  ro.row.wrap(s, F.get_wrap(s), ro.wrap(s, Wr.get_nat(s), ro.nat(s)))

def ro.Prl(s: String, m: Nat, d: Wr.Dec<List<&2, M.Row>>) -> Type:
  match d:
    case Wr.Got{+rows, r}:
      {s == Selection.sl_spell_rows.items(rows, r) : String} & ({List.length(&2, M.Row, rows) == 1n+m : Nat} & {Selection.sl_rows_fit(rows) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def ro.rows.step(-s: String, x: M.Row, +s3: String, -k: Nat, ex: {s == ro.spell_row(x, s3) : String}, fx: {ro.row_fit(x) == True{} : Bool}, d: Wr.Dec<List<&2, M.Row>>, ih: ro.Prl(s3, k, d)) -> ro.Prl(s, 1n+k, Wr.get_list.cons(M.Row, x, d)):
  match x:
    case M.Row{+w, +gs}:
      match d:
        case Wr.Got{+ys, +r}:
          (e1, rest) = ih
          (e2, e3) = rest
          (Equal.trans(String, s, ro.spell_row(M.Row{w, gs}, s3), ro.spell_row(M.Row{w, gs}, Selection.sl_spell_rows.items(ys, r)), ex, Equal.cong(String, String, z => ro.spell_row(M.Row{w, gs}, z), s3, Selection.sl_spell_rows.items(ys, r), e1)), (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, M.Row, ys), 1n+k, e2), LS.ls.and_tt(Selection.sl_gs_fit(gs), Selection.sl_rows_fit(ys), fx, e3)))
        case Wr.Bad{}:
          Unit{}

def ro.rows.one(x: M.Row, -s: String, +s3: String, e: {s == ro.spell_row(x, s3) : String}, f: {ro.row_fit(x) == True{} : Bool}) -> ro.Prl(s, 0n, Wr.Got{[x], s3}):
  match x:
    case M.Row{w, gs}:
      (e, ({==}, LS.ls.and_tt(Selection.sl_gs_fit(gs), True{}, f, {==})))

def ro.rows.spec(m: Nat, cur: Wr.Dec<M.Row>, +s: String, p: ro.Prow(s, cur)) -> ro.Prl(s, m, Wr.get_list.go(~M.Row, ~F.get_row, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = p
      ro.rows.one(x, s, s3, e, f)
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = p
      ro.rows.step(s, x, s3, k, e, f, Wr.get_list.go(~M.Row, ~F.get_row, k, F.get_row(s3)), ro.rows.spec(k, F.get_row(s3), s3, ro.row(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def ro.Prows(s: String, d: Wr.Dec<List<&2, M.Row>>) -> Type:
  match d:
    case Wr.Got{+rows, r}:
      {s == Wr.put_nat(List.length(&2, M.Row, rows), Selection.sl_spell_rows.items(rows, r)) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, M.Row, rows)), Selection.sl_rows_fit(rows)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ro.rows.eq(+s: String, -s2: String, +m: Nat, +rows: List<&2, M.Row>, +r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == Selection.sl_spell_rows.items(rows, r) : String}, e2: {List.length(&2, M.Row, rows) == 1n+m : Nat}) -> {s == Wr.put_nat(List.length(&2, M.Row, rows), Selection.sl_spell_rows.items(rows, r)) : String}:
  %Equal.sym(Nat, List.length(&2, M.Row, rows), 1n+m, e2) : {s == Wr.put_nat(_, Selection.sl_spell_rows.items(rows, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def ro.rows.fit(+m: Nat, +rows: List<&2, M.Row>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, M.Row, rows) == 1n+m : Nat}, e3: {Selection.sl_rows_fit(rows) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, M.Row, rows)), Selection.sl_rows_fit(rows)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, M.Row, rows), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), Selection.sl_rows_fit(rows)) == True{} : Bool}
  LS.ls.and_tt(LawsBase.wire_fits(1n+m), Selection.sl_rows_fit(rows), fn, e3)

def ro.rows.conv(+s: String, +s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, M.Row>>, pl: ro.Prl(s2, m, d)) -> ro.Prows(s, d):
  match d:
    case Wr.Got{+rows, +r}:
      (e1, rest) = pl
      (e2, e3) = rest
      +he2 = e2
      (ro.rows.eq(s, s2, m, rows, r, en, e1, he2), ro.rows.fit(m, rows, fn, he2, e3))
    case Wr.Bad{}:
      Unit{}

def ro.rows.nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> ro.Prows(s, Wr.get_list.start(~M.Row, ~F.get_row, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      ro.rows.conv(s, s2, m, en, fn, Wr.get_list.go(~M.Row, ~F.get_row, m, F.get_row(s2)), ro.rows.spec(m, F.get_row(s2), s2, ro.row(s2)))

def ro.rows.top(+s: String, d: Wr.Dec<Nat>, p: ro.Pnat(s, d)) -> ro.Prows(s, Wr.get_list.start(~M.Row, ~F.get_row, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (en, fn) = p
      ro.rows.nat(s, n, s2, en, fn)
    case Wr.Bad{}:
      Unit{}

def ro.rows(+s: String) -> ro.Prows(s, Wr.get_list(~M.Row, ~F.get_row, s)):
  ro.rows.top(s, Wr.get_nat(s), ro.nat(s))

# Events
# ------

def ro.Pev(s: String, d: Wr.Dec<M.Ev>) -> Type:
  match d:
    case Wr.Got{+e, r}:
      {s == Selection.sl_spell_ev(e, r) : String} & {Selection.sl_ev_fits(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ro.ev.gs(-s: String, +at: M.Cell, +t: Nat, -s2: String, e2: {s == Wr.put_nat(0n, Selection.sl_spell_cell(at, Wr.put_nat(t, s2))) : String}, fat: {Selection.sl_cell_fits(at) == True{} : Bool}, ft: {LawsBase.wire_fits(t) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, p: ro.Pgs(s2, d)) -> ro.Pev(s, F.get_ev.gs(at, t, d)):
  match d:
    case Wr.Got{+gs, +r}:
      (eg, fg) = p
      (Equal.trans(String, s, Wr.put_nat(0n, Selection.sl_spell_cell(at, Wr.put_nat(t, s2))), Wr.put_nat(0n, Selection.sl_spell_cell(at, Wr.put_nat(t, Selection.sl_spell_gs(gs, r)))), e2, Equal.cong(String, String, z => Wr.put_nat(0n, Selection.sl_spell_cell(at, Wr.put_nat(t, z))), s2, Selection.sl_spell_gs(gs, r), eg)), LS.ls.and_tt(Selection.sl_cell_fits(at), Bool.and(LawsBase.wire_fits(t), Selection.sl_gs_fit(gs)), fat, LS.ls.and_tt(LawsBase.wire_fits(t), Selection.sl_gs_fit(gs), ft, fg)))
    case Wr.Bad{}:
      Unit{}

def ro.ev.time(-s: String, +at: M.Cell, -s1: String, e1: {s == Wr.put_nat(0n, Selection.sl_spell_cell(at, s1)) : String}, fat: {Selection.sl_cell_fits(at) == True{} : Bool}, d: Wr.Dec<Nat>, p: ro.Pnat(s1, d)) -> ro.Pev(s, F.get_ev.time(at, d)):
  match d:
    case Wr.Got{+t, +s2}:
      (et, ft) = p
      ro.ev.gs(s, at, t, s2, Equal.trans(String, s, Wr.put_nat(0n, Selection.sl_spell_cell(at, s1)), Wr.put_nat(0n, Selection.sl_spell_cell(at, Wr.put_nat(t, s2))), e1, Equal.cong(String, String, z => Wr.put_nat(0n, Selection.sl_spell_cell(at, z)), s1, Wr.put_nat(t, s2), et)), fat, ft, F.get_gs(s2), ro.gs(s2))
    case Wr.Bad{}:
      Unit{}

def ro.ev.press(-s: String, -s0: String, e0: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<M.Cell>, p: ro.Pcell(s0, d)) -> ro.Pev(s, F.get_ev.press(d)):
  match d:
    case Wr.Got{+at, +s1}:
      (ec, fc) = p
      ro.ev.time(s, at, s1, Equal.trans(String, s, Wr.put_nat(0n, s0), Wr.put_nat(0n, Selection.sl_spell_cell(at, s1)), e0, Equal.cong(String, String, z => Wr.put_nat(0n, z), s0, Selection.sl_spell_cell(at, s1), ec)), fc, Wr.get_nat(s1), ro.nat(s1))
    case Wr.Bad{}:
      Unit{}

def ro.ev.hi(-s: String, +at: M.Cell, +lo: Nat, -s2: String, e2: {s == Wr.put_nat(1n, Selection.sl_spell_cell(at, Wr.put_nat(lo, s2))) : String}, fat: {Selection.sl_cell_fits(at) == True{} : Bool}, flo: {LawsBase.wire_fits(lo) == True{} : Bool}, d: Wr.Dec<Nat>, p: ro.Pnat(s2, d)) -> ro.Pev(s, F.get_ev.hi(at, lo, d)):
  match d:
    case Wr.Got{+hi, +r}:
      (eh, fh) = p
      (Equal.trans(String, s, Wr.put_nat(1n, Selection.sl_spell_cell(at, Wr.put_nat(lo, s2))), Wr.put_nat(1n, Selection.sl_spell_cell(at, Wr.put_nat(lo, Wr.put_nat(hi, r)))), e2, Equal.cong(String, String, z => Wr.put_nat(1n, Selection.sl_spell_cell(at, Wr.put_nat(lo, z))), s2, Wr.put_nat(hi, r), eh)), LS.ls.and_tt(Selection.sl_cell_fits(at), Bool.and(LawsBase.wire_fits(lo), LawsBase.wire_fits(hi)), fat, LS.ls.and_tt(LawsBase.wire_fits(lo), LawsBase.wire_fits(hi), flo, fh)))
    case Wr.Bad{}:
      Unit{}

def ro.ev.lo(-s: String, +at: M.Cell, -s1: String, e1: {s == Wr.put_nat(1n, Selection.sl_spell_cell(at, s1)) : String}, fat: {Selection.sl_cell_fits(at) == True{} : Bool}, d: Wr.Dec<Nat>, p: ro.Pnat(s1, d)) -> ro.Pev(s, F.get_ev.lo(at, d)):
  match d:
    case Wr.Got{+lo, +s2}:
      (el, fl) = p
      ro.ev.hi(s, at, lo, s2, Equal.trans(String, s, Wr.put_nat(1n, Selection.sl_spell_cell(at, s1)), Wr.put_nat(1n, Selection.sl_spell_cell(at, Wr.put_nat(lo, s2))), e1, Equal.cong(String, String, z => Wr.put_nat(1n, Selection.sl_spell_cell(at, z)), s1, Wr.put_nat(lo, s2), el)), fat, fl, Wr.get_nat(s2), ro.nat(s2))
    case Wr.Bad{}:
      Unit{}

def ro.ev.drag(-s: String, -s0: String, e0: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<M.Cell>, p: ro.Pcell(s0, d)) -> ro.Pev(s, F.get_ev.drag(d)):
  match d:
    case Wr.Got{+at, +s1}:
      (ec, fc) = p
      ro.ev.lo(s, at, s1, Equal.trans(String, s, Wr.put_nat(1n, s0), Wr.put_nat(1n, Selection.sl_spell_cell(at, s1)), e0, Equal.cong(String, String, z => Wr.put_nat(1n, z), s0, Selection.sl_spell_cell(at, s1), ec)), fc, Wr.get_nat(s1), ro.nat(s1))
    case Wr.Bad{}:
      Unit{}

def ro.ev.rows(-s: String, -s0: String, e0: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<List<&2, M.Row>>, p: ro.Prows(s0, d)) -> ro.Pev(s, F.get_ev.rows(d)):
  match d:
    case Wr.Got{+rows, +r}:
      (er, fr) = p
      (Equal.trans(String, s, Wr.put_nat(2n, s0), Wr.put_nat(2n, Wr.put_nat(List.length(&2, M.Row, rows), Selection.sl_spell_rows.items(rows, r))), e0, Equal.cong(String, String, z => Wr.put_nat(2n, z), s0, Wr.put_nat(List.length(&2, M.Row, rows), Selection.sl_spell_rows.items(rows, r)), er)), fr)
    case Wr.Bad{}:
      Unit{}

def ro.ev.tag(n: Nat, +s: String, +s1: String, en: {s == Wr.put_nat(n, s1) : String}) -> ro.Pev(s, F.get_ev.tag(n, s1)):
  match n:
    case 0n:
      ro.ev.press(s, s1, en, F.get_cell(s1), ro.cell(s1))
    case 1n+a:
      match a:
        case 0n:
          ro.ev.drag(s, s1, en, F.get_cell(s1), ro.cell(s1))
        case 1n+b:
          match b:
            case 0n:
              ro.ev.rows(s, s1, en, Wr.get_list(~M.Row, ~F.get_row, s1), ro.rows(s1))
            case 1n+c:
              match c:
                case 0n:
                  (en, {==})
                case 1n+d:
                  match d:
                    case 0n:
                      (en, {==})
                    case 1n+f:
                      match f:
                        case 0n:
                          (en, {==})
                        case 1n+g:
                          match g:
                            case 0n:
                              (en, {==})
                            case 1n+x:
                              Unit{}

def ro.ev(+s: String, d: Wr.Dec<Nat>, p: ro.Pnat(s, d)) -> ro.Pev(s, F.get_ev.go(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (en, fn) = p
      ro.ev.tag(n, s, s1, en)
    case Wr.Bad{}:
      Unit{}

# The answer
# ----------

def ro.Goal(+s: M.St, +str: String) -> Type:
  Exists(M.Ev, ev => {(str, (Selection.sl_ev_fits(ev), F.step(F.Live{s}, str))) == (Selection.sl_spell_ev(ev, ""), (True{}, (Selection.sl_live(M.step(s, ev)), Selection.sl_spell_reply(M.step(s, ev))))) : String & (Bool & (F.St & String))})

def ro.fin.eq(+s: M.St, +e: M.Ev, +str: String, ex: {str == Selection.sl_spell_ev(e, "") : String}, +fe: {Selection.sl_ev_fits(e) == True{} : Bool}) -> {(str, (Selection.sl_ev_fits(e), F.step(F.Live{s}, str))) == (Selection.sl_spell_ev(e, ""), (True{}, (Selection.sl_live(M.step(s, e)), Selection.sl_spell_reply(M.step(s, e))))) : String & (Bool & (F.St & String))}:
  %Equal.sym(String, str, Selection.sl_spell_ev(e, ""), ex) : {(_, (Selection.sl_ev_fits(e), F.step(F.Live{s}, _))) == (Selection.sl_spell_ev(e, ""), (True{}, (Selection.sl_live(M.step(s, e)), Selection.sl_spell_reply(M.step(s, e))))) : String & (Bool & (F.St & String))}
  %Equal.sym(Bool, Selection.sl_ev_fits(e), True{}, fe) : {(Selection.sl_spell_ev(e, ""), (_, F.step(F.Live{s}, Selection.sl_spell_ev(e, "")))) == (Selection.sl_spell_ev(e, ""), (True{}, (Selection.sl_live(M.step(s, e)), Selection.sl_spell_reply(M.step(s, e))))) : String & (Bool & (F.St & String))}
  %Equal.sym(F.St & String, F.step(F.Live{s}, Selection.sl_spell_ev(e, "")), (Selection.sl_live(M.step(s, e)), Selection.sl_spell_reply(M.step(s, e))), Selection.selection_ffi_decides(s, e, fe)) : {(Selection.sl_spell_ev(e, ""), (True{}, _)) == (Selection.sl_spell_ev(e, ""), (True{}, (Selection.sl_live(M.step(s, e)), Selection.sl_spell_reply(M.step(s, e))))) : String & (Bool & (F.St & String))}
  {==}

def ro.fin.rest(r: String, +s: M.St, +e: M.Ev, +str: String, ex: {str == Selection.sl_spell_ev(e, r) : String}, +fe: {Selection.sl_ev_fits(e) == True{} : Bool}, ok: {LawsBase.wire_opens_err(Pair.snd(F.St, String, F.step.end(String.is_empty(r), s, e))) == False{} : Bool}) -> ro.Goal(s, str):
  match r:
    case SNil{}:
      (e, ro.fin.eq(s, e, str, ex, fe))
    case SCon{c, r2}:
      LS.ls.absurd_t(ro.Goal(s, str), ok)

def ro.fin(d: Wr.Dec<M.Ev>, +s: M.St, +str: String, p: ro.Pev(str, d), ok: {LawsBase.wire_opens_err(Pair.snd(F.St, String, F.step.ev(s, d))) == False{} : Bool}) -> ro.Goal(s, str):
  match d:
    case Wr.Got{+e, +r}:
      (ex, fe) = p
      ro.fin.rest(r, s, e, str, ex, fe, ok)
    case Wr.Bad{}:
      LS.ls.absurd_t(ro.Goal(s, str), ok)

def Selection.selection_ffi_reads_only_events(s, str, ok):
  ro.fin(F.get_ev(str), s, str, ro.ev(str, Wr.get_nat(str), ro.nat(str)), ok)
