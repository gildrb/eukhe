# eukhe: the proof of LAW selection_ffi_decides
#
# Every decoder of bend/ffi_selection.bend reads back what the spec
# spellers write for a value that fits (ent.*, from the wire round trips;
# turned around to rewrite a decode into its value); the reply encoder
# spells what sl_spell_reply spells (ent.reply). So a spelled input runs
# the model's step and answers its reply.

import Base
import ../../bend/selection.bend as M
import ../../bend/ffi_selection.bend as F
import ../../bend/wire.bend as Wr
import ../../laws/selection.bend as Selection
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ./base.bend as LS

# Decoders
# --------

def ent.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def ent.cell(c: M.Cell, +rest: String, h: {Selection.sl_cell_fits(c) == True{} : Bool}) -> {F.get_cell(Selection.sl_spell_cell(c, rest)) == Wr.Got{c, rest} : Wr.Dec<M.Cell>}:
  match c:
    case M.Cell{+r, +k}:
      +hh = h
      %ent.nat(r, Wr.put_nat(k, rest), LS.ls.and_l(LawsBase.wire_fits(r), LawsBase.wire_fits(k), hh)) : {F.get_cell.row(_) == Wr.Got{M.Cell{r, k}, rest} : Wr.Dec<M.Cell>}
      %ent.nat(k, rest, LS.ls.and_r(LawsBase.wire_fits(r), LawsBase.wire_fits(k), hh)) : {F.get_cell.col(r, _) == Wr.Got{M.Cell{r, k}, rest} : Wr.Dec<M.Cell>}
      {==}

def ent.gs(+gs: List<&2, Nat>, +rest: String, h: {Selection.sl_gs_fit(gs) == True{} : Bool}) -> {F.get_gs(Selection.sl_spell_gs(gs, rest)) == Wr.Got{gs, rest} : Wr.Dec<List<&2, Nat>>}:
  Wire.wire_list_round_trip(gs, rest, h)

def ent.wrap(w: M.Wrap, +rest: String) -> {F.get_wrap(Selection.sl_spell_wrap(w, rest)) == Wr.Got{w, rest} : Wr.Dec<M.Wrap>}:
  match w:
    case M.Single{}:
      %ent.nat(0n, rest, {==}) : {F.get_wrap.go(_) == Wr.Got{M.Single{}, rest} : Wr.Dec<M.Wrap>}
      {==}
    case M.Head{}:
      %ent.nat(1n, rest, {==}) : {F.get_wrap.go(_) == Wr.Got{M.Head{}, rest} : Wr.Dec<M.Wrap>}
      {==}
    case M.Cont{}:
      %ent.nat(2n, rest, {==}) : {F.get_wrap.go(_) == Wr.Got{M.Cont{}, rest} : Wr.Dec<M.Wrap>}
      {==}

def ent.row(+w: M.Wrap, +gs: List<&2, Nat>, +rest: String, h: {Selection.sl_gs_fit(gs) == True{} : Bool}) -> {F.get_row(Selection.sl_spell_wrap(w, Selection.sl_spell_gs(gs, rest))) == Wr.Got{M.Row{w, gs}, rest} : Wr.Dec<M.Row>}:
  %Equal.sym(Wr.Dec<M.Wrap>, F.get_wrap(Selection.sl_spell_wrap(w, Selection.sl_spell_gs(gs, rest))), Wr.Got{w, Selection.sl_spell_gs(gs, rest)}, ent.wrap(w, Selection.sl_spell_gs(gs, rest))) : {F.get_row.wrap(_) == Wr.Got{M.Row{w, gs}, rest} : Wr.Dec<M.Row>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, F.get_gs(Selection.sl_spell_gs(gs, rest)), Wr.Got{gs, rest}, ent.gs(gs, rest, h)) : {F.get_row.gs(w, _) == Wr.Got{M.Row{w, gs}, rest} : Wr.Dec<M.Row>}
  {==}

# the row loop reads back x then t
def ent.rows_go(+t: List<&2, M.Row>, x: M.Row, +rest: String, +hf: {Selection.sl_rows_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~M.Row, ~F.get_row, List.length(&2, M.Row, t), F.get_row(Selection.sl_spell_rows.items(x <> t, rest))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, M.Row>>}:
  match t:
    case Nil{}:
      match x:
        case M.Row{+w, +gs}:
          %Equal.sym(Wr.Dec<M.Row>, F.get_row(Selection.sl_spell_wrap(w, Selection.sl_spell_gs(gs, rest))), Wr.Got{M.Row{w, gs}, rest}, ent.row(w, gs, rest, LS.ls.and_l(Selection.sl_gs_fit(gs), True{}, hf))) : {Wr.get_list.go(~M.Row, ~F.get_row, 0n, _) == Wr.Got{[M.Row{w, gs}], rest} : Wr.Dec<List<&2, M.Row>>}
          {==}
    case Con{+y, +u}:
      match x:
        case M.Row{+w, +gs}:
          +more = Selection.sl_spell_rows.items(y <> u, rest)
          %Equal.sym(Wr.Dec<M.Row>, F.get_row(Selection.sl_spell_wrap(w, Selection.sl_spell_gs(gs, more))), Wr.Got{M.Row{w, gs}, more}, ent.row(w, gs, more, LS.ls.and_l(Selection.sl_gs_fit(gs), Selection.sl_rows_fit(y <> u), hf))) : {Wr.get_list.go(~M.Row, ~F.get_row, 1n+List.length(&2, M.Row, u), _) == Wr.Got{M.Row{w, gs} <> y <> u, rest} : Wr.Dec<List<&2, M.Row>>}
          %Equal.sym(Wr.Dec<List<&2, M.Row>>, Wr.get_list.go(~M.Row, ~F.get_row, List.length(&2, M.Row, u), F.get_row(Selection.sl_spell_rows.items(y <> u, rest))), Wr.Got{y <> u, rest}, ent.rows_go(u, y, rest, LS.ls.and_r(Selection.sl_gs_fit(gs), Selection.sl_rows_fit(y <> u), hf))) : {Wr.get_list.cons(M.Row, M.Row{w, gs}, _) == Wr.Got{M.Row{w, gs} <> y <> u, rest} : Wr.Dec<List<&2, M.Row>>}
          {==}

def ent.rows(+rows: List<&2, M.Row>, +rest: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, M.Row, rows)), Selection.sl_rows_fit(rows)) == True{} : Bool}) -> {Wr.get_list(~M.Row, ~F.get_row, Wr.put_nat(List.length(&2, M.Row, rows), Selection.sl_spell_rows.items(rows, rest))) == Wr.Got{rows, rest} : Wr.Dec<List<&2, M.Row>>}:
  match rows:
    case Nil{}:
      %ent.nat(0n, rest, {==}) : {Wr.get_list.start(~M.Row, ~F.get_row, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, M.Row>>}
      {==}
    case Con{+x, +t}:
      %ent.nat(List.length(&2, M.Row, x <> t), Selection.sl_spell_rows.items(x <> t, rest), LS.ls.and_l(LawsBase.wire_fits(List.length(&2, M.Row, x <> t)), Selection.sl_rows_fit(x <> t), h)) : {Wr.get_list.start(~M.Row, ~F.get_row, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, M.Row>>}
      ent.rows_go(t, x, rest, LS.ls.and_r(LawsBase.wire_fits(List.length(&2, M.Row, x <> t)), Selection.sl_rows_fit(x <> t), h))

def ent.ev(e: M.Ev, +rest: String, h: {Selection.sl_ev_fits(e) == True{} : Bool}) -> {F.get_ev(Selection.sl_spell_ev(e, rest)) == Wr.Got{e, rest} : Wr.Dec<M.Ev>}:
  match e:
    case M.EvPress{+at, +t, +gs}:
      +hh = h
      +h2 = LS.ls.and_r(Selection.sl_cell_fits(at), Bool.and(LawsBase.wire_fits(t), Selection.sl_gs_fit(gs)), hh)
      %ent.nat(0n, Selection.sl_spell_cell(at, Wr.put_nat(t, Selection.sl_spell_gs(gs, rest))), {==}) : {F.get_ev.go(_) == Wr.Got{M.EvPress{at, t, gs}, rest} : Wr.Dec<M.Ev>}
      %Equal.sym(Wr.Dec<M.Cell>, F.get_cell(Selection.sl_spell_cell(at, Wr.put_nat(t, Selection.sl_spell_gs(gs, rest)))), Wr.Got{at, Wr.put_nat(t, Selection.sl_spell_gs(gs, rest))}, ent.cell(at, Wr.put_nat(t, Selection.sl_spell_gs(gs, rest)), LS.ls.and_l(Selection.sl_cell_fits(at), Bool.and(LawsBase.wire_fits(t), Selection.sl_gs_fit(gs)), hh))) : {F.get_ev.press(_) == Wr.Got{M.EvPress{at, t, gs}, rest} : Wr.Dec<M.Ev>}
      %ent.nat(t, Selection.sl_spell_gs(gs, rest), LS.ls.and_l(LawsBase.wire_fits(t), Selection.sl_gs_fit(gs), h2)) : {F.get_ev.time(at, _) == Wr.Got{M.EvPress{at, t, gs}, rest} : Wr.Dec<M.Ev>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, F.get_gs(Selection.sl_spell_gs(gs, rest)), Wr.Got{gs, rest}, ent.gs(gs, rest, LS.ls.and_r(LawsBase.wire_fits(t), Selection.sl_gs_fit(gs), h2))) : {F.get_ev.gs(at, t, _) == Wr.Got{M.EvPress{at, t, gs}, rest} : Wr.Dec<M.Ev>}
      {==}
    case M.EvDrag{+at, +lo, +hi}:
      +hh = h
      +h2 = LS.ls.and_r(Selection.sl_cell_fits(at), Bool.and(LawsBase.wire_fits(lo), LawsBase.wire_fits(hi)), hh)
      %ent.nat(1n, Selection.sl_spell_cell(at, Wr.put_nat(lo, Wr.put_nat(hi, rest))), {==}) : {F.get_ev.go(_) == Wr.Got{M.EvDrag{at, lo, hi}, rest} : Wr.Dec<M.Ev>}
      %Equal.sym(Wr.Dec<M.Cell>, F.get_cell(Selection.sl_spell_cell(at, Wr.put_nat(lo, Wr.put_nat(hi, rest)))), Wr.Got{at, Wr.put_nat(lo, Wr.put_nat(hi, rest))}, ent.cell(at, Wr.put_nat(lo, Wr.put_nat(hi, rest)), LS.ls.and_l(Selection.sl_cell_fits(at), Bool.and(LawsBase.wire_fits(lo), LawsBase.wire_fits(hi)), hh))) : {F.get_ev.drag(_) == Wr.Got{M.EvDrag{at, lo, hi}, rest} : Wr.Dec<M.Ev>}
      %ent.nat(lo, Wr.put_nat(hi, rest), LS.ls.and_l(LawsBase.wire_fits(lo), LawsBase.wire_fits(hi), h2)) : {F.get_ev.lo(at, _) == Wr.Got{M.EvDrag{at, lo, hi}, rest} : Wr.Dec<M.Ev>}
      %ent.nat(hi, rest, LS.ls.and_r(LawsBase.wire_fits(lo), LawsBase.wire_fits(hi), h2)) : {F.get_ev.hi(at, lo, _) == Wr.Got{M.EvDrag{at, lo, hi}, rest} : Wr.Dec<M.Ev>}
      {==}
    case M.EvRelease{+rows}:
      %ent.nat(2n, Wr.put_nat(List.length(&2, M.Row, rows), Selection.sl_spell_rows.items(rows, rest)), {==}) : {F.get_ev.go(_) == Wr.Got{M.EvRelease{rows}, rest} : Wr.Dec<M.Ev>}
      %Equal.sym(Wr.Dec<List<&2, M.Row>>, Wr.get_list(~M.Row, ~F.get_row, Wr.put_nat(List.length(&2, M.Row, rows), Selection.sl_spell_rows.items(rows, rest))), Wr.Got{rows, rest}, ent.rows(rows, rest, h)) : {F.get_ev.rows(_) == Wr.Got{M.EvRelease{rows}, rest} : Wr.Dec<M.Ev>}
      {==}
    case M.EvKey{}:
      %ent.nat(3n, rest, {==}) : {F.get_ev.go(_) == Wr.Got{M.EvKey{}, rest} : Wr.Dec<M.Ev>}
      {==}
    case M.EvEsc{}:
      %ent.nat(4n, rest, {==}) : {F.get_ev.go(_) == Wr.Got{M.EvEsc{}, rest} : Wr.Dec<M.Ev>}
      {==}
    case M.EvWheel{}:
      %ent.nat(5n, rest, {==}) : {F.get_ev.go(_) == Wr.Got{M.EvWheel{}, rest} : Wr.Dec<M.Ev>}
      {==}
    case M.EvChanged{}:
      %ent.nat(6n, rest, {==}) : {F.get_ev.go(_) == Wr.Got{M.EvChanged{}, rest} : Wr.Dec<M.Ev>}
      {==}

# Reply
# -----

def ent.sel(m: Maybe<&2, M.Rng>, +rest: String) -> {F.put_sel(m, rest) == Selection.sl_spell_sel(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{r}:
      match r:
        case M.Rng{a, b}:
          match a:
            case M.Cell{ar, ac}:
              match b:
                case M.Cell{br, bc}:
                  {==}

def ent.pieces_go(ps: List<&2, M.Piece>, -rest: String) -> {Wr.put_list.go(~M.Piece, ~F.put_piece, ps, rest) == (List.length(&2, M.Piece, ps), Selection.sl_spell_pieces.items(ps, rest)) : Nat & String}:
  match ps:
    case Nil{}:
      {==}
    case Con{p, +t}:
      match p:
        case M.Piece{+row, +from, +to, +nl}:
          %Equal.sym(Nat & String, Wr.put_list.go(~M.Piece, ~F.put_piece, t, rest), (List.length(&2, M.Piece, t), Selection.sl_spell_pieces.items(t, rest)), ent.pieces_go(t, rest)) : {Wr.put_list.step(~M.Piece, ~F.put_piece, M.Piece{row, from, to, nl}, _) == (1n+List.length(&2, M.Piece, t), Wr.put_nat(row, Wr.put_nat(from, Wr.put_nat(to, Wr.put_bool(nl, Selection.sl_spell_pieces.items(t, rest)))))) : Nat & String}
          {==}

def ent.copy(m: Maybe<&2, List<&2, M.Piece>>, +rest: String) -> {F.put_copy(m, rest) == Selection.sl_spell_copy(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{+ps}:
      %Equal.sym(Nat & String, Wr.put_list.go(~M.Piece, ~F.put_piece, ps, rest), (List.length(&2, M.Piece, ps), Selection.sl_spell_pieces.items(ps, rest)), ent.pieces_go(ps, rest)) : {Wr.put_nat(1n, Wr.put_list.fin(_)) == Selection.sl_spell_copy(Some{ps}, rest) : String}
      {==}

def ent.pan(p: M.Pan, +rest: String) -> {F.put_pan(p, rest) == Selection.sl_spell_pan(p, rest) : String}:
  match p:
    case M.PanNone{}:
      {==}
    case M.PanUp{}:
      {==}
    case M.PanDown{}:
      {==}

# the stepper's answer to a model answer
def ent.reply(r: M.Res) -> {F.step.res(r) == (Selection.sl_live(r), Selection.sl_spell_reply(r)) : F.St & String}:
  match r:
    case M.Res{s, o}:
      match o:
        case M.Out{+sel, +c, +p, +e}:
          +T = Selection.sl_spell_copy(c, Selection.sl_spell_pan(p, Wr.put_bool(e, "")))
          %Equal.sym(String, F.put_pan(p, Wr.put_bool(e, "")), Selection.sl_spell_pan(p, Wr.put_bool(e, "")), ent.pan(p, Wr.put_bool(e, ""))) : {(F.Live{s}, F.put_sel(sel, F.put_copy(c, _))) == (F.Live{s}, Selection.sl_spell_sel(sel, T)) : F.St & String}
          %Equal.sym(String, F.put_copy(c, Selection.sl_spell_pan(p, Wr.put_bool(e, ""))), T, ent.copy(c, Selection.sl_spell_pan(p, Wr.put_bool(e, "")))) : {(F.Live{s}, F.put_sel(sel, _)) == (F.Live{s}, Selection.sl_spell_sel(sel, T)) : F.St & String}
          %Equal.sym(String, F.put_sel(sel, T), Selection.sl_spell_sel(sel, T), ent.sel(sel, T)) : {(F.Live{s}, _) == (F.Live{s}, Selection.sl_spell_sel(sel, T)) : F.St & String}
          {==}

def Selection.selection_ffi_decides(s, e, h):
  %Equal.sym(Wr.Dec<M.Ev>, F.get_ev(Selection.sl_spell_ev(e, "")), Wr.Got{e, ""}, ent.ev(e, "", h)) : {F.step.ev(s, _) == (Selection.sl_live(M.step(s, e)), Selection.sl_spell_reply(M.step(s, e))) : F.St & String}
  ent.reply(M.step(s, e))
