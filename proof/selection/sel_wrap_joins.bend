# eukhe: the proof of LAW sel_wrap_joins

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ./base.bend as LS
import ./sel_release_copies.bend as PSelReleaseCopies

# The release copies sl_copy of its range (LAW sel_release_copies). The
# spec puts a newline only before a row that does not continue the row
# above, and glyph tokens hold none; over a row and its continuations
# there is no such row.

def swj.toks(xs: List<&2, Selection.SlGl>, +i: Nat) -> {Selection.sl_nls(Selection.sl_toks(xs, i)) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case Selection.SlGl{j, g}:
          swj.toks(rest, i)

def swj.app(xs: List<&2, Selection.SlTok>, -ys: List<&2, Selection.SlTok>, hx: {Selection.sl_nls(xs) == 0n : Nat}, hy: {Selection.sl_nls(ys) == 0n : Nat}) -> {Selection.sl_nls(List.append(&2, Selection.SlTok, xs, ys)) == 0n : Nat}:
  match xs:
    case Nil{}:
      hy
    case Con{x, rest}:
      match x:
        case Selection.SlG{r, i}:
          swj.app(rest, ys, hx, hy)
        case Selection.SlNl{}:
          LS.ls.succ_zero({Selection.sl_nls(List.append(&2, Selection.SlTok, Selection.SlNl{} <> rest, ys)) == 0n : Nat}, Selection.sl_nls(rest), hx)

def swj.k(b: Bool, x: List<&2, Selection.SlTok>, -y: List<&2, Selection.SlTok>, hx: {Selection.sl_nls(x) == 0n : Nat}, hy: {Selection.sl_nls(y) == 0n : Nat}) -> {Selection.sl_nls(Selection.sl_rows.k(b, x, y)) == 0n : Nat}:
  match b:
    case True{}:
      swj.app(x, y, hx, hy)
    case False{}:
      {==}

# rows from 1 + i on, each continuing the row above, add no newline
def swj.conts(rows: List<&2, M.Row>, +i: Nat, +a: M.Cell, +b: M.Cell, hc: {Selection.sl_all_cont(rows) == True{} : Bool}) -> {Selection.sl_nls(Selection.sl_rows(rows, 1n+i, a, b)) == 0n : Nat}:
  match rows:
    case Nil{}:
      {==}
    case Con{row, +rest}:
      match row:
        case M.Row{w, +gs}:
          match w:
            case M.Single{}:
              LS.ls.absurd({Selection.sl_nls(Selection.sl_rows(M.Row{M.Single{}, gs} <> rest, 1n+i, a, b)) == 0n : Nat}, hc)
            case M.Head{}:
              LS.ls.absurd({Selection.sl_nls(Selection.sl_rows(M.Row{M.Head{}, gs} <> rest, 1n+i, a, b)) == 0n : Nat}, hc)
            case M.Cont{}:
              +R = Nat.add(1n+i, Selection.sl_row_of(a))
              +T = Bool.or(Nat.is_eq(R, Selection.sl_row_of(b)), Selection.sl_next_brk(rest))
              +TOKS = Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, R, a, b), T), 1n+i)
              swj.k(Nat.is_le(R, Selection.sl_row_of(b)), TOKS, Selection.sl_rows(rest, 2n+i, a, b), swj.toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, R, a, b), T), 1n+i), swj.conts(rest, 1n+i, a, b, hc))

def swj.copy(r: M.Rng, row: M.Row, +conts: List<&2, M.Row>, hc: {Selection.sl_all_cont(conts) == True{} : Bool}) -> {Selection.sl_nls(Selection.sl_copy(r, row <> conts)) == 0n : Nat}:
  match r:
    case M.Rng{+a, +b}:
      match row:
        case M.Row{w, +gs}:
          +R = Nat.add(0n, Selection.sl_row_of(a))
          +T = Bool.or(Nat.is_eq(R, Selection.sl_row_of(b)), Selection.sl_next_brk(conts))
          swj.k(Nat.is_le(R, Selection.sl_row_of(b)), Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, R, a, b), T), 0n), Selection.sl_rows(conts, 1n, a, b), swj.toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, R, a, b), T), 0n), swj.conts(conts, 0n, a, b, hc))

def swj.mode(m: M.Mode, +row: M.Row, +conts: List<&2, M.Row>, hc: {Selection.sl_all_cont(conts) == True{} : Bool}) -> {Selection.sl_copied_nls(Selection.sl_release_copy(m, row <> conts)) == 0n : Nat}:
  match m:
    case M.Idle{}:
      {==}
    case M.Pressed{a}:
      {==}
    case M.Selecting{a, h}:
      swj.copy(Selection.sl_order(a, h), row, conts, hc)
    case M.Picked{r}:
      swj.copy(r, row, conts, hc)
    case M.Shown{r}:
      {==}

def Selection.sel_wrap_joins(m, last, row, conts, wrapped):
  %Equal.sym(Maybe<&2, List<&2, Selection.SlTok>>, Selection.sl_copied(M.step(M.St{m, last}, M.EvRelease{row <> conts})), Selection.sl_release_copy(m, row <> conts), Pair.fst({Selection.sl_copied(M.step(M.St{m, last}, M.EvRelease{row <> conts})) == Selection.sl_release_copy(m, row <> conts) : Maybe<&2, List<&2, Selection.SlTok>>}, {Selection.sl_uncopied(M.step(M.St{m, last}, M.EvRelease{row <> conts})) == Selection.sl_release(m, last) : M.Res}, Selection.sel_release_copies(m, last, row <> conts))) : {Selection.sl_copied_nls(_) == 0n : Nat}
  swj.mode(m, row, conts, wrapped)
