# eukhe: the proof of LAW layout_column_reached
#
# PROOF: a width at i puts i below the count of columns (gw.wget_lt) and
# is the width of column i (gw.wget). By induction on the rows, a column
# below the count is as wide as a cell of it (lcr.reach): the first row's
# cell when it has one at least as wide as the rest's column (lcr.here);
# else the rest's column, which is below the rest's count (lcr.lt_max_r
# when the first row has no cell there; when it has one, a column past
# every row of the rest is 0 wide (lcr.colw_zero), narrower than no
# cell).

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

# Nat
# ---

def lcr.lt_zero(-G: Type, i: Nat, h: {Nat.is_lt(i, 0n) == True{} : Bool}) -> G:
  match i:
    case 0n:
      LLogicLogic.wn_absurd(G, h)
    case 1n+p:
      LLogicLogic.wn_absurd(G, h)

# not a < b: b <= a
def lcr.lt_flip(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.pf.absurd_tf({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lcr.lt_flip(p, q, h)

def lcr.max_l(a: Nat, b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.max(a, b) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.wn_absurd({Nat.max(0n, 1n+q) == 0n : Nat}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.max(p, q), p, lcr.max_l(p, q, h))

def lcr.max_r(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.max(a, b) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.wn_absurd({Nat.max(1n+p, 0n) == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.max(p, q), q, lcr.max_r(p, q, h))

# i < max(x, y) and x <= i: i < y
def lcr.lt_max_r(x: Nat, y: Nat, i: Nat, h: {Nat.is_lt(i, Nat.max(x, y)) == True{} : Bool}, hx: {Nat.is_le(x, i) == True{} : Bool}) -> {Nat.is_lt(i, y) == True{} : Bool}:
  match x y i:
    case 0n 0n 0n:
      LLogicLogic.wn_absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 0n 0n 1n+k:
      LLogicLogic.wn_absurd({Nat.is_lt(1n+k, 0n) == True{} : Bool}, h)
    case 0n 1n+q 0n:
      {==}
    case 0n 1n+q 1n+k:
      h
    case 1n+p 0n 0n:
      LLogicLogic.wn_absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, hx)
    case 1n+p 0n 1n+k:
      LLogicLogic.wn_absurd({Nat.is_lt(1n+k, 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_le(p, k), True{}, Equal.sym(Bool, Nat.is_le(p, k), False{}, LNat.pc.lt_not_le(k, p, h)), hx))
    case 1n+p 1n+q 0n:
      {==}
    case 1n+p 1n+q 1n+k:
      lcr.lt_max_r(p, q, k, h, hx)

# x is 0 and not x <= c: anything follows
def lcr.zero_absurd(-G: Type, -x: Nat, c: Nat, ez: {x == 0n : Nat}, eb: {Nat.is_le(x, c) == False{} : Bool}) -> G:
  LLogicLogic.wn_absurd(G, Equal.trans(Bool, False{}, Nat.is_le(0n, c), True{}, Equal.trans(Bool, False{}, Nat.is_le(x, c), Nat.is_le(0n, c), Equal.sym(Bool, Nat.is_le(x, c), False{}, eb), Equal.cong(Nat, Bool, y => Nat.is_le(y, c), x, 0n, ez)), LNat.compactor.pc.le_zero(c)))

# Cells past the end
# -----------------

# no cell at i: the measured row has at most i cells
def lcr.none_ge(r: List<&2, Nat>, i: Nat, e: {List.get(&2, Nat, r, i) == None{} : Maybe<&2, Nat>}) -> {Nat.is_le(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r)), i) == True{} : Bool}:
  match r:
    case Nil{}:
      LNat.compactor.pc.le_zero(i)
    case w <> rest:
      match i:
        case 0n:
          LA.gw.some_none(Nat, w, {Nat.is_le(1n, 0n) == True{} : Bool}, e)
        case 1n+p:
          lcr.none_ge(rest, p, e)

# a row of at most i cells: its cell i is 0 wide
def lcr.cells_past(r: List<&2, Nat>, i: Nat, h: {Nat.is_le(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r)), i) == True{} : Bool}) -> {Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i) == 0n : Nat}:
  match r:
    case Nil{}:
      {==}
    case w <> rest:
      match i:
        case 0n:
          LLogicLogic.wn_absurd({Nat.add(w, 0n) == 0n : Nat}, h)
        case 1n+p:
          lcr.cells_past(rest, p, h)

# a column past every row is 0 wide
def lcr.colw_zero(rows: List<&2, List<&2, Nat>>, +i: Nat, h: {Nat.is_le(Gw.cols(GatewayWidth.gw_table(rows)), i) == True{} : Bool}) -> {Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i) == 0n : Nat}:
  match rows:
    case Nil{}:
      {==}
    case +r0 <> +rest:
      +h2 = h
      +ea = lcr.cells_past(r0, i, LNat.wn_le_trans(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r0)), Nat.max(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r0)), Gw.cols(GatewayWidth.gw_table(rest))), i, LA.gw.le_max_l(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r0)), Gw.cols(GatewayWidth.gw_table(rest))), h2))
      %Equal.sym(Nat, Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i), 0n, ea) : {Nat.max(_, Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i)) == 0n : Nat}
      lcr.colw_zero(rest, i, LNat.wn_le_trans(Gw.cols(GatewayWidth.gw_table(rest)), Nat.max(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r0)), Gw.cols(GatewayWidth.gw_table(rest))), i, LA.gw.le_max_r(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r0)), Gw.cols(GatewayWidth.gw_table(rest))), h2))

# Reach
# -----

# some row j has a cell of column i's width
def lcr.Reach(+rows: List<&2, List<&2, Nat>>, +i: Nat) -> Type:
  &j: Nat -> &r: List<&2, Nat> -> {(List.get(&2, List<&2, Nat>, rows, j), List.get(&2, Nat, r, i)) == (Some{r}, Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}

# the first row's cell c, at least as wide as the rest's column
def lcr.here(-r0: List<&2, Nat>, -rest: List<&2, List<&2, Nat>>, -i: Nat, -c: Nat, em: {List.get(&2, Nat, r0, i) == Some{c} : Maybe<&2, Nat>}, ea: {Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i) == c : Nat}, emax: {Nat.max(c, Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i)) == c : Nat}) -> {(List.get(&2, List<&2, Nat>, r0 <> rest, 0n), List.get(&2, Nat, r0, i)) == (Some{r0}, Some{Nat.max(Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i))}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, r0, i), Some{c}, em) : {(List.get(&2, List<&2, Nat>, r0 <> rest, 0n), _) == (Some{r0}, Some{Nat.max(Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i))}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}
  %Equal.sym(Nat, Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i), c, ea) : {(List.get(&2, List<&2, Nat>, r0 <> rest, 0n), Some{c}) == (Some{r0}, Some{Nat.max(_, Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i))}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}
  %Equal.sym(Nat, Nat.max(c, Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i)), c, emax) : {(List.get(&2, List<&2, Nat>, r0 <> rest, 0n), Some{c}) == (Some{r0}, Some{_}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}
  {==}

# a cell of the rest's column of width w: the column of the table when
# the first row's cell (of width a) is narrower
def lcr.shift(-r0: List<&2, Nat>, -rest: List<&2, List<&2, Nat>>, -i: Nat, -a: Nat, -j: Nat, -r: List<&2, Nat>, ea: {Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i) == a : Nat}, emax: {Nat.max(a, Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i)) == Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i) : Nat}, pf: {(List.get(&2, List<&2, Nat>, rest, j), List.get(&2, Nat, r, i)) == (Some{r}, Some{Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i)}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}) -> {(List.get(&2, List<&2, Nat>, r0 <> rest, 1n+j), List.get(&2, Nat, r, i)) == (Some{r}, Some{Nat.max(Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i))}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}:
  %Equal.sym(Nat, Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i), a, ea) : {(List.get(&2, List<&2, Nat>, r0 <> rest, 1n+j), List.get(&2, Nat, r, i)) == (Some{r}, Some{Nat.max(_, Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i))}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}
  %Equal.sym(Nat, Nat.max(a, Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i)), Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i), emax) : {(List.get(&2, List<&2, Nat>, r0 <> rest, 1n+j), List.get(&2, Nat, r, i)) == (Some{r}, Some{_}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}
  pf

# a cell of the rest's column: one of the table's column, a row down
def lcr.lift(-r0: List<&2, Nat>, -rest: List<&2, List<&2, Nat>>, +i: Nat, -a: Nat, ea: {Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i) == a : Nat}, emax: {Nat.max(a, Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i)) == Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i) : Nat}, g: lcr.Reach(rest, i)) -> lcr.Reach(r0 <> rest, i):
  (j, more) = g
  (r, pf) = more
  (1n+j, (r, lcr.shift(r0, rest, i, a, j, r, ea, emax, pf)))

# the first row's cell c is narrower than the rest's column: the rest's
# column, reached when i is below the rest's count (b2), else 0 wide
def lcr.far(+r0: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, +i: Nat, +c: Nat, ih: {Nat.is_lt(i, Gw.cols(GatewayWidth.gw_table(rest))) == True{} : Bool} -> lcr.Reach(rest, i), ea: {Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i) == c : Nat}, eb: {Nat.is_le(Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i), c) == False{} : Bool}, b2: Bool, eb2: {Nat.is_lt(i, Gw.cols(GatewayWidth.gw_table(rest))) == b2 : Bool}) -> lcr.Reach(r0 <> rest, i):
  match b2:
    case True{}:
      lcr.lift(r0, rest, i, c, ea, lcr.max_r(c, Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i), LA.gw.le_flip(Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i), c, eb)), ih(eb2))
    case False{}:
      lcr.zero_absurd(lcr.Reach(r0 <> rest, i), Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i), c, lcr.colw_zero(rest, i, lcr.lt_flip(i, Gw.cols(GatewayWidth.gw_table(rest)), eb2)), eb)

# the first row has a cell c at i: it is the column's width when at least
# as wide as the rest's column (b), else lcr.far
def lcr.some(+r0: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, +i: Nat, +c: Nat, ih: {Nat.is_lt(i, Gw.cols(GatewayWidth.gw_table(rest))) == True{} : Bool} -> lcr.Reach(rest, i), em: {List.get(&2, Nat, r0, i) == Some{c} : Maybe<&2, Nat>}, ea: {Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i) == c : Nat}, b: Bool, eb: {Nat.is_le(Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i), c) == b : Bool}) -> lcr.Reach(r0 <> rest, i):
  match b:
    case True{}:
      (0n, (r0, lcr.here(r0, rest, i, c, em, ea, lcr.max_l(c, Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i), eb))))
    case False{}:
      lcr.far(r0, rest, i, c, ih, ea, eb, Nat.is_lt(i, Gw.cols(GatewayWidth.gw_table(rest))), {==})

# the first row of a table and the rest, with the first row's cell at i
# (m)
def lcr.cons(+r0: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, +i: Nat, h: {Nat.is_lt(i, Nat.max(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r0)), Gw.cols(GatewayWidth.gw_table(rest)))) == True{} : Bool}, ih: {Nat.is_lt(i, Gw.cols(GatewayWidth.gw_table(rest))) == True{} : Bool} -> lcr.Reach(rest, i), m: Maybe<&2, Nat>, em: {List.get(&2, Nat, r0, i) == m : Maybe<&2, Nat>}) -> lcr.Reach(r0 <> rest, i):
  match m:
    case None{}:
      +em2 = em
      lcr.lift(r0, rest, i, 0n, LA.gw.cell_none(r0, i, em2), {==}, ih(lcr.lt_max_r(List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r0)), Gw.cols(GatewayWidth.gw_table(rest)), i, h, lcr.none_ge(r0, i, em2))))
    case Some{+c}:
      +em2 = em
      lcr.some(r0, rest, i, c, ih, em2, LA.gw.cell_some(r0, i, c, em2), Nat.is_le(Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i), c), {==})

# below the count, a column is as wide as a cell of it
def lcr.reach(rows: List<&2, List<&2, Nat>>, +i: Nat, h: {Nat.is_lt(i, Gw.cols(GatewayWidth.gw_table(rows))) == True{} : Bool}) -> lcr.Reach(rows, i):
  match rows:
    case Nil{}:
      lcr.lt_zero(lcr.Reach(Nil{}, i), i, h)
    case +r0 <> +rest:
      lcr.cons(r0, rest, i, h, hh => lcr.reach(rest, i, hh), List.get(&2, Nat, r0, i), {==})

# the width w at i is the width of column i
def lcr.fin(+rows: List<&2, List<&2, Nat>>, +i: Nat, -w: Nat, -j: Nat, -r: List<&2, Nat>, col: {List.get(&2, Nat, Gw.widths(Gw.cols(GatewayWidth.gw_table(rows)), Gw.Display{}, GatewayWidth.gw_table(rows), 0n), i) == Some{w} : Maybe<&2, Nat>}, ew: {List.get(&2, Nat, Gw.widths(Gw.cols(GatewayWidth.gw_table(rows)), Gw.Display{}, GatewayWidth.gw_table(rows), 0n), i) == Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n))} : Maybe<&2, Nat>}, pf: {(List.get(&2, List<&2, Nat>, rows, j), List.get(&2, Nat, r, i)) == (Some{r}, Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}) -> {(List.get(&2, List<&2, Nat>, rows, j), List.get(&2, Nat, r, i)) == (Some{r}, Some{w}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}:
  +W = List.get(&2, Nat, Gw.widths(Gw.cols(GatewayWidth.gw_table(rows)), Gw.Display{}, GatewayWidth.gw_table(rows), 0n), i)
  %LA.gw.some_inj(Nat, Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n)), w, Equal.trans(Maybe<&2, Nat>, Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n))}, W, Some{w}, Equal.sym(Maybe<&2, Nat>, W, Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n))}, ew), col)) : {(List.get(&2, List<&2, Nat>, rows, j), List.get(&2, Nat, r, i)) == (Some{r}, Some{_}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}
  %Equal.sym(Nat, Nat.add(i, 0n), i, LNat.wn_add_zero_r(i)) : {(List.get(&2, List<&2, Nat>, rows, j), List.get(&2, Nat, r, i)) == (Some{r}, Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, _)}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}
  pf

# the law's claim, from a cell of column i's width
def lcr.end(+rows: List<&2, List<&2, Nat>>, +i: Nat, -w: Nat, col: {List.get(&2, Nat, Gw.widths(Gw.cols(GatewayWidth.gw_table(rows)), Gw.Display{}, GatewayWidth.gw_table(rows), 0n), i) == Some{w} : Maybe<&2, Nat>}, ew: {List.get(&2, Nat, Gw.widths(Gw.cols(GatewayWidth.gw_table(rows)), Gw.Display{}, GatewayWidth.gw_table(rows), 0n), i) == Some{Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, Nat.add(i, 0n))} : Maybe<&2, Nat>}, g: lcr.Reach(rows, i)) -> &j: Nat -> &r: List<&2, Nat> -> {(List.get(&2, List<&2, Nat>, rows, j), List.get(&2, Nat, r, i)) == (Some{r}, Some{w}) : Maybe<&2, List<&2, Nat>> & Maybe<&2, Nat>}:
  (j, more) = g
  (r, pf) = more
  (j, (r, lcr.fin(rows, i, w, j, r, col, ew, pf)))

def GatewayWidth.layout_column_reached(rows, i, w, col):
  +col2 = col
  +hlt = LA.gw.wget_lt(Gw.cols(GatewayWidth.gw_table(rows)), GatewayWidth.gw_table(rows), 0n, i, w, col2)
  lcr.end(rows, i, w, col2, LA.gw.wget(Gw.cols(GatewayWidth.gw_table(rows)), GatewayWidth.gw_table(rows), 0n, i, hlt), lcr.reach(rows, i, hlt))
