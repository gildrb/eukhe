# eukhe: lemmas the proofs of area gateway_width share

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat

def gw.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Maybe
# -----

# G at Some, Unit at None
def gw.MIf(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some: anything follows
def gw.none_some(-A: Data, -x: A, -G: Type, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %e : gw.MIf(A, _, G)
  Unit{}

def gw.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  gw.none_some(A, x, G, Equal.sym(Maybe<&2, A>, Some{x}, None{}, e))

def gw.some_inj(-A: Data, -a: A, -b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => Maybe.default(&2, A, m, a), Some{a}, Some{b}, e)

# Nat
# ---

def gw.le_max_l(a: Nat, b: Nat) -> {Nat.is_le(a, Nat.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LNat.compactor.pc.le_refl(p)
    case 1n+p 1n+q:
      gw.le_max_l(p, q)

def gw.le_max_r(a: Nat, b: Nat) -> {Nat.is_le(b, Nat.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LNat.compactor.pc.le_refl(q)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      gw.le_max_r(p, q)

# not a <= b: b <= a
def gw.le_flip(a: Nat, b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.pf.absurd_tf({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      gw.le_flip(p, q, h)

# a < b <= c: a < c
def gw.lt_le(a: Nat, b: Nat, c: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      LLogicLogic.wn_absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, h1)
    case 0n 0n 1n+z:
      {==}
    case 0n 1n+y 0n:
      LLogicLogic.wn_absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
    case 0n 1n+y 1n+z:
      {==}
    case 1n+x 0n 0n:
      LLogicLogic.wn_absurd({Nat.is_lt(1n+x, 0n) == True{} : Bool}, h1)
    case 1n+x 0n 1n+z:
      LLogicLogic.wn_absurd({Nat.is_lt(1n+x, 1n+z) == True{} : Bool}, h1)
    case 1n+x 1n+y 0n:
      LLogicLogic.wn_absurd({Nat.is_lt(1n+x, 0n) == True{} : Bool}, h2)
    case 1n+x 1n+y 1n+z:
      gw.lt_le(x, y, z, h1, h2)

# a <= b: a + (b - a) is b
def gw.add_sub(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.wn_absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, Nat.sub(q, p)), q, gw.add_sub(p, q, h))

# A measured table
# ----------------
# gw_table(rows) has a one-glyph cell per measured width: its display
# width is that width (0 past the end of the row).

# a measured cell's display width is its width
def gw.cell_some(r: List<&2, Nat>, i: Nat, -c: Nat, e: {List.get(&2, Nat, r, i) == Some{c} : Maybe<&2, Nat>}) -> {Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i) == c : Nat}:
  match r:
    case Nil{}:
      gw.none_some(Nat, c, {0n == c : Nat}, e)
    case w <> rest:
      match i:
        case 0n:
          Equal.trans(Nat, Nat.add(w, 0n), w, c, LNat.wn_add_zero_r(w), gw.some_inj(Nat, w, c, e))
        case 1n+p:
          gw.cell_some(rest, p, c, e)

# a missing cell is 0 wide
def gw.cell_none(r: List<&2, Nat>, i: Nat, e: {List.get(&2, Nat, r, i) == None{} : Maybe<&2, Nat>}) -> {Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i) == 0n : Nat}:
  match r:
    case Nil{}:
      {==}
    case w <> rest:
      match i:
        case 0n:
          gw.some_none(Nat, w, {Nat.add(w, 0n) == 0n : Nat}, e)
        case 1n+p:
          gw.cell_none(rest, p, e)

# row j of a measured table: as many cells as widths
def gw.len_cells(r: List<&2, Nat>) -> {List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(r)) == List.length(&2, Nat, r) : Nat}:
  match r:
    case Nil{}:
      {==}
    case w <> rest:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, List<&2, Nat>, GatewayWidth.gw_cells(rest)), List.length(&2, Nat, rest), gw.len_cells(rest))

# the cell of row j in column i is at most the column's width
def gw.colw_ge(rows: List<&2, List<&2, Nat>>, j: Nat, +r: List<&2, Nat>, +i: Nat, e: {List.get(&2, List<&2, Nat>, rows, j) == Some{r} : Maybe<&2, List<&2, Nat>>}) -> {Nat.is_le(Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rows), Gw.Display{}, i)) == True{} : Bool}:
  match rows:
    case Nil{}:
      gw.none_some(List<&2, Nat>, r, {Nat.is_le(Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i), 0n) == True{} : Bool}, e)
    case +r0 <> +rest:
      match j:
        case 0n:
          %gw.some_inj(List<&2, Nat>, r0, r, e) : {Nat.is_le(Gw.get.w(GatewayWidth.gw_cells(_), Gw.Display{}, i), Nat.max(Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i))) == True{} : Bool}
          gw.le_max_l(Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i))
        case 1n+p:
          LNat.wn_le_trans(Gw.get.w(GatewayWidth.gw_cells(r), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i), Nat.max(Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i)), gw.colw_ge(rest, p, r, i, e), gw.le_max_r(Gw.get.w(GatewayWidth.gw_cells(r0), Gw.Display{}, i), Gw.col.w(GatewayWidth.gw_table(rest), Gw.Display{}, i)))

# The layout's widths
# -------------------

# below k, item i of the widths from column i0 is the width of column i0 + i
def gw.wget(k: Nat, +t: List<&2, List<&2, List<&2, Nat>>>, +i0: Nat, i: Nat, h: {Nat.is_lt(i, k) == True{} : Bool}) -> {List.get(&2, Nat, Gw.widths(k, Gw.Display{}, t, i0), i) == Some{Gw.col.w(t, Gw.Display{}, Nat.add(i, i0))} : Maybe<&2, Nat>}:
  match k i:
    case 0n 0n:
      LLogicLogic.wn_absurd({None{} == Some{Gw.col.w(t, Gw.Display{}, i0)} : Maybe<&2, Nat>}, h)
    case 0n 1n+q:
      LLogicLogic.wn_absurd({None{} == Some{Gw.col.w(t, Gw.Display{}, Nat.add(1n+q, i0))} : Maybe<&2, Nat>}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n++q:
      %LNat.wn_add_succ_r(q, i0) : {List.get(&2, Nat, Gw.widths(p, Gw.Display{}, t, 1n+i0), q) == Some{Gw.col.w(t, Gw.Display{}, _)} : Maybe<&2, Nat>}
      gw.wget(p, t, 1n+i0, q, h)

# a width at i: i is below k
def gw.wget_lt(k: Nat, +t: List<&2, List<&2, List<&2, Nat>>>, +i0: Nat, i: Nat, -w: Nat, e: {List.get(&2, Nat, Gw.widths(k, Gw.Display{}, t, i0), i) == Some{w} : Maybe<&2, Nat>}) -> {Nat.is_lt(i, k) == True{} : Bool}:
  match k i:
    case 0n 0n:
      gw.none_some(Nat, w, {Nat.is_lt(0n, 0n) == True{} : Bool}, e)
    case 0n 1n+q:
      gw.none_some(Nat, w, {Nat.is_lt(1n+q, 0n) == True{} : Bool}, e)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      gw.wget_lt(p, t, 1n+i0, q, w, e)

# The layout's pads
# -----------------

# row j's pads in the layout of a measured table: the pads of its cells
def gw.pall_row(rows: List<&2, List<&2, Nat>>, +ws: List<&2, Nat>, j: Nat, +r: List<&2, Nat>, e: {List.get(&2, List<&2, Nat>, rows, j) == Some{r} : Maybe<&2, List<&2, Nat>>}) -> {List.get(&2, List<&2, Nat>, Gw.pads.all(GatewayWidth.gw_table(rows), ws), j) == Some{Gw.pads.row(ws, GatewayWidth.gw_cells(r))} : Maybe<&2, List<&2, Nat>>}:
  match rows:
    case Nil{}:
      gw.none_some(List<&2, Nat>, r, {None{} == Some{Gw.pads.row(ws, GatewayWidth.gw_cells(r))} : Maybe<&2, List<&2, Nat>>}, e)
    case r0 <> rest:
      match j:
        case 0n:
          %gw.some_inj(List<&2, Nat>, r0, r, e) : {Some{Gw.pads.row(ws, GatewayWidth.gw_cells(r0))} == Some{Gw.pads.row(ws, GatewayWidth.gw_cells(_))} : Maybe<&2, List<&2, Nat>>}
          {==}
        case 1n+p:
          gw.pall_row(rest, ws, p, r, e)
