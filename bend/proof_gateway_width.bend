# The proofs of laws/gateway_width.bend (PROOF.bend delegates each law
# GatewayWidth.<law> to the def of the same name here): the model of
# bend/gateway_width.bend pads every cell to its column width, and an
# ASCII table measures the same by display width and by glyph count.

import Base
import ./gateway_width.bend as Gw

def gw.ND(n: Nat, A: Type) -> Type:
  match n:
    case 0n:
      A
    case 1n+p:
      Unit

# 1 + p is not 0
def gw.absurd(-A: Type, -p: Nat, e: {1n+p == 0n : Nat}) -> A:
  %e : gw.ND(_, A)
  Unit{}

# Arithmetic
# ----------
# `a <= b` is `Nat.sub(a, b) == 0n`, as the padding `w - c` reads it.

def gw.sub_self(a: Nat) -> {Nat.sub(a, a) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      gw.sub_self(p)

def gw.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def gw.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %gw.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def gw.add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %gw.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# a <= max(a, b)
def gw.le_max_l(+a: Nat, +b: Nat) -> {Nat.sub(a, Nat.max(a, b)) == 0n : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      gw.sub_self(ap)
    case 1n+ap 1n+bp:
      gw.le_max_l(ap, bp)

# b <= max(a, b)
def gw.le_max_r(+a: Nat, +b: Nat) -> {Nat.sub(b, Nat.max(a, b)) == 0n : Nat}:
  match a b:
    case 0n _:
      gw.sub_self(b)
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      gw.le_max_r(ap, bp)

def gw.le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.sub(a, b) == 0n : Nat}, h2: {Nat.sub(b, c) == 0n : Nat}) -> {Nat.sub(a, c) == 0n : Nat}:
  match a b c:
    case 0n _ _:
      {==}
    case 1n+ap 0n _:
      gw.absurd({Nat.sub(1n+ap, c) == 0n : Nat}, ap, h1)
    case 1n+ap 1n+bp 0n:
      gw.absurd({Nat.sub(1n+ap, 0n) == 0n : Nat}, bp, h2)
    case 1n+ap 1n+bp 1n+cp:
      gw.le_trans(ap, bp, cp, h1, h2)

# a cell no wider than its column pads to the column width
def gw.pad_fits(c: Nat, w: Nat, h: {Nat.sub(c, w) == 0n : Nat}) -> {Gw.pad(c, w) == w : Nat}:
  match c w:
    case 0n _:
      gw.sub_zero(w)
    case 1n+cp 0n:
      gw.absurd({Gw.pad(1n+cp, 0n) == 0n : Nat}, cp, h)
    case 1n+cp 1n+wp:
      %gw.pad_fits(cp, wp, h) : {1n+Nat.add(cp, Nat.sub(wp, cp)) == 1n+_ : Nat}
      {==}

# The table
# ---------

# a cell of a row is no wider than its column
def gw.cell_fits(pre: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +post: List<&2, List<&2, List<&2, Nat>>>, +m: Gw.Measure, +i: Nat) -> {Nat.sub(Gw.get.w(row, m, i), Gw.col.w(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), m, i)) == 0n : Nat}:
  match pre:
    case Nil{}:
      gw.le_max_l(Gw.get.w(row, m, i), Gw.col.w(post, m, i))
    case +r <> +rest:
      +tail = Gw.col.w(List.append(&2, List<&2, List<&2, Nat>>, rest, row <> post), m, i)
      gw.le_trans(Gw.get.w(row, m, i), tail, Nat.max(Gw.get.w(r, m, i), tail), gw.cell_fits(rest, row, post, m, i), gw.le_max_r(Gw.get.w(r, m, i), tail))

# a row from column i: the widths of k columns, then its own cell k + i
def gw.line_aligned(+k: Nat, +m: Gw.Measure, +pre: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +post: List<&2, List<&2, List<&2, Nat>>>, +i: Nat) -> {Gw.line(k, m, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), row, i) == List.append(&2, Nat, Gw.widths(k, m, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), i), [Gw.get.w(row, m, Nat.add(k, i))]) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      +rows = List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)
      +g = Gw.get.w(row, m, i)
      +c = Gw.col.w(rows, m, i)
      %Equal.sym(Nat, Gw.pad(g, c), c, gw.pad_fits(g, c, gw.cell_fits(pre, row, post, m, i))) : {_ <> Gw.line(p, m, rows, row, 1n+i) == c <> List.append(&2, Nat, Gw.widths(p, m, rows, 1n+i), [Gw.get.w(row, m, 1n+Nat.add(p, i))]) : List<&2, Nat>}
      %gw.add_succ(p, i) : {c <> Gw.line(p, m, rows, row, 1n+i) == c <> List.append(&2, Nat, Gw.widths(p, m, rows, 1n+i), [Gw.get.w(row, m, _)]) : List<&2, Nat>}
      %gw.line_aligned(p, m, pre, row, post, 1n+i) : {c <> Gw.line(p, m, rows, row, 1n+i) == c <> _ : List<&2, Nat>}
      {==}

def table_aligned(+pre: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +post: List<&2, List<&2, List<&2, Nat>>>) -> {Gw.line(Nat.sub(Gw.cols(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), 1n), Gw.Display{}, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), row, 0n) == List.append(&2, Nat, Gw.widths(Nat.sub(Gw.cols(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), 1n), Gw.Display{}, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), 0n), [Gw.get.w(row, Gw.Display{}, Nat.sub(Gw.cols(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), 1n))]) : List<&2, Nat>}:
  +k = Nat.sub(Gw.cols(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), 1n)
  %gw.add_zero(k) : {Gw.line(k, Gw.Display{}, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), row, 0n) == List.append(&2, Nat, Gw.widths(k, Gw.Display{}, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), 0n), [Gw.get.w(row, Gw.Display{}, _)]) : List<&2, Nat>}
  gw.line_aligned(k, Gw.Display{}, pre, row, post, 0n)

# ASCII
# -----

def gw.cell_ascii(c: List<&2, Nat>, ones: Gw.Ones.cell(c)) -> {Gw.cell.sum(c) == List.length(&2, Nat, c) : Nat}:
  match c:
    case Nil{}:
      {==}
    case w <> rest:
      (one, more) = ones
      %Equal.sym(Nat, w, 1n, one) : {Nat.add(_, Gw.cell.sum(rest)) == 1n+List.length(&2, Nat, rest) : Nat}
      %gw.cell_ascii(rest, more) : {1n+Gw.cell.sum(rest) == 1n+_ : Nat}
      {==}

def gw.get_ascii(row: List<&2, List<&2, Nat>>, i: Nat, ones: Gw.Ones.row(row)) -> {Gw.get.w(row, Gw.Display{}, i) == Gw.get.w(row, Gw.Chars{}, i) : Nat}:
  match row:
    case Nil{}:
      {==}
    case c <> rest:
      match i:
        case 0n:
          (oc, orest) = ones
          gw.cell_ascii(c, oc)
        case 1n+p:
          (oc, orest) = ones
          gw.get_ascii(rest, p, orest)
def gw.col_ascii(rows: List<&2, List<&2, List<&2, Nat>>>, +i: Nat, ones: Gw.Ones.rows(rows)) -> {Gw.col.w(rows, Gw.Display{}, i) == Gw.col.w(rows, Gw.Chars{}, i) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case r <> rest:
      (or, orest) = ones
      %gw.get_ascii(r, i, or) : {Nat.max(Gw.get.w(r, Gw.Display{}, i), Gw.col.w(rest, Gw.Display{}, i)) == Nat.max(_, Gw.col.w(rest, Gw.Chars{}, i)) : Nat}
      %gw.col_ascii(rest, i, orest) : {Nat.max(Gw.get.w(r, Gw.Display{}, i), Gw.col.w(rest, Gw.Display{}, i)) == Nat.max(Gw.get.w(r, Gw.Display{}, i), _) : Nat}
      {==}

def gw.line_ascii(+k: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>, +row: List<&2, List<&2, Nat>>, +i: Nat, +orows: Gw.Ones.rows(rows), +orow: Gw.Ones.row(row)) -> {Gw.line(k, Gw.Display{}, rows, row, i) == Gw.line(k, Gw.Chars{}, rows, row, i) : List<&2, Nat>}:
  match k:
    case 0n:
      %gw.get_ascii(row, i, orow) : {[Gw.get.w(row, Gw.Display{}, i)] == [_] : List<&2, Nat>}
      {==}
    case 1n+p:
      %gw.get_ascii(row, i, orow) : {Gw.line(1n+p, Gw.Display{}, rows, row, i) == Gw.pad(_, Gw.col.w(rows, Gw.Chars{}, i)) <> Gw.line(p, Gw.Chars{}, rows, row, 1n+i) : List<&2, Nat>}
      %gw.col_ascii(rows, i, orows) : {Gw.line(1n+p, Gw.Display{}, rows, row, i) == Gw.pad(Gw.get.w(row, Gw.Display{}, i), _) <> Gw.line(p, Gw.Chars{}, rows, row, 1n+i) : List<&2, Nat>}
      %gw.line_ascii(p, rows, row, 1n+i, orows, orow) : {Gw.line(1n+p, Gw.Display{}, rows, row, i) == Gw.pad(Gw.get.w(row, Gw.Display{}, i), Gw.col.w(rows, Gw.Display{}, i)) <> _ : List<&2, Nat>}
      {==}

def gw.table_ascii(rs: List<&2, List<&2, List<&2, Nat>>>, +k: Nat, +rows: List<&2, List<&2, List<&2, Nat>>>, ors: Gw.Ones.rows(rs), +orows: Gw.Ones.rows(rows)) -> {Gw.table.go(rs, k, Gw.Display{}, rows) == Gw.table.go(rs, k, Gw.Chars{}, rows) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> rest:
      (or, orest) = ors
      %gw.line_ascii(k, rows, r, 0n, orows, or) : {Gw.line(k, Gw.Display{}, rows, r, 0n) <> Gw.table.go(rest, k, Gw.Display{}, rows) == _ <> Gw.table.go(rest, k, Gw.Chars{}, rows) : List<&2, List<&2, Nat>>}
      %gw.table_ascii(rest, k, rows, orest, orows) : {Gw.line(k, Gw.Display{}, rows, r, 0n) <> Gw.table.go(rest, k, Gw.Display{}, rows) == Gw.line(k, Gw.Display{}, rows, r, 0n) <> _ : List<&2, List<&2, Nat>>}
      {==}

def ascii_unchanged(+rows: List<&2, List<&2, List<&2, Nat>>>, +ones: Gw.Ones.rows(rows)) -> {Gw.table(Gw.Display{}, rows) == Gw.table(Gw.Chars{}, rows) : List<&2, List<&2, Nat>>}:
  gw.table_ascii(rows, Nat.sub(Gw.cols(rows), 1n), rows, ones, ones)
