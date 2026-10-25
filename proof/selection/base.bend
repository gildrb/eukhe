# eukhe: lemmas shared by the proofs of laws/selection.bend
#
# The model's helpers and the spec's agree on every cell: once a cell is
# a constructor both compute the same comparison (sl_le, sl_same), so the
# order of two cells, a mode's selection and the answers built from them
# agree for every argument. Below them: the Nat order facts the proofs
# use, and the count of a press that counts on.

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection

# Logic
# -----

def ls.clash(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      G

# False is not True: anything follows
def ls.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : ls.clash(_, G)
  Unit{}

def ls.absurd_t(-G: Type, e: {True{} == False{} : Bool}) -> G:
  ls.absurd(G, Equal.sym(Bool, True{}, False{}, e))

# Nat order
# ---------

def ls.and_tt(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      ls.absurd({Bool.and(False{}, b) == True{} : Bool}, ea)

def ls.zcl(n: Nat, G: Type) -> Type:
  match n:
    case 0n:
      G
    case 1n+p:
      Unit

# 1 + n is not 0: anything follows
def ls.succ_zero(-G: Type, -n: Nat, e: {1n+n == 0n : Nat}) -> G:
  %e : ls.zcl(_, G)
  Unit{}

def ls.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ls.absurd({False{} == True{} : Bool}, e)

def ls.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      ls.absurd({b == True{} : Bool}, e)

# a at most b: b is not below a
def ls.le_nlt(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      ls.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      ls.le_nlt(p, q, h)

def ls.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ls.eq_refl(p)

def ls.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def ls.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ls.le_refl(p)

def ls.le_succ(n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ls.le_succ(p)

def ls.le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ q:
      ls.le_zero(q)
    case 1n+p 0n _:
      ls.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      ls.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      ls.le_trans(p, q, r, h1, h2)

# x is at most p + x
def ls.le_add(p: Nat, +x: Nat) -> {Nat.is_le(x, Nat.add(p, x)) == True{} : Bool}:
  match p:
    case 0n:
      ls.le_refl(x)
    case 1n++q:
      ls.le_trans(x, Nat.add(q, x), 1n+Nat.add(q, x), ls.le_add(q, x), ls.le_succ(Nat.add(q, x)))

def ls.lt_not_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      ls.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      ls.absurd({Nat.is_le(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      ls.lt_not_le(p, q, h)

# x not at most c: c + 1 is at most x
def ls.nle_lt(x: Nat, c: Nat, h: {Nat.is_le(x, c) == False{} : Bool}) -> {Nat.is_le(1n+c, x) == True{} : Bool}:
  match x c:
    case 0n q:
      ls.absurd_t({Nat.is_le(1n+q, 0n) == True{} : Bool}, Equal.trans(Bool, True{}, Nat.is_le(0n, q), False{}, Equal.sym(Bool, Nat.is_le(0n, q), True{}, ls.le_zero(q)), h))
    case 1n+p 0n:
      ls.le_zero(p)
    case 1n+p 1n+q:
      ls.nle_lt(p, q, h)

def ls.le_lt_succ(x: Nat, c: Nat, h: {Nat.is_le(x, c) == True{} : Bool}) -> {Nat.is_lt(x, 1n+c) == True{} : Bool}:
  match x c:
    case 0n q:
      {==}
    case 1n+p 0n:
      ls.absurd({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      ls.le_lt_succ(p, q, h)

def ls.lt_le(a: Nat, b: Nat, c: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      ls.absurd({Nat.is_lt(0n, c) == True{} : Bool}, h1)
    case 0n 1n+q 0n:
      ls.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      ls.absurd({Nat.is_lt(1n+p, c) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      ls.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      ls.lt_le(p, q, r, h1, h2)

def ls.lt_succ(+x: Nat, +c: Nat, h: {Nat.is_lt(x, c) == True{} : Bool}) -> {Nat.is_lt(x, 1n+c) == True{} : Bool}:
  ls.lt_le(x, c, 1n+c, h, ls.le_succ(c))

# e + 1 at most x: x is not at most e
def ls.succ_le_nle(e: Nat, x: Nat, h: {Nat.is_le(1n+e, x) == True{} : Bool}) -> {Nat.is_le(x, e) == False{} : Bool}:
  match e x:
    case 0n 0n:
      ls.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      ls.absurd({Nat.is_le(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      ls.succ_le_nle(p, q, h)

# Nat sums
# --------

def ls.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %ls.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def ls.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ls.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def ls.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ls.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def ls.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, ls.add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, b), Nat.add(b, p), ls.add_comm(p, b)) : {1n+_ == Nat.add(b, 1n+p) : Nat}
      Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), ls.add_succ(b, p))

def ls.lt_irrefl(n: Nat) -> {Nat.is_lt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ls.lt_irrefl(p)

def ls.lt_ne(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      ls.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ls.lt_ne(p, q, h)

def ls.sub_zero(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def ls.sub_self(n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ls.sub_self(p)

def ls.sub_le_zero(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n q:
      {==}
    case 1n+p 0n:
      ls.absurd({Nat.sub(1n+p, 0n) == 0n : Nat}, h)
    case 1n+p 1n+q:
      ls.sub_le_zero(p, q, h)

# p - j is one more than p - (j + 1) when j < p
def ls.sub_pos(p: Nat, j: Nat, h: {Nat.is_le(1n+j, p) == True{} : Bool}) -> {Nat.sub(p, j) == 1n+Nat.sub(p, 1n+j) : Nat}:
  match p j:
    case 0n q:
      ls.absurd({Nat.sub(0n, q) == 1n+Nat.sub(0n, 1n+q) : Nat}, h)
    case 1n+q 0n:
      %Equal.sym(Nat, Nat.sub(q, 0n), q, ls.sub_zero(q)) : {1n+q == 1n+_ : Nat}
      {==}
    case 1n+q 1n+r:
      ls.sub_pos(q, r, h)

# what M.row_nb answers from index j: 0, or past j
def ls.nbok(n: Nat, +j: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Nat.is_le(j, p)

# the larger of L and N, less L, is 0 when N is at most L
def ls.hz.k(b: Bool, +L: Nat, +N: Nat, eb: {Nat.is_le(L, N) == b : Bool}, h: {Nat.is_le(N, L) == True{} : Bool}) -> {Nat.sub(M.max.pick(b, L, N), L) == 0n : Nat}:
  match b:
    case True{}:
      ls.sub_le_zero(N, L, h)
    case False{}:
      ls.sub_self(L)

def ls.hz(+L: Nat, +N: Nat, h: {Nat.is_le(N, L) == True{} : Bool}) -> {Nat.sub(M.max.pick(Nat.is_le(L, N), L, N), L) == 0n : Nat}:
  ls.hz.k(Nat.is_le(L, N), L, N, {==}, h)

# Token lists
# -----------

def ls.isnil(l: List<&2, Selection.SlTok>, G: Type) -> Type:
  match l:
    case Nil{}:
      G
    case Con{x, xs}:
      Unit

def ls.cons_nil(-G: Type, -x: Selection.SlTok, -xs: List<&2, Selection.SlTok>, e: {x <> xs == Nil{} : List<&2, Selection.SlTok>}) -> G:
  %e : ls.isnil(_, G)
  Unit{}

def ls.app_nil(xs: List<&2, Selection.SlTok>) -> {List.append(&2, Selection.SlTok, xs, Nil{}) == xs : List<&2, Selection.SlTok>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      %ls.app_nil(rest) : {x <> List.append(&2, Selection.SlTok, rest, Nil{}) == x <> _ : List<&2, Selection.SlTok>}
      {==}

def ls.app_assoc(xs: List<&2, Selection.SlTok>, -ys: List<&2, Selection.SlTok>, -zs: List<&2, Selection.SlTok>) -> {List.append(&2, Selection.SlTok, List.append(&2, Selection.SlTok, xs, ys), zs) == List.append(&2, Selection.SlTok, xs, List.append(&2, Selection.SlTok, ys, zs)) : List<&2, Selection.SlTok>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      %ls.app_assoc(rest, ys, zs) : {x <> List.append(&2, Selection.SlTok, List.append(&2, Selection.SlTok, rest, ys), zs) == x <> _ : List<&2, Selection.SlTok>}
      {==}

# Cells and answers
# -----------------

def ls.le(a: M.Cell, b: M.Cell) -> {M.cell_le(a, b) == Selection.sl_le(a, b) : Bool}:
  match a:
    case M.Cell{ar, ac}:
      match b:
        case M.Cell{br, bc}:
          {==}

def ls.same(a: M.Cell, b: M.Cell) -> {M.cell_eq(a, b) == Selection.sl_same(a, b) : Bool}:
  match a:
    case M.Cell{ar, ac}:
      match b:
        case M.Cell{br, bc}:
          {==}

def ls.order(a: M.Cell, b: M.Cell) -> {M.order(a, b) == Selection.sl_order(a, b) : M.Rng}:
  match a:
    case M.Cell{ar, ac}:
      match b:
        case M.Cell{br, bc}:
          {==}

def ls.sel(m: M.Mode) -> {M.sel(m) == Selection.sl_sel(m) : Maybe<&2, M.Rng>}:
  match m:
    case M.Idle{}:
      {==}
    case M.Pressed{a}:
      {==}
    case M.Selecting{+a, +h}:
      %Equal.sym(M.Rng, M.order(a, h), Selection.sl_order(a, h), ls.order(a, h)) : {Some{_} == Some{Selection.sl_order(a, h)} : Maybe<&2, M.Rng>}
      {==}
    case M.Picked{r}:
      {==}
    case M.Shown{r}:
      {==}

def ls.moved(+m: M.Mode, +p: M.Pan) -> {M.moved(m, p) == Selection.sl_moved(m, p) : M.Res}:
  %Equal.sym(Maybe<&2, M.Rng>, M.sel(m), Selection.sl_sel(m), ls.sel(m)) : {M.Res{M.St{m, None{}}, M.Out{_, None{}, p, False{}}} == Selection.sl_moved(m, p) : M.Res}
  {==}

def ls.quiet(+m: M.Mode, +last: Maybe<&2, M.Click>) -> {M.quiet(m, last) == Selection.sl_quiet(m, last) : M.Res}:
  %Equal.sym(Maybe<&2, M.Rng>, M.sel(m), Selection.sl_sel(m), ls.sel(m)) : {M.Res{M.St{m, last}, M.Out{_, None{}, M.PanNone{}, False{}}} == Selection.sl_quiet(m, last) : M.Res}
  {==}

# Presses
# -------

# a press on the cell of the last press, at most 400 ms later, counts on
def ls.clicks(+r: Nat, +x: Nat, +t1: Nat, +t2: Nat, n: Nat, near: {Bool.and(Nat.is_le(t1, t2), Nat.is_le(Nat.sub(t2, t1), 400n)) == True{} : Bool}) -> {M.clicks(Some{M.Click{M.Cell{r, x}, t1, n}}, M.Cell{r, x}, t2) == M.next(n) : Nat}:
  %Equal.sym(Bool, Nat.is_eq(r, r), True{}, ls.eq_refl(r)) : {M.near(Bool.and(Bool.and(_, Nat.is_eq(x, x)), Bool.and(Nat.is_le(t1, t2), Nat.is_le(Nat.sub(t2, t1), 400n))), n) == M.next(n) : Nat}
  %Equal.sym(Bool, Nat.is_eq(x, x), True{}, ls.eq_refl(x)) : {M.near(Bool.and(_, Bool.and(Nat.is_le(t1, t2), Nat.is_le(Nat.sub(t2, t1), 400n))), n) == M.next(n) : Nat}
  %Equal.sym(Bool, Bool.and(Nat.is_le(t1, t2), Nat.is_le(Nat.sub(t2, t1), 400n)), True{}, near) : {M.near(_, n) == M.next(n) : Nat}
  {==}
