# eukhe.com's Neovim: the proof of LAW sel_cells
# ==============================================
#
# The frame's selection is Vis.go over the text rows: row d of it is the
# run of line top + d (Go.cov), which covers column x exactly when Vis.cols
# puts x between its ends (Run.cov), which is when x lies between the
# selection's ends as the spec reads them (Cols.in, line by line through
# Tri).

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/view.bend as V
import ../../../vim/visual.bend as Vi
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/visual.bend as VisualLaws
import ../../base.bend as L
import ../../base/final.bend as Fi
import ../../base/reach.bend as Re
import ../../base/text.bend as Tx
import ../motion/base.bend as Mo
import ./yank_line.bend as Yl
import ../mouse/click.bend as Cl
import ../screen/base.bend as Sc

# Booleans
# --------

def Iff.refl(b: Bool) -> {Laws.Spec.iff(b, b) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Or.false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def And.true(b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def And.false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def And.comm(a: Bool, b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def And.left(a: Bool, b: Bool, c: Bool) -> {Bool.and(b, Bool.and(c, a)) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# Numbers
# -------

def Le.zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Lt.zero(x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def And.zero(x: Nat) -> {Bool.and(Nat.is_le(0n, x), Nat.is_lt(x, 0n)) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Lt.succ(x: Nat, c: Nat) -> {Nat.is_lt(x, 1n+c) == Nat.is_le(x, c) : Bool}:
  match x c:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Lt.zero(p)
    case 1n+p 1n+q:
      Lt.succ(p, q)

def Lt.min(x: Nat, a: Nat, b: Nat) -> {Nat.is_lt(x, Nat.min(a, b)) == Bool.and(Nat.is_lt(x, a), Nat.is_lt(x, b)) : Bool}:
  match x a b:
    case 0n 0n _:
      {==}
    case 0n 1n+p 0n:
      {==}
    case 0n 1n+p 1n+q:
      {==}
    case 1n+y 0n _:
      {==}
    case 1n+y 1n+p 0n:
      Equal.sym(Bool, Bool.and(Nat.is_lt(y, p), False{}), False{}, And.false(Nat.is_lt(y, p)))
    case 1n+y 1n+p 1n+q:
      Lt.min(y, p, q)

def Max.one(n: Nat) -> {Nat.max(n, 1n) == Laws.Spec.max(n, 1n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      match m:
        case 0n:
          {==}
        case 1n+k:
          {==}

def Size.chars(s: String) -> {Vi.Vis.size(s) == Laws.Spec.chars(s) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(Nat, Nat, n => 1n+n, Vi.Vis.size(t), Laws.Spec.chars(t), Size.chars(t))

def Ne.succ(r: Nat, +e: Nat) -> {Nat.is_eq(r, 1n+Nat.add(e, r)) == False{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      %L.Nat.add_succ(e, p) : {Nat.is_eq(p, _) == False{} : Bool}
      Ne.succ(p, e)

def Ne.of_lt(a: Nat, b: Nat, h: L.LT(a, b)) -> {Nat.is_eq(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      L.Bool.false_true({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      L.Bool.false_true({Nat.is_eq(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      Ne.of_lt(p, q, h)

# a then b compared, in one of three ways: the claim for each
def Tri(a: Nat, b: Nat, -G: Bool -> Bool -> Bool -> Bool -> Type, glt: G(True{}, False{}, False{}, True{}), geq: G(False{}, True{}, True{}, True{}), ggt: G(False{}, False{}, False{}, False{}))
  -> G(Nat.is_lt(a, b), Nat.is_eq(a, b), Nat.is_eq(b, a), Nat.is_le(a, b)):
  match a b:
    case 0n 0n:
      geq
    case 0n 1n+q:
      glt
    case 1n+p 0n:
      ggt
    case 1n+p 1n+q:
      Tri(p, q, G, glt, geq, ggt)

# Runs
# ----

# the columns between a pair's ends
def Pair.in(ft: (Nat & Nat), +x: Nat) -> Bool:
  match ft:
    case (from, to):
      Bool.and(Nat.is_le(from, x), Nat.is_lt(x, to))

def One(m: Maybe<&2, T.Span>, +r: Nat, +x: Nat) -> Bool:
  Laws.Spec.in_runs(V.View.span.put(m, Nil{}), r, x)

def Put.cov(m: Maybe<&2, T.Span>, +rest: List<&2, T.Span>, +r: Nat, +x: Nat) -> {Laws.Spec.in_runs(V.View.span.put(m, rest), r, x) == Bool.or(One(m, r, x), Laws.Spec.in_runs(rest, r, x)) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{T.Span{+row, +col, +len}}:
      +head = Bool.and(Nat.is_eq(row, r), Bool.and(Nat.is_le(col, x), Nat.is_lt(x, Nat.add(col, len))))
      %Equal.sym(Bool, Bool.or(head, False{}), head, Or.false(head)) : {Bool.or(head, Laws.Spec.in_runs(rest, r, x)) == Bool.or(_, Laws.Spec.in_runs(rest, r, x)) : Bool}
      {==}

# a run with no column, or past it, holds no cell
def Run.none.go(a: Bool, b: Bool, +from: Nat, +to: Nat, +x: Nat, ea: {Nat.is_le(from, x) == a : Bool}, eb: {Nat.is_lt(x, to) == b : Bool}, e: {Nat.is_lt(from, to) == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a b:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      +lt = L.Nat.le_lt_trans(from, x, to, ea, eb)
      L.Bool.false_true({True{} == False{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(from, to), True{}, Equal.sym(Bool, Nat.is_lt(from, to), False{}, e), lt))


def Run.none(+from: Nat, +to: Nat, +x: Nat, e: {Nat.is_lt(from, to) == False{} : Bool}) -> {Bool.and(Nat.is_le(from, x), Nat.is_lt(x, to)) == False{} : Bool}:
  Run.none.go(Nat.is_le(from, x), Nat.is_lt(x, to), from, to, x, {==}, {==}, e)

def Run.cov.at(b: Bool, +from: Nat, +to: Nat, +r: Nat, +x: Nat, e: {Nat.is_lt(from, to) == b : Bool})
  -> {Laws.Spec.in_runs(V.View.span.put(Bool.pick(Maybe<&2, T.Span>, b, Some{T.Span{r, from, Nat.sub(to, from)}}, None{}), Nil{}), r, x) == Bool.and(Nat.is_le(from, x), Nat.is_lt(x, to)) : Bool}:
  match b:
    case False{}:
      Equal.sym(Bool, Bool.and(Nat.is_le(from, x), Nat.is_lt(x, to)), False{}, Run.none(from, to, x, e))
    case True{}:
      +inside = Bool.and(Nat.is_le(from, x), Nat.is_lt(x, to))
      %Equal.sym(Bool, Nat.is_eq(r, r), True{}, L.Nat.eq_refl(r)) : {Bool.or(Bool.and(_, Bool.and(Nat.is_le(from, x), Nat.is_lt(x, Nat.add(from, Nat.sub(to, from))))), False{}) == inside : Bool}
      %Equal.sym(Nat, Nat.add(from, Nat.sub(to, from)), to, L.Nat.add_sub(to, from, L.Nat.lt_to_le(from, to, e))) : {Bool.or(Bool.and(Nat.is_le(from, x), Nat.is_lt(x, _)), False{}) == inside : Bool}
      Or.false(inside)

# a run of another row holds no cell of row r

def Run.cov(ft: (Nat & Nat), +r: Nat, +x: Nat) -> {One(Vi.Vis.run(ft, r), r, x) == Pair.in(ft, x) : Bool}:
  match ft:
    case (+from, +to):
      Run.cov.at(Nat.is_lt(from, to), from, to, r, x, {==})

def Run.row.at(b: Bool, +from: Nat, +to: Nat, +r0: Nat, +r: Nat, +x: Nat, hne: {Nat.is_eq(r0, r) == False{} : Bool})
  -> {Laws.Spec.in_runs(V.View.span.put(Bool.pick(Maybe<&2, T.Span>, b, Some{T.Span{r0, from, Nat.sub(to, from)}}, None{}), Nil{}), r, x) == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(r0, r), False{}, hne) : {Bool.or(Bool.and(_, Bool.and(Nat.is_le(from, x), Nat.is_lt(x, Nat.add(from, Nat.sub(to, from))))), False{}) == False{} : Bool}
      {==}

# Rows
# ----

# the rows from r1 on hold no cell of an earlier row

def Run.row(ft: (Nat & Nat), +r0: Nat, +r: Nat, +x: Nat, hne: {Nat.is_eq(r0, r) == False{} : Bool}) -> {One(Vi.Vis.run(ft, r0), r, x) == False{} : Bool}:
  match ft:
    case (+from, +to):
      Run.row.at(Nat.is_lt(from, to), from, to, r0, r, x, hne)

def Above(hh: Nat, ls: List<&2, String>, +k: T.Vis, +l: Nat, +r1: Nat, +p: T.Pos, +q: T.Pos, +r: Nat, +x: Nat, +h: L.LT(r, r1)) -> {Laws.Spec.in_runs(Vi.Vis.go(hh, ls, k, l, r1, p, q), r, x) == False{} : Bool}:
  match hh ls:
    case 0n _:
      {==}
    case 1n+n Nil{}:
      {==}
    case 1n++n Con{+line, +t}:
      +m = Vi.Vis.run(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), r1)
      +rest = Vi.Vis.go(n, t, k, 1n+l, 1n+r1, p, q)
      +h2 = L.Nat.le_lt(r, 1n+r1, L.Nat.le_succ(1n+r, r1, L.Nat.lt_le(r, r1, h)))
      %Equal.sym(Bool, Laws.Spec.in_runs(V.View.span.put(m, rest), r, x), Bool.or(One(m, r, x), Laws.Spec.in_runs(rest, r, x)), Put.cov(m, rest, r, x)) : {_ == False{} : Bool}
      %Equal.sym(Bool, One(m, r, x), False{}, Run.row(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), r1, r, x, Ne.of_lt(r, r1, h))) : {Bool.or(_, Laws.Spec.in_runs(rest, r, x)) == False{} : Bool}
      Above(n, t, k, 1n+l, 1n+r1, p, q, r, x, h2)

def Go.G(+ls: List<&2, String>, +k: T.Vis, +l: Nat, +p: T.Pos, +q: T.Pos, +d: Nat, +x: Nat) -> Bool:
  Bool.and(Nat.is_lt(d, Laws.Spec.count(ls)), Pair.in(Vi.Vis.cols(k, Nat.add(d, l), Vi.Vis.size(B.Lines.at(ls, d)), p, q), x))

# row d of the rows from r0: the run of line l + d
def Go.cov(hh: Nat, ls: List<&2, String>, d: Nat, +k: T.Vis, +l: Nat, +r0: Nat, +p: T.Pos, +q: T.Pos, +x: Nat, hd: L.LT(d, hh))
  -> {Laws.Spec.in_runs(Vi.Vis.go(hh, ls, k, l, r0, p, q), Nat.add(d, r0), x) == Go.G(ls, k, l, p, q, d, x) : Bool}:
  match hh ls d:
    case 0n _ 0n:
      L.Bool.false_true({Laws.Spec.in_runs(Vi.Vis.go(0n, ls, k, l, r0, p, q), Nat.add(0n, r0), x) == Go.G(ls, k, l, p, q, 0n, x) : Bool}, hd)
    case 0n _ 1n+e:
      L.Bool.false_true({Laws.Spec.in_runs(Vi.Vis.go(0n, ls, k, l, r0, p, q), Nat.add(1n+e, r0), x) == Go.G(ls, k, l, p, q, 1n+e, x) : Bool}, hd)
    case 1n+n Nil{} 0n:
      {==}
    case 1n+n Nil{} 1n+e:
      {==}
    case 1n+n Con{+line, +t} 0n:
      +rest = Vi.Vis.go(n, t, k, 1n+l, 1n+r0, p, q)
      %Equal.sym(Bool, Laws.Spec.in_runs(V.View.span.put(Vi.Vis.run(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), r0), rest), r0, x), Bool.or(One(Vi.Vis.run(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), r0), r0, x), Laws.Spec.in_runs(rest, r0, x)), Put.cov(Vi.Vis.run(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), r0), rest, r0, x)) : {_ == Pair.in(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), x) : Bool}
      %Equal.sym(Bool, One(Vi.Vis.run(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), r0), r0, x), Pair.in(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), x), Run.cov(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), r0, x)) : {Bool.or(_, Laws.Spec.in_runs(rest, r0, x)) == Pair.in(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), x) : Bool}
      %Equal.sym(Bool, Laws.Spec.in_runs(rest, r0, x), False{}, Above(n, t, k, 1n+l, 1n+r0, p, q, r0, x, L.Nat.lt_succ(r0))) : {Bool.or(Pair.in(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), x), _) == Pair.in(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), x) : Bool}
      Or.false(Pair.in(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), x))
    case 1n++n Con{+line, +t} 1n++e:
      +rest = Vi.Vis.go(n, t, k, 1n+l, 1n+r0, p, q)
      +r = {1n+Nat.add(e, r0) : Nat}
      %Equal.sym(Nat, 1n+Nat.add(e, l), Nat.add(e, 1n+l), L.Nat.add_succ(e, l)) : {Laws.Spec.in_runs(Vi.Vis.go(1n+n, Con{line, t}, k, l, r0, p, q), r, x) == Bool.and(Nat.is_lt(e, Laws.Spec.count(t)), Pair.in(Vi.Vis.cols(k, _, Vi.Vis.size(B.Lines.at(t, e)), p, q), x)) : Bool}
      %Equal.sym(Bool, Laws.Spec.in_runs(V.View.span.put(Vi.Vis.run(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), r0), rest), r, x), Bool.or(One(Vi.Vis.run(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), r0), r, x), Laws.Spec.in_runs(rest, r, x)), Put.cov(Vi.Vis.run(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), r0), rest, r, x)) : {_ == Go.G(t, k, 1n+l, p, q, e, x) : Bool}
      %Equal.sym(Bool, One(Vi.Vis.run(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), r0), r, x), False{}, Run.row(Vi.Vis.cols(k, l, Vi.Vis.size(line), p, q), r0, r, x, Ne.succ(r0, e))) : {Bool.or(_, Laws.Spec.in_runs(rest, r, x)) == Go.G(t, k, 1n+l, p, q, e, x) : Bool}
      %Equal.sym(Nat, 1n+Nat.add(e, r0), Nat.add(e, 1n+r0), L.Nat.add_succ(e, r0)) : {Laws.Spec.in_runs(rest, _, x) == Go.G(t, k, 1n+l, p, q, e, x) : Bool}
      Go.cov(n, t, e, k, 1n+l, 1n+r0, p, q, x, hd)

# Columns
# -------

def Bef0(a: Nat, b: Nat) -> {Laws.Spec.before(T.Pos{a, 0n}, T.Pos{b, 0n}) == Nat.is_le(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Bef0(p, q)

# V: the line's columns while it lies between the ends' lines
def Lines.at(bb: Bool, +n: Nat, +x: Nat) -> {Pair.in(Bool.pick((Nat & Nat), bb, (0n, Nat.max(n, 1n)), (0n, 0n)), x) == Bool.and(Nat.is_lt(x, Laws.Spec.max(n, 1n)), bb) : Bool}:
  match bb:
    case True{}:
      %Equal.sym(Bool, Nat.is_le(0n, x), True{}, Le.zero(x)) : {Bool.and(_, Nat.is_lt(x, Nat.max(n, 1n))) == Bool.and(Nat.is_lt(x, Laws.Spec.max(n, 1n)), True{}) : Bool}
      %Equal.sym(Nat, Nat.max(n, 1n), Laws.Spec.max(n, 1n), Max.one(n)) : {Nat.is_lt(x, _) == Bool.and(Nat.is_lt(x, Laws.Spec.max(n, 1n)), True{}) : Bool}
      Equal.sym(Bool, Bool.and(Nat.is_lt(x, Laws.Spec.max(n, 1n)), True{}), Nat.is_lt(x, Laws.Spec.max(n, 1n)), And.true(Nat.is_lt(x, Laws.Spec.max(n, 1n))))
    case False{}:
      Equal.trans(Bool, Bool.and(Nat.is_le(0n, x), Nat.is_lt(x, 0n)), False{}, Bool.and(Nat.is_lt(x, Laws.Spec.max(n, 1n)), False{}), And.zero(x), Equal.sym(Bool, Bool.and(Nat.is_lt(x, Laws.Spec.max(n, 1n)), False{}), False{}, And.false(Nat.is_lt(x, Laws.Spec.max(n, 1n)))))

# v: the claim for line l against the ends' lines, compared
def VC.T(lt1: Bool, eq1: Bool, eq1r: Bool, le1: Bool, lt2: Bool, eq2: Bool, le2: Bool, +c1: Nat, +c2: Nat, +x: Nat, +n: Nat) -> Type:
  +m = Nat.max(n, 1n)
  {Pair.in(Bool.pick((Nat & Nat), Bool.and(le1, le2), (Bool.pick(Nat, eq1r, c1, 0n), Bool.pick(Nat, eq2, Nat.min(1n+c2, m), m)), (0n, 0n)), x)
    == Bool.and(Nat.is_lt(x, Laws.Spec.max(n, 1n)), Bool.and(Bool.or(lt1, Bool.and(eq1, Nat.is_le(c1, x))), Bool.or(lt2, Bool.and(eq2, Nat.is_le(x, c2))))) : Bool}

def Leaf.zero(+x: Nat, +a: Bool) -> {Bool.and(Nat.is_le(0n, x), Nat.is_lt(x, 0n)) == Bool.and(a, False{}) : Bool}:
  Equal.trans(Bool, Bool.and(Nat.is_le(0n, x), Nat.is_lt(x, 0n)), False{}, Bool.and(a, False{}), And.zero(x), Equal.sym(Bool, Bool.and(a, False{}), False{}, And.false(a)))

def Leaf.lt_lt(+c1: Nat, +c2: Nat, +x: Nat, +n: Nat) -> VC.T(True{}, False{}, False{}, True{}, True{}, False{}, True{}, c1, c2, x, n):
  +a = Nat.is_lt(x, Laws.Spec.max(n, 1n))
  %Equal.sym(Bool, Nat.is_le(0n, x), True{}, Le.zero(x)) : {Bool.and(_, Nat.is_lt(x, Nat.max(n, 1n))) == Bool.and(a, True{}) : Bool}
  %Equal.sym(Nat, Nat.max(n, 1n), Laws.Spec.max(n, 1n), Max.one(n)) : {Nat.is_lt(x, _) == Bool.and(a, True{}) : Bool}
  Equal.sym(Bool, Bool.and(a, True{}), a, And.true(a))

def Leaf.lt_eq(+c1: Nat, +c2: Nat, +x: Nat, +n: Nat) -> VC.T(True{}, False{}, False{}, True{}, False{}, True{}, True{}, c1, c2, x, n):
  +a = Nat.is_lt(x, Laws.Spec.max(n, 1n))
  +c = Nat.is_le(x, c2)
  %Equal.sym(Bool, Nat.is_le(0n, x), True{}, Le.zero(x)) : {Bool.and(_, Nat.is_lt(x, Nat.min(1n+c2, Nat.max(n, 1n)))) == Bool.and(a, c) : Bool}
  %Equal.sym(Bool, Nat.is_lt(x, Nat.min(1n+c2, Nat.max(n, 1n))), Bool.and(Nat.is_lt(x, 1n+c2), Nat.is_lt(x, Nat.max(n, 1n))), Lt.min(x, 1n+c2, Nat.max(n, 1n))) : {_ == Bool.and(a, c) : Bool}
  %Equal.sym(Bool, Nat.is_lt(x, 1n+c2), c, Lt.succ(x, c2)) : {Bool.and(_, Nat.is_lt(x, Nat.max(n, 1n))) == Bool.and(a, c) : Bool}
  %Equal.sym(Nat, Nat.max(n, 1n), Laws.Spec.max(n, 1n), Max.one(n)) : {Bool.and(c, Nat.is_lt(x, _)) == Bool.and(a, c) : Bool}
  And.comm(c, a)

def Leaf.eq_lt(+c1: Nat, +c2: Nat, +x: Nat, +n: Nat) -> VC.T(False{}, True{}, True{}, True{}, True{}, False{}, True{}, c1, c2, x, n):
  +a = Nat.is_lt(x, Laws.Spec.max(n, 1n))
  +b = Nat.is_le(c1, x)
  %Equal.sym(Nat, Nat.max(n, 1n), Laws.Spec.max(n, 1n), Max.one(n)) : {Bool.and(b, Nat.is_lt(x, _)) == Bool.and(a, Bool.and(b, True{})) : Bool}
  %Equal.sym(Bool, Bool.and(b, True{}), b, And.true(b)) : {Bool.and(b, a) == Bool.and(a, _) : Bool}
  And.comm(b, a)

def Leaf.eq_eq(+c1: Nat, +c2: Nat, +x: Nat, +n: Nat) -> VC.T(False{}, True{}, True{}, True{}, False{}, True{}, True{}, c1, c2, x, n):
  +a = Nat.is_lt(x, Laws.Spec.max(n, 1n))
  +b = Nat.is_le(c1, x)
  +c = Nat.is_le(x, c2)
  %Equal.sym(Bool, Nat.is_lt(x, Nat.min(1n+c2, Nat.max(n, 1n))), Bool.and(Nat.is_lt(x, 1n+c2), Nat.is_lt(x, Nat.max(n, 1n))), Lt.min(x, 1n+c2, Nat.max(n, 1n))) : {Bool.and(b, _) == Bool.and(a, Bool.and(b, c)) : Bool}
  %Equal.sym(Bool, Nat.is_lt(x, 1n+c2), c, Lt.succ(x, c2)) : {Bool.and(b, Bool.and(_, Nat.is_lt(x, Nat.max(n, 1n)))) == Bool.and(a, Bool.and(b, c)) : Bool}
  %Equal.sym(Nat, Nat.max(n, 1n), Laws.Spec.max(n, 1n), Max.one(n)) : {Bool.and(b, Bool.and(c, Nat.is_lt(x, _))) == Bool.and(a, Bool.and(b, c)) : Bool}
  And.left(a, b, c)

def Leaf.eq_gt(+c1: Nat, +c2: Nat, +x: Nat, +n: Nat) -> VC.T(False{}, True{}, True{}, True{}, False{}, False{}, False{}, c1, c2, x, n):
  +a = Nat.is_lt(x, Laws.Spec.max(n, 1n))
  +b = Nat.is_le(c1, x)
  %Equal.sym(Bool, Bool.and(b, False{}), False{}, And.false(b)) : {Bool.and(Nat.is_le(0n, x), Nat.is_lt(x, 0n)) == Bool.and(a, _) : Bool}
  Leaf.zero(x, a)

def Cols.chars(+l1: Nat, +l: Nat, +l2: Nat, +c1: Nat, +c2: Nat, +x: Nat, +n: Nat)
  -> VC.T(Nat.is_lt(l1, l), Nat.is_eq(l1, l), Nat.is_eq(l, l1), Nat.is_le(l1, l), Nat.is_lt(l, l2), Nat.is_eq(l, l2), Nat.is_le(l, l2), c1, c2, x, n):
  +a = Nat.is_lt(x, Laws.Spec.max(n, 1n))
  Tri(l1, l, p1 => p2 => p3 => p4 => VC.T(p1, p2, p3, p4, Nat.is_lt(l, l2), Nat.is_eq(l, l2), Nat.is_le(l, l2), c1, c2, x, n),
    Tri(l, l2, q1 => q2 => q3 => q4 => VC.T(True{}, False{}, False{}, True{}, q1, q2, q4, c1, c2, x, n), Leaf.lt_lt(c1, c2, x, n), Leaf.lt_eq(c1, c2, x, n), Leaf.zero(x, a)),
    Tri(l, l2, q1 => q2 => q3 => q4 => VC.T(False{}, True{}, True{}, True{}, q1, q2, q4, c1, c2, x, n), Leaf.eq_lt(c1, c2, x, n), Leaf.eq_eq(c1, c2, x, n), Leaf.eq_gt(c1, c2, x, n)),
    Tri(l, l2, q1 => q2 => q3 => q4 => VC.T(False{}, False{}, False{}, False{}, q1, q2, q4, c1, c2, x, n), Leaf.zero(x, a), Leaf.zero(x, a), Leaf.zero(x, a)))


# Data
# ----

def Le.spec(+a: T.Pos, +b: T.Pos) -> {Vi.Vis.le(a, b) == Laws.Spec.before(a, b) : Bool}:
  match a b:
    case T.Pos{+l1, +c1} T.Pos{+l2, +c2}:
      {==}

def Line.spec(ls: List<&2, String>, i: Nat) -> {Laws.Spec.line(ls, i) == B.Lines.at(ls, i) : String}:
  match ls i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      Line.spec(t, p)

def Drop.at(ls: List<&2, String>, top: Nat, +r: Nat) -> {B.Lines.at(B.Lines.drop(ls, top), r) == B.Lines.at(ls, Nat.add(r, top)) : String}:
  match ls top:
    case Nil{} _:
      {==}
    case Con{+h, +t} 0n:
      %L.Nat.add_zero(r) : {B.Lines.at(Con{h, t}, r) == B.Lines.at(Con{h, t}, _) : String}
      {==}
    case Con{+h, +t} 1n+p:
      %L.Nat.add_succ(r, p) : {B.Lines.at(B.Lines.drop(t, p), r) == B.Lines.at(Con{h, t}, _) : String}
      Drop.at(t, p, r)

def Drop.count(ls: List<&2, String>, top: Nat, +r: Nat) -> {Nat.is_lt(r, Laws.Spec.count(B.Lines.drop(ls, top))) == Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)) : Bool}:
  match ls top:
    case Nil{} +top:
      Equal.trans(Bool, Nat.is_lt(r, 0n), False{}, Nat.is_lt(Nat.add(r, top), 0n), Lt.zero(r), Equal.sym(Bool, Nat.is_lt(Nat.add(r, top), 0n), False{}, Lt.zero(Nat.add(r, top))))
    case Con{+h, +t} 0n:
      %L.Nat.add_zero(r) : {Nat.is_lt(r, Laws.Spec.count(Con{h, t})) == Nat.is_lt(_, Laws.Spec.count(Con{h, t})) : Bool}
      {==}
    case Con{+h, +t} 1n+p:
      %L.Nat.add_succ(r, p) : {Nat.is_lt(r, Laws.Spec.count(B.Lines.drop(t, p))) == Nat.is_lt(_, Laws.Spec.count(Con{h, t})) : Bool}
      Drop.count(t, p, r)

def Pos.eta(p: T.Pos) -> {T.Pos{S.Pos.line(p), S.Pos.col(p)} == p : T.Pos}:
  match p:
    case T.Pos{l, c}:
      {==}

# a pair's columns are the spec's
def Cols.in(k: T.Vis, +l: Nat, +n: Nat, +p: T.Pos, +q: T.Pos, +x: Nat) -> {Pair.in(Vi.Vis.cols(k, l, n, p, q), x) == Bool.and(Nat.is_lt(x, Laws.Spec.max(n, 1n)), Laws.Spec.between(k, p, q, l, x)) : Bool}:
  match k p q:
    case T.VChars{} T.Pos{+l1, +c1} T.Pos{+l2, +c2}:
      Cols.chars(l1, l, l2, c1, c2, x, n)
    case T.VLines{} T.Pos{+l1, +c1} T.Pos{+l2, +c2}:
      %Equal.sym(Bool, Laws.Spec.before(T.Pos{l1, 0n}, T.Pos{l, 0n}), Nat.is_le(l1, l), Bef0(l1, l)) : {Pair.in(Vi.Vis.cols(T.VLines{}, l, n, T.Pos{l1, c1}, T.Pos{l2, c2}), x) == Bool.and(Nat.is_lt(x, Laws.Spec.max(n, 1n)), Bool.and(_, Laws.Spec.before(T.Pos{l, 0n}, T.Pos{l2, 0n}))) : Bool}
      %Equal.sym(Bool, Laws.Spec.before(T.Pos{l, 0n}, T.Pos{l2, 0n}), Nat.is_le(l, l2), Bef0(l, l2)) : {Pair.in(Vi.Vis.cols(T.VLines{}, l, n, T.Pos{l1, c1}, T.Pos{l2, c2}), x) == Bool.and(Nat.is_lt(x, Laws.Spec.max(n, 1n)), Bool.and(Nat.is_le(l1, l), _)) : Bool}
      Lines.at(Bool.and(Nat.is_le(l1, l), Nat.is_le(l, l2)), n, x)

# p implies q, from q given p
def Imp(b: Bool, -X: Bool, f: {b == True{} : Bool} -> {X == True{} : Bool}) -> {Laws.Spec.implies(b, X) == True{} : Bool}:
  match b:
    case True{}:
      f({==})
    case False{}:
      {==}

# The selection
# -------------

# on any lines, rows and ends: row r of the runs covers column x exactly
# when it is picked
def Sel.in(+ls: List<&2, String>, +k: T.Vis, +a: T.Pos, +c: T.Pos, +top: Nat, +h: Nat, +r: Nat, +x: Nat, hd: L.LT(r, h)) -> {Laws.Spec.iff(Laws.Spec.in_runs(Vi.Vis.spans(k, ls, a, c, top, h), r, x), Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Laws.Spec.picked(k, a, c, Nat.add(r, top), x, Laws.Spec.chars(Laws.Spec.line(ls, Nat.add(r, top)))))) == True{} : Bool}:
  %Equal.sym(Nat, r, Nat.add(r, 0n), L.Nat.add_zero(r)) : {Laws.Spec.iff(Laws.Spec.in_runs(Vi.Vis.go(h, B.Lines.drop(ls, top), k, top, 0n, Vi.Vis.lo(a, c), Vi.Vis.hi(a, c)), _, x), Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Laws.Spec.picked(k, a, c, Nat.add(r, top), x, Laws.Spec.chars(Laws.Spec.line(ls, Nat.add(r, top)))))) == True{} : Bool}
  %Equal.sym(Bool, Laws.Spec.in_runs(Vi.Vis.go(h, B.Lines.drop(ls, top), k, top, 0n, Vi.Vis.lo(a, c), Vi.Vis.hi(a, c)), Nat.add(r, 0n), x), Go.G(B.Lines.drop(ls, top), k, top, Vi.Vis.lo(a, c), Vi.Vis.hi(a, c), r, x), Go.cov(h, B.Lines.drop(ls, top), r, k, top, 0n, Vi.Vis.lo(a, c), Vi.Vis.hi(a, c), x, hd)) : {Laws.Spec.iff(_, Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Laws.Spec.picked(k, a, c, Nat.add(r, top), x, Laws.Spec.chars(Laws.Spec.line(ls, Nat.add(r, top)))))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(r, Laws.Spec.count(B.Lines.drop(ls, top))), Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Drop.count(ls, top, r)) : {Laws.Spec.iff(Bool.and(_, Pair.in(Vi.Vis.cols(k, Nat.add(r, top), Vi.Vis.size(B.Lines.at(B.Lines.drop(ls, top), r)), Vi.Vis.lo(a, c), Vi.Vis.hi(a, c)), x)), Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Laws.Spec.picked(k, a, c, Nat.add(r, top), x, Laws.Spec.chars(Laws.Spec.line(ls, Nat.add(r, top)))))) == True{} : Bool}
  %Equal.sym(String, B.Lines.at(B.Lines.drop(ls, top), r), B.Lines.at(ls, Nat.add(r, top)), Drop.at(ls, top, r)) : {Laws.Spec.iff(Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Pair.in(Vi.Vis.cols(k, Nat.add(r, top), Vi.Vis.size(_), Vi.Vis.lo(a, c), Vi.Vis.hi(a, c)), x)), Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Laws.Spec.picked(k, a, c, Nat.add(r, top), x, Laws.Spec.chars(Laws.Spec.line(ls, Nat.add(r, top)))))) == True{} : Bool}
  %Line.spec(ls, Nat.add(r, top)) : {Laws.Spec.iff(Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Pair.in(Vi.Vis.cols(k, Nat.add(r, top), Vi.Vis.size(_), Vi.Vis.lo(a, c), Vi.Vis.hi(a, c)), x)), Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Laws.Spec.picked(k, a, c, Nat.add(r, top), x, Laws.Spec.chars(Laws.Spec.line(ls, Nat.add(r, top)))))) == True{} : Bool}
  %Equal.sym(Nat, Vi.Vis.size(Laws.Spec.line(ls, Nat.add(r, top))), Laws.Spec.chars(Laws.Spec.line(ls, Nat.add(r, top))), Size.chars(Laws.Spec.line(ls, Nat.add(r, top)))) : {Laws.Spec.iff(Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Pair.in(Vi.Vis.cols(k, Nat.add(r, top), _, Vi.Vis.lo(a, c), Vi.Vis.hi(a, c)), x)), Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Laws.Spec.picked(k, a, c, Nat.add(r, top), x, Laws.Spec.chars(Laws.Spec.line(ls, Nat.add(r, top)))))) == True{} : Bool}
  +n = Laws.Spec.chars(Laws.Spec.line(ls, Nat.add(r, top)))
  %Equal.sym(Bool, Pair.in(Vi.Vis.cols(k, Nat.add(r, top), n, Vi.Vis.lo(a, c), Vi.Vis.hi(a, c)), x), Bool.and(Nat.is_lt(x, Laws.Spec.max(n, 1n)), Laws.Spec.between(k, Vi.Vis.lo(a, c), Vi.Vis.hi(a, c), Nat.add(r, top), x)), Cols.in(k, Nat.add(r, top), n, Vi.Vis.lo(a, c), Vi.Vis.hi(a, c), x)) : {Laws.Spec.iff(Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), _), Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Laws.Spec.picked(k, a, c, Nat.add(r, top), x, Laws.Spec.chars(Laws.Spec.line(ls, Nat.add(r, top)))))) == True{} : Bool}
  %Equal.sym(Bool, Vi.Vis.le(a, c), Laws.Spec.before(a, c), Le.spec(a, c)) : {Laws.Spec.iff(Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Bool.and(Nat.is_lt(x, Laws.Spec.max(n, 1n)), Laws.Spec.between(k, Bool.pick(T.Pos, _, a, c), Vi.Vis.hi(a, c), Nat.add(r, top), x))), Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Laws.Spec.picked(k, a, c, Nat.add(r, top), x, Laws.Spec.chars(Laws.Spec.line(ls, Nat.add(r, top)))))) == True{} : Bool}
  %Equal.sym(Bool, Vi.Vis.le(a, c), Laws.Spec.before(a, c), Le.spec(a, c)) : {Laws.Spec.iff(Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Bool.and(Nat.is_lt(x, Laws.Spec.max(n, 1n)), Laws.Spec.between(k, Bool.pick(T.Pos, Laws.Spec.before(a, c), a, c), Bool.pick(T.Pos, _, c, a), Nat.add(r, top), x))), Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Laws.Spec.picked(k, a, c, Nat.add(r, top), x, Laws.Spec.chars(Laws.Spec.line(ls, Nat.add(r, top)))))) == True{} : Bool}
  Iff.refl(Bool.and(Nat.is_lt(Nat.add(r, top), Laws.Spec.count(ls)), Laws.Spec.picked(k, a, c, Nat.add(r, top), x, Laws.Spec.chars(Laws.Spec.line(ls, Nat.add(r, top))))))


# The frame
# ---------

# a settled editor in visual mode: the frame reads back the cursor's line
def Vf.line(+y: T.St, fin: Fi.Final(y), -k: T.Vis, -a: T.Pos) -> {Laws.Spec.at_line(Cl.Ck.frame(y, T.Visual{k, a})) == C.St.line(y) : Nat}:
  (f3, r1) = fin
  (f12, r2) = r1
  (fl, r3) = r2
  (fc, r4) = r3
  (bt, bl) = r4
  (bth, btl) = bt
  +h = V.View.text_rows(S.St.rows(y))
  L.Nat.add_sub(C.St.line(y), S.Win.top(S.St.win(y)), Sc.Win.top_le(C.St.line(y), V.View.so_in(h), S.Win.top(S.St.win(y)), btl))

# and its column
def Vf.col(+y: T.St, fin: Fi.Final(y), -k: T.Vis, -a: T.Pos) -> {Laws.Spec.at_col(Cl.Ck.frame(y, T.Visual{k, a})) == C.St.col(y) : Nat}:
  (f3, r1) = fin
  (f12, r2) = r1
  (fl, r3) = r2
  (fc, r4) = r3
  (bt, bl) = r4
  (blh, bll) = bl
  +g = C.St.g(y)
  +w = V.View.text_cols(S.St.cols(y), V.View.gutter(S.St.opts(y), B.Lines.len(C.St.lines(y)), C.St.on_file(y), S.St.cols(y)))
  +left = S.Win.left(S.St.win(y))
  +col = C.St.col(y)
  +d = Nat.sub(col, left)
  Equal.trans(Nat, Nat.add(left, Nat.sub(Nat.add(g, d), g)), Nat.add(left, d), col, Equal.cong(Nat, Nat, z => Nat.add(left, z), Nat.sub(Nat.add(g, d), g), d, L.Nat.add_sub_l(g, d)), L.Nat.add_sub(col, left, Sc.Win.top_le(col, V.View.so_in(w), left, bll)))

# The law
# -------

def SelCells.visual(+y: T.St, +fin: Fi.Final(y), +k: T.Vis, +a: T.Pos, hm: {S.St.mode(y) == T.Visual{k, a} : T.Mode}, +r: Nat, +x: Nat) -> {Laws.Claim.sel_cells.at(T.Visual{k, a}, y, r, x) == True{} : Bool}:
  %Equal.sym(T.Mode, S.St.mode(y), T.Visual{k, a}, hm) : {Laws.Spec.implies(Nat.is_lt(r, Nat.sub(S.St.rows(y), 2n)), Laws.Spec.iff(Laws.Spec.in_runs(Laws.F.sel(Cl.Ck.frame(y, _)), r, x), Bool.and(Nat.is_lt(Nat.add(r, Laws.F.top(Cl.Ck.frame(y, _))), Laws.Spec.count(Vim.Vim.lines(y))), Laws.Spec.picked(k, a, T.Pos{Laws.Spec.at_line(Cl.Ck.frame(y, _)), Laws.Spec.at_col(Cl.Ck.frame(y, _))}, Nat.add(r, Laws.F.top(Cl.Ck.frame(y, _))), x, Laws.Spec.chars(Laws.Spec.line(Vim.Vim.lines(y), Nat.add(r, Laws.F.top(Cl.Ck.frame(y, _))))))))) == True{} : Bool}
  %Equal.sym(Nat, Laws.Spec.at_line(Cl.Ck.frame(y, T.Visual{k, a})), C.St.line(y), Vf.line(y, fin, k, a)) : {Laws.Spec.implies(Nat.is_lt(r, Nat.sub(S.St.rows(y), 2n)), Laws.Spec.iff(Laws.Spec.in_runs(Laws.F.sel(Cl.Ck.frame(y, T.Visual{k, a})), r, x), Bool.and(Nat.is_lt(Nat.add(r, Laws.F.top(Cl.Ck.frame(y, T.Visual{k, a}))), Laws.Spec.count(Vim.Vim.lines(y))), Laws.Spec.picked(k, a, T.Pos{_, Laws.Spec.at_col(Cl.Ck.frame(y, T.Visual{k, a}))}, Nat.add(r, Laws.F.top(Cl.Ck.frame(y, T.Visual{k, a}))), x, Laws.Spec.chars(Laws.Spec.line(Vim.Vim.lines(y), Nat.add(r, Laws.F.top(Cl.Ck.frame(y, T.Visual{k, a}))))))))) == True{} : Bool}
  %Equal.sym(Nat, Laws.Spec.at_col(Cl.Ck.frame(y, T.Visual{k, a})), C.St.col(y), Vf.col(y, fin, k, a)) : {Laws.Spec.implies(Nat.is_lt(r, Nat.sub(S.St.rows(y), 2n)), Laws.Spec.iff(Laws.Spec.in_runs(Laws.F.sel(Cl.Ck.frame(y, T.Visual{k, a})), r, x), Bool.and(Nat.is_lt(Nat.add(r, Laws.F.top(Cl.Ck.frame(y, T.Visual{k, a}))), Laws.Spec.count(Vim.Vim.lines(y))), Laws.Spec.picked(k, a, T.Pos{C.St.line(y), _}, Nat.add(r, Laws.F.top(Cl.Ck.frame(y, T.Visual{k, a}))), x, Laws.Spec.chars(Laws.Spec.line(Vim.Vim.lines(y), Nat.add(r, Laws.F.top(Cl.Ck.frame(y, T.Visual{k, a}))))))))) == True{} : Bool}
  %Equal.sym(T.Pos, T.Pos{C.St.line(y), C.St.col(y)}, S.Win.cur(S.St.win(y)), Pos.eta(S.Win.cur(S.St.win(y)))) : {Laws.Spec.implies(Nat.is_lt(r, Nat.sub(S.St.rows(y), 2n)), Laws.Spec.iff(Laws.Spec.in_runs(Laws.F.sel(Cl.Ck.frame(y, T.Visual{k, a})), r, x), Bool.and(Nat.is_lt(Nat.add(r, Laws.F.top(Cl.Ck.frame(y, T.Visual{k, a}))), Laws.Spec.count(Vim.Vim.lines(y))), Laws.Spec.picked(k, a, _, Nat.add(r, Laws.F.top(Cl.Ck.frame(y, T.Visual{k, a}))), x, Laws.Spec.chars(Laws.Spec.line(Vim.Vim.lines(y), Nat.add(r, Laws.F.top(Cl.Ck.frame(y, T.Visual{k, a}))))))))) == True{} : Bool}
  Imp(Nat.is_lt(r, Nat.sub(S.St.rows(y), 2n)), Laws.Spec.iff(Laws.Spec.in_runs(Vi.Vis.spans(k, C.St.lines(y), a, S.Win.cur(S.St.win(y)), S.Win.top(S.St.win(y)), C.St.h(y)), r, x), Bool.and(Nat.is_lt(Nat.add(r, S.Win.top(S.St.win(y))), Laws.Spec.count(C.St.lines(y))), Laws.Spec.picked(k, a, S.Win.cur(S.St.win(y)), Nat.add(r, S.Win.top(S.St.win(y))), x, Laws.Spec.chars(Laws.Spec.line(C.St.lines(y), Nat.add(r, S.Win.top(S.St.win(y)))))))), hd => Sel.in(C.St.lines(y), k, a, S.Win.cur(S.St.win(y)), S.Win.top(S.St.win(y)), C.St.h(y), r, x, hd))

def SelCells.at(m: T.Mode, +y: T.St, +fin: Fi.Final(y), hm: {S.St.mode(y) == m : T.Mode}, +r: Nat, +x: Nat) -> {Laws.Claim.sel_cells.at(m, y, r, x) == True{} : Bool}:
  match m:
    case T.Normal{}:
      {==}
    case T.Typing{kind, text}:
      {==}
    case T.Picking{kind, q, its, n, sel, top, pv, levels}:
      {==}
    case T.Visual{+k, +a}:
      SelCells.visual(y, fin, k, a, hm, r, x)

def SelCells.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>, +r: Nat, +x: Nat) -> {Laws.Claim.sel_cells(Laws.Spec.run(fs, rows, cols, evs), r, x) == True{} : Bool}:
  +y = Laws.Spec.run(fs, rows, cols, evs)
  SelCells.at(S.St.mode(y), y, Re.Reach.final(fs, rows, cols, evs), {==}, r, x)

def VisualLaws.sel_cells(fs, rows, cols, evs, r, x):
  SelCells.law(fs, rows, cols, evs, r, x)
