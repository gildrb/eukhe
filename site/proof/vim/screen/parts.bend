# eukhe.com's Neovim: the parts of the frame
# ==========================================
#
# The number column (View.nums), the search hits (View.hits), the
# scrollbar (View.bar), a picker's float (Float.fit), the cursor kept in
# it (Scr.inside), the command being typed (Scr.typed) and the
# statusline: each fits the screen, for any editor (vim/view.bend,
# vim/box.bend, vim/screen.bend).

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
import ../../../vim/buf.bend as B
import ../../../vim/view.bend as V
import ../../../vim/find.bend as F
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/box.bend as Bx
import ../../../vim/screen.bend as R
import ../../../laws/vim/base.bend as Laws
import ../../base.bend as L
import ../../base/text.bend as Tx
import ./base.bend as Sc

# Lists
# -----

def Count.rev(xs: List<&2, String>, +ys: List<&2, String>) -> {Laws.Spec.count(List.reverse.go(&2, String, xs, ys)) == Nat.add(Laws.Spec.count(xs), Laws.Spec.count(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.trans(Nat, Laws.Spec.count(List.reverse.go(&2, String, t, Con{h, ys})), Nat.add(Laws.Spec.count(t), 1n+Laws.Spec.count(ys)), 1n+Nat.add(Laws.Spec.count(t), Laws.Spec.count(ys)), Count.rev(t, Con{h, ys}), Equal.sym(Nat, 1n+Nat.add(Laws.Spec.count(t), Laws.Spec.count(ys)), Nat.add(Laws.Spec.count(t), 1n+Laws.Spec.count(ys)), L.Nat.add_succ(Laws.Spec.count(t), Laws.Spec.count(ys))))

def Cells.rev(xs: List<&2, String>, +ys: List<&2, String>, +w: Nat, +hx: {Laws.Spec.all_cells(xs, w) == True{} : Bool}, hy: {Laws.Spec.all_cells(ys, w) == True{} : Bool}) -> {Laws.Spec.all_cells(List.reverse.go(&2, String, xs, ys), w) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+h, t}:
      Cells.rev(t, Con{h, ys}, w, L.And.r(Nat.is_eq(Laws.Spec.cells(h), w), Laws.Spec.all_cells(t, w), hx), L.And.intro(Nat.is_eq(Laws.Spec.cells(h), w), Laws.Spec.all_cells(ys, w), L.And.l(Nat.is_eq(Laws.Spec.cells(h), w), Laws.Spec.all_cells(t, w), hx), hy))

def Spans.rev(xs: List<&2, T.Span>, +ys: List<&2, T.Span>, +h: Nat, +g: Nat, +c: Nat, +hx: {Laws.Spec.spans_in(xs, h, g, c) == True{} : Bool}, hy: {Laws.Spec.spans_in(ys, h, g, c) == True{} : Bool}) -> {Laws.Spec.spans_in(List.reverse.go(&2, T.Span, xs, ys), h, g, c) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{T.Span{+row, +col, +len}, t}:
      +a = Bool.and(Bool.and(Nat.is_lt(row, h), Nat.is_le(g, col)), Bool.and(Nat.is_lt(0n, len), Nat.is_le(Nat.add(col, len), c)))
      Spans.rev(t, Con{T.Span{row, col, len}, ys}, h, g, c, L.And.r(a, Laws.Spec.spans_in(t, h, g, c), hx), L.And.intro(a, Laws.Spec.spans_in(ys, h, g, c), L.And.l(a, Laws.Spec.spans_in(t, h, g, c), hx), hy))

def Marks.rev(xs: List<&2, T.Mark>, +ys: List<&2, T.Mark>, +h: Nat, +w: Nat, +hx: {Laws.Spec.count_marks(xs, h, w) == True{} : Bool}, hy: {Laws.Spec.count_marks(ys, h, w) == True{} : Bool}) -> {Laws.Spec.count_marks(List.reverse.go(&2, T.Mark, xs, ys), h, w) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{T.Mark{+row, +col, +len, +group}, t}:
      +a = Bool.and(Nat.is_lt(row, h), Nat.is_le(Nat.add(col, len), w))
      Marks.rev(t, Con{T.Mark{row, col, len, group}, ys}, h, w, L.And.r(a, Laws.Spec.count_marks(t, h, w), hx), L.And.intro(a, Laws.Spec.count_marks(ys, h, w), L.And.l(a, Laws.Spec.count_marks(t, h, w), hx), hy))

# a Nat equal to another compares equal
def Eq.of(+a: Nat, -b: Nat, e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  L.Nat.eq_refl(a)

# The number column
# -----------------

def Nums.count(r: Nat, +o: T.Opts, +k: Nat, +l: Nat, +last: Nat, +w: Nat, +g: Nat, +sign: String, +blank: String, +acc: List<&2, String>)
  -> {Laws.Spec.count(V.View.nums.go(r, o, k, l, last, w, g, sign, blank, acc)) == Nat.add(r, Laws.Spec.count(acc)) : Nat}:
  match r:
    case 0n:
      Equal.trans(Nat, Laws.Spec.count(List.reverse.go(&2, String, acc, Nil{})), Nat.add(Laws.Spec.count(acc), 0n), Laws.Spec.count(acc), Count.rev(acc, Nil{}), L.Nat.zero_r(Laws.Spec.count(acc)))
    case 1n++p:
      +x = Bool.pick(String, Nat.is_gt(k, last), blank, X.Text.fitted(sign ++ V.View.num(o, k, l, w), g))
      Equal.trans(Nat, Laws.Spec.count(V.View.nums.go(p, o, 1n+k, l, last, w, g, sign, blank, Con{x, acc})), Nat.add(p, 1n+Laws.Spec.count(acc)), 1n+Nat.add(p, Laws.Spec.count(acc)), Nums.count(p, o, 1n+k, l, last, w, g, sign, blank, Con{x, acc}), Equal.sym(Nat, 1n+Nat.add(p, Laws.Spec.count(acc)), Nat.add(p, 1n+Laws.Spec.count(acc)), L.Nat.add_succ(p, Laws.Spec.count(acc))))

def Nums.row(c: Bool, +blank: String, +s: String, +g: Nat, hb: {Laws.Spec.cells(blank) == g : Nat}) -> {Nat.is_eq(Laws.Spec.cells(Bool.pick(String, c, blank, X.Text.fitted(s, g))), g) == True{} : Bool}:
  match c:
    case True{}:
      Eq.of(Laws.Spec.cells(blank), g, hb)
    case False{}:
      Eq.of(Laws.Spec.cells(X.Text.fitted(s, g)), g, Tx.Fitted.cells(s, g))

def Nums.cells(r: Nat, +o: T.Opts, +k: Nat, +l: Nat, +last: Nat, +w: Nat, +g: Nat, +sign: String, +blank: String, +acc: List<&2, String>, +hb: {Laws.Spec.cells(blank) == g : Nat}, ha: {Laws.Spec.all_cells(acc, g) == True{} : Bool})
  -> {Laws.Spec.all_cells(V.View.nums.go(r, o, k, l, last, w, g, sign, blank, acc), g) == True{} : Bool}:
  match r:
    case 0n:
      Cells.rev(acc, Nil{}, g, ha, {==})
    case 1n+p:
      +s = sign ++ V.View.num(o, k, l, w)
      +x = Bool.pick(String, Nat.is_gt(k, last), blank, X.Text.fitted(s, g))
      Nums.cells(p, o, 1n+k, l, last, w, g, sign, blank, Con{x, acc}, hb, L.And.intro(Nat.is_eq(Laws.Spec.cells(x), g), Laws.Spec.all_cells(acc, g), Nums.row(Nat.is_gt(k, last), blank, s, g, hb), ha))

# the number column: one entry per text row
def Nums.ok_count(+h: Nat, +o: T.Opts, +top: Nat, +l: Nat, +last: Nat, +w: Nat, +signs: Bool, +g: Nat)
  -> {Nat.is_eq(Laws.Spec.count(V.View.nums(h, o, top, l, last, w, signs, g)), h) == True{} : Bool}:
  +sign = X.Text.spaces(V.View.signw(signs), SNil{})
  +blank = X.Text.spaces(g, SNil{})
  Eq.of(Laws.Spec.count(V.View.nums(h, o, top, l, last, w, signs, g)), h, Equal.trans(Nat, Laws.Spec.count(V.View.nums(h, o, top, l, last, w, signs, g)), Nat.add(h, 0n), h, Nums.count(h, o, top, l, last, w, g, sign, blank, Nil{}), L.Nat.zero_r(h)))

# each entry g cells
def Nums.ok_cells(+h: Nat, +o: T.Opts, +top: Nat, +l: Nat, +last: Nat, +w: Nat, +signs: Bool, +g: Nat)
  -> {Laws.Spec.all_cells(V.View.nums(h, o, top, l, last, w, signs, g), g) == True{} : Bool}:
  +sign = X.Text.spaces(V.View.signw(signs), SNil{})
  +blank = X.Text.spaces(g, SNil{})
  Nums.cells(h, o, top, l, last, w, g, sign, blank, Nil{}, Tx.Cells.blank(g), {==})

# Search hits
# -----------

def Span.ok(b: Bool, +r: Nat, +c: Nat, +n: Nat, +left: Nat, +w: Nat, +g: Nat, +h: Nat, +cols: Nat, +acc: List<&2, T.Span>,
  +e: {Nat.is_lt(Nat.max(c, left), Nat.min(Nat.add(c, n), Nat.add(left, w))) == b : Bool}, hr: L.LT(r, h), hgw: L.LE(Nat.add(g, w), cols), ha: {Laws.Spec.spans_in(acc, h, g, cols) == True{} : Bool})
  -> {Laws.Spec.spans_in(V.View.span.put(Bool.pick(Maybe<&2, T.Span>, b, Some{T.Span{r, Nat.add(g, Nat.sub(Nat.max(c, left), left)), Nat.sub(Nat.min(Nat.add(c, n), Nat.add(left, w)), Nat.max(c, left))}}, None{}), acc), h, g, cols) == True{} : Bool}:
  match b:
    case False{}:
      ha
    case True{}:
      +from = Nat.max(c, left)
      +to = Nat.min(Nat.add(c, n), Nat.add(left, w))
      +col = Nat.add(g, Nat.sub(from, left))
      +len = Nat.sub(to, from)
      +lf = L.Nat.le_max_r(c, left)
      +ft = L.Nat.lt_to_le(from, to, e)
      +tw = L.Nat.le_add_sub(to, left, w, L.LE.cast_r(to, Nat.add(left, w), Nat.add(w, left), L.Nat.add_comm(left, w), L.Nat.min_le_r(Nat.add(c, n), Nat.add(left, w))))
      +e1 = Equal.trans(Nat, Nat.add(col, len), Nat.add(g, Nat.add(Nat.sub(from, left), len)), Nat.add(g, Nat.sub(to, left)), L.Nat.add_assoc(g, Nat.sub(from, left), len), Equal.cong(Nat, Nat, z => Nat.add(g, z), Nat.add(Nat.sub(from, left), len), Nat.sub(to, left), L.Nat.sub_chain(left, from, to, lf, ft)))
      +q = L.LE.cast_l(Nat.add(g, Nat.sub(to, left)), Nat.add(col, len), cols, Equal.sym(Nat, Nat.add(col, len), Nat.add(g, Nat.sub(to, left)), e1), L.Nat.le_trans(Nat.add(g, Nat.sub(to, left)), Nat.add(g, w), cols, L.Nat.le_add_mono(g, Nat.sub(to, left), w, tw), hgw))
      +a1 = L.And.intro(Nat.is_lt(r, h), Nat.is_le(g, col), hr, L.Nat.le_add(g, Nat.sub(from, left)))
      +a2 = L.And.intro(Nat.is_lt(0n, len), Nat.is_le(Nat.add(col, len), cols), L.Nat.sub_pos(from, to, e), q)
      +a = Bool.and(Bool.and(Nat.is_lt(r, h), Nat.is_le(g, col)), Bool.and(Nat.is_lt(0n, len), Nat.is_le(Nat.add(col, len), cols)))
      L.And.intro(a, Laws.Spec.spans_in(acc, h, g, cols), L.And.intro(Bool.and(Nat.is_lt(r, h), Nat.is_le(g, col)), Bool.and(Nat.is_lt(0n, len), Nat.is_le(Nat.add(col, len), cols)), a1, a2), ha)

def Spans.ok(cs: List<&2, Nat>, +r: Nat, +n: Nat, +left: Nat, +w: Nat, +g: Nat, +h: Nat, +cols: Nat, +acc: List<&2, T.Span>, +hr: L.LT(r, h), +hgw: L.LE(Nat.add(g, w), cols), ha: {Laws.Spec.spans_in(acc, h, g, cols) == True{} : Bool})
  -> {Laws.Spec.spans_in(V.View.spans(cs, r, n, left, w, g, acc), h, g, cols) == True{} : Bool}:
  match cs:
    case Nil{}:
      ha
    case Con{+c, t}:
      +m = V.View.span(r, c, n, left, w, g)
      Spans.ok(t, r, n, left, w, g, h, cols, V.View.span.put(m, acc), hr, hgw, Span.ok(Nat.is_lt(Nat.max(c, left), Nat.min(Nat.add(c, n), Nat.add(left, w))), r, c, n, left, w, g, h, cols, acc, {==}, hr, hgw, ha))

def Hits.go(rows: Nat, ls: List<&2, String>, fls: List<&2, String>, +f: T.Find, +n: Nat, +r: Nat, +left: Nat, +w: Nat, +g: Nat, +h: Nat, +cols: Nat, +acc: List<&2, T.Span>,
  hrows: L.LE(Nat.add(r, rows), h), +hgw: L.LE(Nat.add(g, w), cols), ha: {Laws.Spec.spans_in(acc, h, g, cols) == True{} : Bool})
  -> {Laws.Spec.spans_in(V.View.hits.go(rows, ls, fls, f, n, r, left, w, g, acc), h, g, cols) == True{} : Bool}:
  match rows ls fls:
    case 0n _ _:
      Spans.rev(acc, Nil{}, h, g, cols, ha, {==})
    case 1n+p Nil{} Nil{}:
      Spans.rev(acc, Nil{}, h, g, cols, ha, {==})
    case 1n+p Nil{} Con{fx, ft}:
      Spans.rev(acc, Nil{}, h, g, cols, ha, {==})
    case 1n+p Con{+x, t} Nil{}:
      Spans.rev(acc, Nil{}, h, g, cols, ha, {==})
    case 1n++p Con{x, t} Con{+fx, ft}:
      +rp = L.LE.cast_l(Nat.add(r, 1n+p), 1n+Nat.add(r, p), h, Equal.sym(Nat, 1n+Nat.add(r, p), Nat.add(r, 1n+p), L.Nat.add_succ(r, p)), hrows)
      +hr = L.Nat.le_lt(r, h, L.Nat.le_trans(1n+r, 1n+Nat.add(r, p), h, L.Nat.le_add(r, p), rp))
      Hits.go(p, t, ft, f, n, 1n+r, left, w, g, h, cols, V.View.spans(F.Find.hits(f, x, fx), r, n, left, w, g, acc), rp, hgw, Spans.ok(F.Find.hits(f, x, fx), r, n, left, w, g, h, cols, acc, hr, hgw, ha))

# the hits of any search the screen highlights: on the text rows, right
# of the gutter, within the screen
def Hits.ok(+s: T.St, lit: Maybe<&2, T.Find>, hg: L.LE(C.St.g(s), S.St.cols(s))) -> {Laws.Spec.spans_in(R.Scr.hits(s, lit), C.St.h(s), C.St.g(s), S.St.cols(s)) == True{} : Bool}:
  match lit:
    case None{}:
      {==}
    case Some{f}:
      match f:
        case T.Find{+text, +back, +word}:
          +g = C.St.g(s)
          +cols = S.St.cols(s)
          +hgw = L.LE.cast_r(Nat.add(g, Nat.sub(cols, g)), Nat.add(g, Nat.sub(cols, g)), cols, L.Nat.add_sub(cols, g, hg), L.Nat.le_refl(Nat.add(g, Nat.sub(cols, g))))
          +top = S.Win.top(S.St.win(s))
          Hits.go(C.St.h(s), B.Lines.drop(C.St.lines(s), top), B.Lines.drop(C.St.folds(s), top), T.Find{text, back, word}, X.Text.len(text), 0n, S.Win.left(S.St.win(s)), C.St.w(s), g, C.St.h(s), cols, Nil{}, L.Nat.le_refl(C.St.h(s)), hgw, {==})

# The scrollbar
# -------------

def Bar.at(b: Bool, +start: Nat, +len: Nat, +c: Nat, +h: Nat, hs: L.LE(start, Nat.sub(h, len)), hl: L.LE(len, h)) -> {Laws.Spec.bar_ok(Bool.pick(T.Span, b, T.Span{start, c, len}, T.Span{0n, c, 0n}), h) == True{} : Bool}:
  match b:
    case True{}:
      L.LE.cast_r(Nat.add(start, len), Nat.add(Nat.sub(h, len), len), h, L.Nat.sub_add(h, len, hl), L.Nat.le_addr(start, Nat.sub(h, len), len, hs))
    case False{}:
      L.Nat.le_zero(h)

# the scrollbar within the text rows
def Bar.ok(+n: Nat, +h: Nat, +top: Nat, +c: Nat) -> {Laws.Spec.bar_ok(V.View.bar(n, h, top, c), h) == True{} : Bool}:
  +len = Nat.min(Nat.max(1n, Nat.div(Nat.mul(h, h), Nat.max(n, 1n))), h)
  +start = Nat.min(Nat.div(Nat.mul(top, h), Nat.max(n, 1n)), Nat.sub(h, len))
  Bar.at(Nat.is_gt(n, h), start, len, c, h, L.Nat.min_le_r(Nat.div(Nat.mul(top, h), Nat.max(n, 1n)), Nat.sub(h, len)), L.Nat.min_le_r(Nat.max(1n, Nat.div(Nat.mul(h, h), Nat.max(n, 1n))), h))

def Bar.col_at(b: Bool, +start: Nat, +len: Nat, +c: Nat) -> {Nat.is_eq(Laws.Spec.bar_col(Bool.pick(T.Span, b, T.Span{start, c, len}, T.Span{0n, c, 0n})), c) == True{} : Bool}:
  match b:
    case True{}:
      L.Nat.eq_refl(c)
    case False{}:
      L.Nat.eq_refl(c)

# the scrollbar in column c
def Bar.col(+n: Nat, +h: Nat, +top: Nat, +c: Nat) -> {Nat.is_eq(Laws.Spec.bar_col(V.View.bar(n, h, top, c)), c) == True{} : Bool}:
  +len = Nat.min(Nat.max(1n, Nat.div(Nat.mul(h, h), Nat.max(n, 1n))), h)
  +start = Nat.min(Nat.div(Nat.mul(top, h), Nat.max(n, 1n)), Nat.sub(h, len))
  Bar.col_at(Nat.is_gt(n, h), start, len, c)

# Floats
# ------

def FRows.count(t: List<&2, String>, +x: String, k: Nat, +w: Nat) -> {Laws.Spec.count(Bx.Float.rows(Con{x, t}, k, w)) == Nat.min(1n+List.length(&2, String, t), 1n+k) : Nat}:
  match t k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{+y, +u} 0n:
      Equal.trans(Nat, Laws.Spec.count(Bx.Float.rows(Con{y, u}, 0n, w)), 1n+Nat.min(List.length(&2, String, u), 0n), 1n, FRows.count(u, y, 0n, w), Equal.cong(Nat, Nat, z => 1n+z, Nat.min(List.length(&2, String, u), 0n), 0n, L.Nat.min_zero_r(List.length(&2, String, u))))
    case Con{+y, +u} 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Laws.Spec.count(Bx.Float.rows(Con{y, u}, p, w)), Nat.min(1n+List.length(&2, String, u), 1n+p), FRows.count(u, y, p, w))

def FRows.cells(ls: List<&2, String>, k: Nat, +w: Nat) -> {Laws.Spec.all_cells(Bx.Float.rows(ls, k, w), w) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+x, t}:
      match t k:
        case Nil{} 0n:
          L.And.intro(Nat.is_eq(Laws.Spec.cells(X.Text.fitted(x, w)), w), True{}, Eq.of(Laws.Spec.cells(X.Text.fitted(x, w)), w, Tx.Fitted.cells(x, w)), {==})
        case Nil{} 1n+p:
          L.And.intro(Nat.is_eq(Laws.Spec.cells(X.Text.fitted(x, w)), w), True{}, Eq.of(Laws.Spec.cells(X.Text.fitted(x, w)), w, Tx.Fitted.cells(x, w)), {==})
        case Con{+y, +u} 0n:
          FRows.cells(Con{y, u}, 0n, w)
        case Con{+y, +u} 1n+p:
          L.And.intro(Nat.is_eq(Laws.Spec.cells(X.Text.fitted(x, w)), w), Laws.Spec.all_cells(Bx.Float.rows(Con{y, u}, p, w), w), Eq.of(Laws.Spec.cells(X.Text.fitted(x, w)), w, Tx.Fitted.cells(x, w)), FRows.cells(Con{y, u}, p, w))

# or(a, b) with b False is a
def Or.left(a: Bool, -b: Bool, eb: {b == False{} : Bool}, h: {Bool.or(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      L.Bool.both({False{} == True{} : Bool}, b, h, eb)

# a kept mark's row, on the float's h rows: the last row's moved to h - 1
def Mark.row(b: Bool, +r: Nat, +h: Nat, -o: Nat, e: {Nat.is_eq(1n+r, o) == b : Bool}, hk: {Bool.or(Nat.is_lt(1n+r, h), b) == True{} : Bool}, h1: L.LE(1n, h)) -> L.LT(Bool.pick(Nat, b, Nat.sub(h, 1n), r), h):
  match b:
    case True{}:
      Sc.Nat.le_pred_lt(Nat.sub(h, 1n), h, L.Nat.le_refl(Nat.sub(h, 1n)), h1)
    case False{}:
      L.Nat.le_lt(r, h, L.Nat.lt_to_le(1n+r, h, Or.left(Nat.is_lt(1n+r, h), False{}, {==}, hk)))

def Mark.keep(k: Bool, +r: Nat, +c: Nat, +len: Nat, +g: T.Group, +n: Nat, +h: Nat, +w: Nat, +acc: List<&2, T.Mark>,
  +e: {Bool.and(Bool.or(Nat.is_lt(1n+r, h), Nat.is_eq(1n+r, n)), Nat.is_lt(c, w)) == k : Bool}, h1: L.LE(1n, h), ha: {Laws.Spec.count_marks(acc, h, w) == True{} : Bool})
  -> {Laws.Spec.count_marks(Bool.pick(List<&2, T.Mark>, k, T.Mark{Bool.pick(Nat, Nat.is_eq(1n+r, n), Nat.sub(h, 1n), r), c, Nat.min(len, Nat.sub(w, c)), g} <> acc, acc), h, w) == True{} : Bool}:
  match k:
    case False{}:
      ha
    case True{}:
      +or = Bool.or(Nat.is_lt(1n+r, h), Nat.is_eq(1n+r, n))
      +hor = L.And.l(or, Nat.is_lt(c, w), e)
      +hc = L.And.r(or, Nat.is_lt(c, w), e)
      +r2 = Bool.pick(Nat, Nat.is_eq(1n+r, n), Nat.sub(h, 1n), r)
      +m = Nat.min(len, Nat.sub(w, c))
      +hm = L.Nat.le_trans(Nat.add(c, m), Nat.add(c, Nat.sub(w, c)), w, L.Nat.le_add_mono(c, m, Nat.sub(w, c), L.Nat.min_le_r(len, Nat.sub(w, c))), L.LE.cast_r(Nat.add(c, Nat.sub(w, c)), Nat.add(c, Nat.sub(w, c)), w, L.Nat.add_sub(w, c, L.Nat.lt_to_le(c, w, hc)), L.Nat.le_refl(Nat.add(c, Nat.sub(w, c)))))
      +a = Bool.and(Nat.is_lt(r2, h), Nat.is_le(Nat.add(c, m), w))
      L.And.intro(a, Laws.Spec.count_marks(acc, h, w), L.And.intro(Nat.is_lt(r2, h), Nat.is_le(Nat.add(c, m), w), Mark.row(Nat.is_eq(1n+r, n), r, h, n, {==}, hor, h1), hm), ha)

def Marks.ok(ms: List<&2, T.Mark>, +n: Nat, +h: Nat, +w: Nat, +acc: List<&2, T.Mark>, +h1: L.LE(1n, h), ha: {Laws.Spec.count_marks(acc, h, w) == True{} : Bool}) -> {Laws.Spec.count_marks(Bx.Marks.fit(ms, n, h, w, acc), h, w) == True{} : Bool}:
  match ms:
    case Nil{}:
      Marks.rev(acc, Nil{}, h, w, ha, {==})
    case Con{T.Mark{+r, +c, +len, +g}, t}:
      +k = Bool.and(Bool.or(Nat.is_lt(1n+r, h), Nat.is_eq(1n+r, n)), Nat.is_lt(c, w))
      +acc2 = Bool.pick(List<&2, T.Mark>, k, T.Mark{Bool.pick(Nat, Nat.is_eq(1n+r, n), Nat.sub(h, 1n), r), c, Nat.min(len, Nat.sub(w, c)), g} <> acc, acc)
      Marks.ok(t, n, h, w, acc2, h1, Mark.keep(k, r, c, len, g, n, h, w, acc, {==}, h1, ha))

def Some.len(ls: List<&2, String>) -> L.LE(1n, List.length(&2, String, B.Lines.some(ls))):
  match ls:
    case Nil{}:
      {==}
    case Con{h, t}:
      L.Nat.le_zero(List.length(&2, String, t))

def FRows.fit_at(+x: String, +t: List<&2, String>, +rows: Nat, +w: Nat, hR: L.LE(1n, rows))
  -> {Nat.is_eq(Laws.Spec.lines_count(Bx.Float.rows(Con{x, t}, Nat.sub(Nat.min(1n+List.length(&2, String, t), rows), 1n), w)), Nat.min(1n+List.length(&2, String, t), rows)) == True{} : Bool}:
  +n = {1n+List.length(&2, String, t) : Nat}
  +h = Nat.min(n, rows)
  +h1 = L.Nat.le_min(1n, n, rows, L.Nat.le_zero(List.length(&2, String, t)), hR)
  +c = Laws.Spec.count(Bx.Float.rows(Con{x, t}, Nat.sub(h, 1n), w))
  +e1 = Equal.trans(Nat, c, Nat.min(n, 1n+Nat.sub(h, 1n)), Nat.min(n, h), FRows.count(t, x, Nat.sub(h, 1n), w), Equal.cong(Nat, Nat, z => Nat.min(n, z), 1n+Nat.sub(h, 1n), h, L.Nat.succ_pred(h, h1)))
  Eq.of(c, h, Equal.trans(Nat, c, Nat.min(n, h), h, e1, L.Nat.min_eq_r(n, h, L.Nat.min_le_l(n, rows))))

# the rows Float.fit keeps: h of them, h at most the n lines (n >= 1)
def FRows.fit(ls: List<&2, String>, +rows: Nat, +w: Nat, hR: L.LE(1n, rows))
  -> {Nat.is_eq(Laws.Spec.lines_count(Bx.Float.rows(B.Lines.some(ls), Nat.sub(Nat.min(List.length(&2, String, B.Lines.some(ls)), rows), 1n), w)), Nat.min(List.length(&2, String, B.Lines.some(ls)), rows)) == True{} : Bool}:
  match ls:
    case Nil{}:
      FRows.fit_at("", Nil{}, rows, w, hR)
    case Con{+x, +t}:
      FRows.fit_at(x, t, rows, w, hR)


# a float Float.fit keeps on a screen of rows x cols (both at least 1):
# inside it, as many rows as it says, each as wide, its marks inside
def FloatFit.ok(D: T.Float, +rows: Nat, +cols: Nat, +hR: L.LE(1n, rows), hC: L.LE(1n, cols)) -> {Laws.Spec.float_ok(Some{Bx.Float.fit(D, rows, cols)}, rows, cols) == True{} : Bool}:
  match D:
    case T.Float{+row, +col, +width, height, +lines, +marks}:
      +w = Nat.max(1n, Nat.min(width, cols))
      +ls = B.Lines.some(lines)
      +n = List.length(&2, String, ls)
      +h = Nat.min(n, rows)
      +r2 = Nat.min(row, Nat.sub(rows, h))
      +c2 = Nat.min(col, Nat.sub(cols, w))
      +rs = Bx.Float.rows(ls, Nat.sub(h, 1n), w)
      +ms = Bx.Marks.fit(marks, n, h, w, Nil{})
      +hh = L.Nat.min_le_r(n, rows)
      +hw = L.Nat.max_le(1n, Nat.min(width, cols), cols, hC, L.Nat.min_le_r(width, cols))
      +h1 = L.Nat.le_min(1n, n, rows, Some.len(lines), hR)
      +b1 = L.LE.cast_r(Nat.add(r2, h), Nat.add(Nat.sub(rows, h), h), rows, L.Nat.sub_add(rows, h, hh), L.Nat.le_addr(r2, Nat.sub(rows, h), h, L.Nat.min_le_r(row, Nat.sub(rows, h))))
      +b2 = L.LE.cast_r(Nat.add(c2, w), Nat.add(Nat.sub(cols, w), w), cols, L.Nat.sub_add(cols, w, hw), L.Nat.le_addr(c2, Nat.sub(cols, w), w, L.Nat.min_le_r(col, Nat.sub(cols, w))))
      L.And.intro(Laws.Spec.box_in(r2, c2, h, w, rows, cols), Bool.and(Nat.is_eq(Laws.Spec.lines_count(rs), h), Bool.and(Laws.Spec.all_cells(rs, w), Laws.Spec.count_marks(ms, h, w))),
        L.And.intro(Nat.is_le(Nat.add(r2, h), rows), Nat.is_le(Nat.add(c2, w), cols), b1, b2),
        Sc.And3(Nat.is_eq(Laws.Spec.lines_count(rs), h), Laws.Spec.all_cells(rs, w), Laws.Spec.count_marks(ms, h, w), FRows.fit(lines, rows, w, hR), FRows.cells(ls, Nat.sub(h, 1n), w), Marks.ok(marks, n, h, w, Nil{}, h1, {==})))

# a coordinate clamped into [row, row + h - 1] (h >= 1) is in it
def Clamp(+r: Nat, +row: Nat, +h: Nat, +h1: L.LE(1n, h)) -> {Bool.and(Nat.is_le(row, Nat.min(Nat.max(r, row), Nat.sub(Nat.add(row, h), 1n))), Nat.is_lt(Nat.min(Nat.max(r, row), Nat.sub(Nat.add(row, h), 1n)), Nat.add(row, h))) == True{} : Bool}:
  +e = Nat.sub(Nat.add(row, h), 1n)
  +x = Nat.min(Nat.max(r, row), e)
  +hre = L.Nat.le_sub_of_add(row, 1n, Nat.add(row, h), L.Nat.le_add_mono(row, 1n, h, h1))
  +pos = L.Nat.le_trans(1n, h, Nat.add(row, h), h1, L.Nat.le_add_l(row, h))
  +lt = L.Nat.le_lt_trans(x, e, Nat.add(row, h), L.Nat.min_le_r(Nat.max(r, row), e), Sc.Nat.le_pred_lt(e, Nat.add(row, h), L.Nat.le_refl(e), pos))
  L.And.intro(Nat.is_le(row, x), Nat.is_lt(x, Nat.add(row, h)), L.Nat.le_min(row, Nat.max(r, row), e, L.Nat.le_max_r(r, row), hre), lt)

# the cursor kept inside a picker's float (Scr.inside) is inside it
def CursorIn.pick(fs: List<&2, T.Buf>, +s: T.St, -tgt: T.Tgt, -top: Nat, -left: Nat, -g: Nat, -nums: List<&2, String>, c: T.Cell, -ch: String, -cmd: String, -hits: List<&2, T.Span>, -bar: T.Span, -cl: Bool, -st: String, D: T.Float, +rows: Nat, +cols: Nat, hR: L.LE(1n, rows), hC: L.LE(1n, cols))
  -> {Laws.Spec.cursor_in(fs, s, T.Frame{tgt, top, left, g, nums, R.Scr.inside(c, Some{Bx.Float.fit(D, rows, cols)}), ch, cmd, hits, bar, cl, st, Some{Bx.Float.fit(D, rows, cols)}}, rows, cols, Some{Bx.Float.fit(D, rows, cols)}) == True{} : Bool}:
  match c D:
    case T.Cell{+r, +k} T.Float{+row, +col, +width, height, +lines, marks}:
      +w = Nat.max(1n, Nat.min(width, cols))
      +n = List.length(&2, String, B.Lines.some(lines))
      +h = Nat.min(n, rows)
      +r2 = Nat.min(row, Nat.sub(rows, h))
      +c2 = Nat.min(col, Nat.sub(cols, w))
      +h1 = L.Nat.le_min(1n, n, rows, Some.len(lines), hR)
      +w1 = L.Nat.le_max_l(1n, Nat.min(width, cols))
      +x = Nat.min(Nat.max(r, r2), Nat.sub(Nat.add(r2, h), 1n))
      +y = Nat.min(Nat.max(k, c2), Nat.sub(Nat.add(c2, w), 1n))
      L.And.intro(Bool.and(Nat.is_le(r2, x), Nat.is_lt(x, Nat.add(r2, h))), Bool.and(Nat.is_le(c2, y), Nat.is_lt(y, Nat.add(c2, w))), Clamp(r, r2, h, h1), Clamp(k, c2, w, w1))

# The command line
# ----------------

# a command typed: its prefix takes a cell
def Prefix.cells(k: T.Line, +text: String) -> L.LE(1n, Laws.Spec.cells(R.Scr.prefix(k) ++ text)):
  match k:
    case T.Colon{}:
      L.Nat.le_zero(Laws.Spec.cells(text))
    case T.Slash{}:
      L.Nat.le_zero(Laws.Spec.cells(text))
    case T.Quest{}:
      L.Nat.le_zero(Laws.Spec.cells(text))

# what the command line shows of a command: min(its cells, cols - 1)
def Typed.cells(+line: String, +cols: Nat) -> {Laws.Spec.cells(R.Scr.typed(line, cols)) == Nat.sub(Laws.Spec.cells(line), Nat.sub(Laws.Spec.cells(line), Nat.sub(cols, 1n))) : Nat}:
  +c = Laws.Spec.cells(line)
  Equal.trans(Nat, Laws.Spec.cells(R.Scr.typed(line, cols)), Nat.sub(c, Nat.sub(X.Text.cells(line), Nat.sub(cols, 1n))), Nat.sub(c, Nat.sub(c, Nat.sub(cols, 1n))),
    Tx.Drop.cells(line, Nat.sub(X.Text.cells(line), Nat.sub(cols, 1n))), Equal.cong(Nat, Nat, z => Nat.sub(c, Nat.sub(z, Nat.sub(cols, 1n))), X.Text.cells(line), c, Tx.Cells.eq(line)))

def Typed.le(+line: String, +cols: Nat) -> L.LE(Laws.Spec.cells(R.Scr.typed(line, cols)), Nat.sub(cols, 1n)):
  +c = Laws.Spec.cells(line)
  L.LE.cast_l(Nat.sub(c, Nat.sub(c, Nat.sub(cols, 1n))), Laws.Spec.cells(R.Scr.typed(line, cols)), Nat.sub(cols, 1n), Equal.sym(Nat, Laws.Spec.cells(R.Scr.typed(line, cols)), Nat.sub(c, Nat.sub(c, Nat.sub(cols, 1n))), Typed.cells(line, cols)), L.Nat.sub_sub_le(c, Nat.sub(cols, 1n)))

# the cursor after it is on screen
def Typed.lt(+line: String, +cols: Nat, hC: L.LE(1n, cols)) -> L.LT(X.Text.cells(R.Scr.typed(line, cols)), cols):
  +t = R.Scr.typed(line, cols)
  Sc.Nat.le_pred_lt(X.Text.cells(t), cols, L.LE.cast_l(Laws.Spec.cells(t), X.Text.cells(t), Nat.sub(cols, 1n), Equal.sym(Nat, X.Text.cells(t), Laws.Spec.cells(t), Tx.Cells.eq(t)), Typed.le(line, cols)), hC)

# a command shows at least a cell: not empty
def Typed.some(+line: String, +cols: Nat, hc: L.LE(1n, Laws.Spec.cells(line)), hk: L.LE(1n, Nat.sub(cols, 1n))) -> {String.is_empty(R.Scr.typed(line, cols)) == False{} : Bool}:
  +c = Laws.Spec.cells(line)
  +t = R.Scr.typed(line, cols)
  +one = L.LE.cast_r(1n, Nat.sub(c, Nat.sub(c, Nat.sub(cols, 1n))), Laws.Spec.cells(t), Equal.sym(Nat, Laws.Spec.cells(t), Nat.sub(c, Nat.sub(c, Nat.sub(cols, 1n))), Typed.cells(line, cols)), L.Nat.sub_sub_pos(c, Nat.sub(cols, 1n), hc, hk))
  Tx.Cells.some(t, L.Nat.le_lt(0n, Laws.Spec.cells(t), one))

# The statusline
# --------------

# the statusline: exactly c cells
def Status.cells(+name: String, +flag: String, +ruler: String, +c: Nat) -> {Laws.Spec.cells(R.Scr.status(name, flag, ruler, c)) == c : Nat}:
  +right = " " ++ ruler ++ " "
  Tx.Fitted.cells(X.Text.fit(" " ++ name ++ " " ++ flag, Nat.sub(c, X.Text.cells(right))) ++ right, c)
