# eukhe.com's Neovim: the cells of the strings the screen shows
# =============================================================
#
# Text.fit gives exactly w cells, Text.cut at most w, Text.dropc drops n
# (vim/text.bend), in the spec's count of cells (Spec.cells: fff's goose
# two, every other character one). And the editor's own counts of
# characters, lines and cells are the spec's.

import Base
import ../../vim/text.bend as X
import ../../vim/buf.bend as B
import ../../vim/screen.bend as R
import ../../laws/vim/base.bend as Laws
import ../base.bend as L

# the cells of character x
def W(+x: U32) -> Nat:
  Bool.pick(Nat, U32.is_eq(x, 129727), 2n, 1n)

# Counts
# ------

def Cells.append(a: String, +b: String) -> {Laws.Spec.cells(String.append(a, b)) == Nat.add(Laws.Spec.cells(a), Laws.Spec.cells(b)) : Nat}:
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +t}:
      +w = W(x)
      Equal.trans(Nat, Nat.add(w, Laws.Spec.cells(String.append(t, b))), Nat.add(w, Nat.add(Laws.Spec.cells(t), Laws.Spec.cells(b))), Nat.add(Nat.add(w, Laws.Spec.cells(t)), Laws.Spec.cells(b)),
        Equal.cong(Nat, Nat, y => Nat.add(w, y), Laws.Spec.cells(String.append(t, b)), Nat.add(Laws.Spec.cells(t), Laws.Spec.cells(b)), Cells.append(t, b)),
        Equal.sym(Nat, Nat.add(Nat.add(w, Laws.Spec.cells(t)), Laws.Spec.cells(b)), Nat.add(w, Nat.add(Laws.Spec.cells(t), Laws.Spec.cells(b))), L.Nat.add_assoc(w, Laws.Spec.cells(t), Laws.Spec.cells(b))))

def Cells.spaces(n: Nat, +acc: String) -> {Laws.Spec.cells(X.Text.spaces(n, acc)) == Nat.add(n, Laws.Spec.cells(acc)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat, Laws.Spec.cells(X.Text.spaces(p, SCon{' ', acc})), Nat.add(p, 1n+Laws.Spec.cells(acc)), 1n+Nat.add(p, Laws.Spec.cells(acc)), Cells.spaces(p, SCon{' ', acc}), Equal.sym(Nat, 1n+Nat.add(p, Laws.Spec.cells(acc)), Nat.add(p, 1n+Laws.Spec.cells(acc)), L.Nat.add_succ(p, Laws.Spec.cells(acc))))

# the cells of n blanks
def Cells.blank(+n: Nat) -> {Laws.Spec.cells(X.Text.spaces(n, SNil{})) == n : Nat}:
  Equal.trans(Nat, Laws.Spec.cells(X.Text.spaces(n, SNil{})), Nat.add(n, 0n), n, Cells.spaces(n, SNil{}), L.Nat.zero_r(n))

def Cells.go(s: String, +acc: Nat) -> {X.Text.cells.go(s, acc) == Nat.add(acc, Laws.Spec.cells(s)) : Nat}:
  match s:
    case SNil{}:
      L.Nat.add_zero(acc)
    case SCon{Chr{+x}, +t}:
      Equal.trans(Nat, X.Text.cells.go(t, Nat.add(acc, W(x))), Nat.add(Nat.add(acc, W(x)), Laws.Spec.cells(t)), Nat.add(acc, Nat.add(W(x), Laws.Spec.cells(t))), Cells.go(t, Nat.add(acc, W(x))), L.Nat.add_assoc(acc, W(x), Laws.Spec.cells(t)))

# the editor's count of cells is the spec's
def Cells.eq(+s: String) -> {X.Text.cells(s) == Laws.Spec.cells(s) : Nat}:
  Cells.go(s, 0n)

def Chars.go(s: String, +acc: Nat) -> {X.Text.len.go(s, acc) == Nat.add(Laws.Spec.chars(s), acc) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, +t}:
      Equal.trans(Nat, X.Text.len.go(t, 1n+acc), Nat.add(Laws.Spec.chars(t), 1n+acc), 1n+Nat.add(Laws.Spec.chars(t), acc), Chars.go(t, 1n+acc), Equal.sym(Nat, 1n+Nat.add(Laws.Spec.chars(t), acc), Nat.add(Laws.Spec.chars(t), 1n+acc), L.Nat.add_succ(Laws.Spec.chars(t), acc)))

# the editor's count of characters is the spec's
def Chars.eq(+s: String) -> {X.Text.len(s) == Laws.Spec.chars(s) : Nat}:
  Equal.trans(Nat, X.Text.len(s), Nat.add(Laws.Spec.chars(s), 0n), Laws.Spec.chars(s), Chars.go(s, 0n), L.Nat.zero_r(Laws.Spec.chars(s)))

def Count.go(ls: List<&2, String>, +acc: Nat) -> {B.Lines.len.go(ls, acc) == Nat.add(Laws.Spec.count(ls), acc) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.trans(Nat, B.Lines.len.go(t, 1n+acc), Nat.add(Laws.Spec.count(t), 1n+acc), 1n+Nat.add(Laws.Spec.count(t), acc), Count.go(t, 1n+acc), Equal.sym(Nat, 1n+Nat.add(Laws.Spec.count(t), acc), Nat.add(Laws.Spec.count(t), 1n+acc), L.Nat.add_succ(Laws.Spec.count(t), acc)))

# the editor's count of lines is the spec's
def Count.eq(+ls: List<&2, String>) -> {B.Lines.len(ls) == Laws.Spec.count(ls) : Nat}:
  Equal.trans(Nat, B.Lines.len(ls), Nat.add(Laws.Spec.count(ls), 0n), Laws.Spec.count(ls), Count.go(ls, 0n), L.Nat.zero_r(Laws.Spec.count(ls)))

# the editor's line i is the spec's
def Line.eq(ls: List<&2, String>, i: Nat) -> {B.Lines.at(ls, i) == Laws.Spec.line(ls, i) : String}:
  match ls i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      Line.eq(t, p)

# the character the frame names is the spec's
def Char.eq(s: String, c: Nat) -> {R.Scr.char(X.Text.at(s, c)) == Laws.Spec.char(s, c) : String}:
  match s c:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      Char.eq(t, p)

# Equal strings
# -------------

def Word.cmp_refl(+n: Nat, +x: Word(n)) -> {Word.cmp(n, x, x) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match x:
        case WCon{False{}, +xt}:
          %Equal.sym(Cmp, Word.cmp(p, xt, xt), EQ{}, Word.cmp_refl(p, xt)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}
        case WCon{True{}, +xt}:
          %Equal.sym(Cmp, Word.cmp(p, xt, xt), EQ{}, Word.cmp_refl(p, xt)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
          {==}

def U32.cmp_refl(+a: U32) -> {U32.cmp(a, a) == EQ{} : Cmp}:
  match a:
    case U32{+x}:
      Word.cmp_refl(32n, x)

def String.order_refl(s: String) -> {String.order.go(s, s, EQ{}) == EQ{} : Cmp}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +t}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, U32.cmp_refl(x)) : {String.order.go(t, t, _) == EQ{} : Cmp}
      String.order_refl(t)

def String.eq_refl(+s: String) -> {String.eq(s, s) == True{} : Bool}:
  %Equal.sym(Cmp, String.order.go(s, s, EQ{}), EQ{}, String.order_refl(s)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def String.eq_same(+a: String, -b: String, e: {a == b : String}) -> {String.eq(a, b) == True{} : Bool}:
  %e : {String.eq(a, _) == True{} : Bool}
  String.eq_refl(a)

# Fit, cut, drop
# --------------

# a string and n blanks after it
def Fit.tail(+a: String, +pad: Nat) -> {Laws.Spec.cells(String.append(a, X.Text.spaces(pad, SNil{}))) == Nat.add(Laws.Spec.cells(a), pad) : Nat}:
  Equal.trans(Nat, Laws.Spec.cells(String.append(a, X.Text.spaces(pad, SNil{}))), Nat.add(Laws.Spec.cells(a), Laws.Spec.cells(X.Text.spaces(pad, SNil{}))), Nat.add(Laws.Spec.cells(a), pad),
    Cells.append(a, X.Text.spaces(pad, SNil{})), Equal.cong(Nat, Nat, y => Nat.add(Laws.Spec.cells(a), y), Laws.Spec.cells(X.Text.spaces(pad, SNil{})), pad, Cells.blank(pad)))

# no cells left: pad blanks
def Fit.pad(s: String, +pad: Nat, +a: String) -> {Laws.Spec.cells(X.Text.fit.go(s, 0n, pad, SCon{' ', a})) == Nat.add(Laws.Spec.cells(a), pad) : Nat}:
  match s:
    case SNil{}:
      Fit.tail(a, pad)
    case SCon{h, t}:
      Fit.tail(a, pad)

# a + c taking W(x) cells, then 1 + p - W(x) cells: a and 1 + p
def Fit.arith(+a: String, +x: U32, +p: Nat, le: L.LE(W(x), 1n+p)) -> {Nat.add(Laws.Spec.cells(String.append(a, SCon{Chr{x}, SNil{}})), Nat.sub(1n+p, W(x))) == Nat.add(Laws.Spec.cells(a), 1n+p) : Nat}:
  +c = Laws.Spec.cells(a)
  +w = W(x)
  +w0 = Nat.add(w, 0n)
  +s = Nat.sub(1n+p, w)
  +e1 = Equal.cong(Nat, Nat, y => Nat.add(y, s), Laws.Spec.cells(String.append(a, SCon{Chr{x}, SNil{}})), Nat.add(c, w0), Cells.append(a, SCon{Chr{x}, SNil{}}))
  +e3 = Equal.trans(Nat, Nat.add(w0, s), Nat.add(w, s), 1n+p, Equal.cong(Nat, Nat, y => Nat.add(y, s), w0, w, L.Nat.zero_r(w)), L.Nat.add_sub(1n+p, w, le))
  Equal.trans(Nat, Nat.add(Laws.Spec.cells(String.append(a, SCon{Chr{x}, SNil{}})), s), Nat.add(Nat.add(c, w0), s), Nat.add(c, 1n+p), e1,
    Equal.trans(Nat, Nat.add(Nat.add(c, w0), s), Nat.add(c, Nat.add(w0, s)), Nat.add(c, 1n+p), L.Nat.add_assoc(c, w0, s), Equal.cong(Nat, Nat, y => Nat.add(c, y), Nat.add(w0, s), 1n+p, e3)))

def Fit.ok(ok: Bool, +x: U32, +t: String, +p: Nat, +a: String, e: {Nat.is_le(W(x), 1n+p) == ok : Bool}, ih: @w: Nat -> @a2: String -> {Laws.Spec.cells(X.Text.fit.go(t, w, 0n, SCon{' ', a2})) == Nat.add(Laws.Spec.cells(a2), w) : Nat})
  -> {Laws.Spec.cells(X.Text.fit.go(t, Bool.pick(Nat, ok, Nat.sub(1n+p, W(x)), 0n), Bool.pick(Nat, ok, 0n, 1n+p), Bool.pick(String, ok, String.append(SCon{' ', a}, SCon{Chr{x}, SNil{}}), SCon{' ', a}))) == Nat.add(Laws.Spec.cells(a), 1n+p) : Nat}:
  match ok:
    case True{}:
      +a2 = String.append(a, SCon{Chr{x}, SNil{}})
      Equal.trans(Nat, Laws.Spec.cells(X.Text.fit.go(t, Nat.sub(1n+p, W(x)), 0n, SCon{' ', a2})), Nat.add(Laws.Spec.cells(a2), Nat.sub(1n+p, W(x))), Nat.add(Laws.Spec.cells(a), 1n+p), ih(Nat.sub(1n+p, W(x)), a2), Fit.arith(a, x, p, e))
    case False{}:
      Fit.pad(t, 1n+p, a)

def Fit.go0(s: String, +w: Nat, +a: String) -> {Laws.Spec.cells(X.Text.fit.go(s, w, 0n, SCon{' ', a})) == Nat.add(Laws.Spec.cells(a), w) : Nat}:
  match s w:
    case SNil{} _:
      Equal.trans(Nat, Laws.Spec.cells(String.append(a, X.Text.spaces(Nat.add(w, 0n), SNil{}))), Nat.add(Laws.Spec.cells(a), Nat.add(w, 0n)), Nat.add(Laws.Spec.cells(a), w), Fit.tail(a, Nat.add(w, 0n)), Equal.cong(Nat, Nat, y => Nat.add(Laws.Spec.cells(a), y), Nat.add(w, 0n), w, L.Nat.zero_r(w)))
    case SCon{h, +t} 0n:
      Fit.tail(a, 0n)
    case SCon{Chr{+x}, t} 1n++p:
      Fit.ok(Nat.is_le(W(x), 1n+p), x, t, p, a, {==}, w2 => a2 => Fit.go0(t, w2, a2))

# Text.fit gives exactly w cells
def Fit.cells(+s: String, +w: Nat) -> {Laws.Spec.cells(X.Text.fit(s, w)) == w : Nat}:
  Fit.go0(s, w, SNil{})

def Fitted.at(c: Bool, +s: String, +w: Nat, e: {Nat.is_eq(X.Text.cells(s), w) == c : Bool}) -> {Laws.Spec.cells(X.Bool.when(String, c, u => X.Text.fit(s, w), u => s)) == w : Nat}:
  match c:
    case True{}:
      Equal.trans(Nat, Laws.Spec.cells(s), X.Text.cells(s), w, Equal.sym(Nat, X.Text.cells(s), Laws.Spec.cells(s), Cells.eq(s)), L.Nat.eq_true(X.Text.cells(s), w, e))
    case False{}:
      Fit.cells(s, w)

# Text.fitted gives exactly w cells
def Fitted.cells(+s: String, +w: Nat) -> {Laws.Spec.cells(X.Text.fitted(s, w)) == w : Nat}:
  Fitted.at(Nat.is_eq(X.Text.cells(s), w), s, w, {==})

def Cut.ok(ok: Bool, +x: U32, +t: String, +p: Nat, +a: String, e: {Nat.is_le(W(x), 1n+p) == ok : Bool}, ih: @w: Nat -> @a2: String -> L.LE(Laws.Spec.cells(X.Text.cut.go(t, w, SCon{' ', a2})), Nat.add(Laws.Spec.cells(a2), w)))
  -> L.LE(Laws.Spec.cells(X.Text.cut.go(t, Bool.pick(Nat, ok, Nat.sub(1n+p, W(x)), 0n), Bool.pick(String, ok, String.append(SCon{' ', a}, SCon{Chr{x}, SNil{}}), SCon{' ', a}))), Nat.add(Laws.Spec.cells(a), 1n+p)):
  match ok:
    case True{}:
      +a2 = String.append(a, SCon{Chr{x}, SNil{}})
      L.LE.cast_r(Laws.Spec.cells(X.Text.cut.go(t, Nat.sub(1n+p, W(x)), SCon{' ', a2})), Nat.add(Laws.Spec.cells(a2), Nat.sub(1n+p, W(x))), Nat.add(Laws.Spec.cells(a), 1n+p), Fit.arith(a, x, p, e), ih(Nat.sub(1n+p, W(x)), a2))
    case False{}:
      +c = Laws.Spec.cells(a)
      L.Nat.le_trans(Laws.Spec.cells(X.Text.cut.go(t, 0n, SCon{' ', a})), Nat.add(c, 0n), Nat.add(c, 1n+p), ih(0n, a), L.Nat.le_add_mono(c, 0n, 1n+p, L.Nat.le_zero(1n+p)))

def Cut.go(s: String, +w: Nat, +a: String) -> L.LE(Laws.Spec.cells(X.Text.cut.go(s, w, SCon{' ', a})), Nat.add(Laws.Spec.cells(a), w)):
  match s w:
    case SNil{} _:
      L.Nat.le_add(Laws.Spec.cells(a), w)
    case SCon{h, +t} 0n:
      L.Nat.le_add(Laws.Spec.cells(a), 0n)
    case SCon{Chr{+x}, t} 1n++p:
      Cut.ok(Nat.is_le(W(x), 1n+p), x, t, p, a, {==}, w2 => a2 => Cut.go(t, w2, a2))

# Text.cut gives at most w cells
def Cut.cells(+s: String, +w: Nat) -> L.LE(Laws.Spec.cells(X.Text.cut(s, w)), w):
  Cut.go(s, w, SNil{})

def Drop.zero(t: String, -pre: String) -> {X.Text.dropc.go(t, 0n, pre) == String.append(pre, t) : String}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, u}:
      {==}

def Drop.at(b: Bool, +t: String, +p: Nat, ih: @m: Nat -> {Laws.Spec.cells(X.Text.dropc.go(t, m, "")) == Nat.sub(Laws.Spec.cells(t), m) : Nat})
  -> {Laws.Spec.cells(X.Text.dropc.go(t, Bool.pick(Nat, Bool.and(Nat.is_eq(Bool.pick(Nat, b, 2n, 1n), 2n), Nat.is_eq(p, 0n)), 0n, Nat.sub(p, Bool.pick(Nat, Nat.is_eq(Bool.pick(Nat, b, 2n, 1n), 2n), 1n, 0n))), Bool.pick(String, Bool.and(Nat.is_eq(Bool.pick(Nat, b, 2n, 1n), 2n), Nat.is_eq(p, 0n)), " ", ""))) == Nat.sub(Nat.add(Bool.pick(Nat, b, 2n, 1n), Laws.Spec.cells(t)), 1n+p) : Nat}:
  match b p:
    case True{} 0n:
      %Equal.sym(String, X.Text.dropc.go(t, 0n, " "), String.append(" ", t), Drop.zero(t, " ")) : {Laws.Spec.cells(_) == Nat.sub(Nat.add(2n, Laws.Spec.cells(t)), 1n) : Nat}
      {==}
    case True{} 1n++q:
      Equal.trans(Nat, Laws.Spec.cells(X.Text.dropc.go(t, Nat.sub(q, 0n), "")), Nat.sub(Laws.Spec.cells(t), Nat.sub(q, 0n)), Nat.sub(Laws.Spec.cells(t), q), ih(Nat.sub(q, 0n)), Equal.cong(Nat, Nat, y => Nat.sub(Laws.Spec.cells(t), y), Nat.sub(q, 0n), q, L.Nat.sub_zero(q)))
    case False{} _:
      Equal.trans(Nat, Laws.Spec.cells(X.Text.dropc.go(t, Nat.sub(p, 0n), "")), Nat.sub(Laws.Spec.cells(t), Nat.sub(p, 0n)), Nat.sub(Laws.Spec.cells(t), p), ih(Nat.sub(p, 0n)), Equal.cong(Nat, Nat, y => Nat.sub(Laws.Spec.cells(t), y), Nat.sub(p, 0n), p, L.Nat.sub_zero(p)))

def Drop.go(s: String, n: Nat) -> {Laws.Spec.cells(X.Text.dropc.go(s, n, "")) == Nat.sub(Laws.Spec.cells(s), n) : Nat}:
  match s n:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+p:
      {==}
    case SCon{+h, +t} 0n:
      Equal.sym(Nat, Nat.sub(Laws.Spec.cells(SCon{h, t}), 0n), Laws.Spec.cells(SCon{h, t}), L.Nat.sub_zero(Laws.Spec.cells(SCon{h, t})))
    case SCon{Chr{+x}, +t} 1n+p:
      Drop.at(U32.is_eq(x, 129727), t, p, m => Drop.go(t, m))

# Text.dropc drops n cells
def Drop.cells(+s: String, +n: Nat) -> {Laws.Spec.cells(X.Text.dropc(s, n)) == Nat.sub(Laws.Spec.cells(s), n) : Nat}:
  Drop.go(s, n)

# a string of some cells is not empty
def Cells.some(s: String, h: L.LT(0n, Laws.Spec.cells(s))) -> {String.is_empty(s) == False{} : Bool}:
  match s:
    case SNil{}:
      L.Bool.false_true({True{} == False{} : Bool}, h)
    case SCon{c, t}:
      {==}
