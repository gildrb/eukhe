# eukhe.com's Neovim: what the screen of a settled editor shows
# =============================================================
#
# Facts about Vim.frame of any editor s that holds Final(s) (proof/base/
# final.bend): the cursor on the text in normal mode (Screen.on_text),
# the gutter, the text columns. The screen laws (proof/screen/*.bend) put
# them together with the reach of the events (proof/base/reach.bend).

import Base
import ../../vim/types.bend as T
import ../../vim/text.bend as X
import ../../vim/buf.bend as B
import ../../vim/move.bend as M
import ../../vim/view.bend as V
import ../../vim/st.bend as S
import ../../vim/core.bend as C
import ../../vim/screen.bend as R
import ../../vim/vim.bend as Vim
import ../../LAWS.bend as Laws
import ../base.bend as L
import ../base/final.bend as Fi
import ../base/text.bend as Tx

# Logic
# -----

def And3(a: Bool, b: Bool, -c: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}, hc: {c == True{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == True{} : Bool}:
  L.And.intro(a, Bool.and(b, c), ha, L.And.intro(b, c, hb, hc))

def And6(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, -f: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}, hc: {c == True{} : Bool}, hd: {d == True{} : Bool}, he: {e == True{} : Bool}, hf: {f == True{} : Bool})
  -> {Bool.and(a, Bool.and(b, Bool.and(c, Bool.and(d, Bool.and(e, f))))) == True{} : Bool}:
  L.And.intro(a, Bool.and(b, Bool.and(c, Bool.and(d, Bool.and(e, f)))), ha, L.And.intro(b, Bool.and(c, Bool.and(d, Bool.and(e, f))), hb, L.And.intro(c, Bool.and(d, Bool.and(e, f)), hc, L.And.intro(d, Bool.and(e, f), hd, L.And.intro(e, f, he, hf)))))

def And7(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, f: Bool, -g: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}, hc: {c == True{} : Bool}, hd: {d == True{} : Bool}, he: {e == True{} : Bool}, hf: {f == True{} : Bool}, hg: {g == True{} : Bool})
  -> {Bool.and(a, Bool.and(b, Bool.and(c, Bool.and(d, Bool.and(e, Bool.and(f, g)))))) == True{} : Bool}:
  L.And.intro(a, Bool.and(b, Bool.and(c, Bool.and(d, Bool.and(e, Bool.and(f, g))))), ha, And6(b, c, d, e, f, g, hb, hc, hd, he, hf, hg))

# G when m is normal mode, else Unit
def Mode.If(m: T.Mode, G: Type) -> Type:
  match m:
    case T.Normal{}:
      Unit
    case T.Typing{kind, text}:
      G
    case T.Picking{kind, q, its, n, sel, top, pv, levels}:
      G

# a mode that is not normal mode is not: anything follows
def Mode.typing(-G: Type, -k: T.Line, -t: String, e: {T.Typing{k, t} == T.Normal{} : T.Mode}) -> G:
  %Equal.sym(T.Mode, T.Typing{k, t}, T.Normal{}, e) : Mode.If(_, G)
  Unit{}

def Mode.picking(-G: Type, -k: T.Pick, -q: String, -its: List<&2, T.Item>, -n: Nat, -sel: Nat, -top: Nat, -pv: Nat, -levels: List<&2, T.Level>, e: {T.Picking{k, q, its, n, sel, top, pv, levels} == T.Normal{} : T.Mode}) -> G:
  %Equal.sym(T.Mode, T.Picking{k, q, its, n, sel, top, pv, levels}, T.Normal{}, e) : Mode.If(_, G)
  Unit{}

# Nat
# ---

# x <= n - 1 and 1 <= n: x < n
def Nat.le_pred_lt(+x: Nat, +n: Nat, h: L.LE(x, Nat.sub(n, 1n)), h1: L.LE(1n, n)) -> L.LT(x, n):
  L.Nat.le_lt(x, n, L.LE.cast_r(1n+x, Nat.add(Nat.sub(n, 1n), 1n), n, L.Nat.sub_add(n, 1n, h1), L.LE.cast_r(1n+x, 1n+Nat.sub(n, 1n), Nat.add(Nat.sub(n, 1n), 1n), Equal.trans(Nat, 1n+Nat.sub(n, 1n), Nat.add(1n, Nat.sub(n, 1n)), Nat.add(Nat.sub(n, 1n), 1n), {==}, L.Nat.add_comm(1n, Nat.sub(n, 1n))), h)))

def LT.cast_l(-a: Nat, -b: Nat, -c: Nat, e: {a == b : Nat}, h: L.LT(a, c)) -> L.LT(b, c):
  %e : L.LT(_, c)
  h

# c - (c - 1) is 1 when 1 <= c
def Nat.sub_pred(c: Nat, h: L.LE(1n, c)) -> {Nat.sub(c, Nat.sub(c, 1n)) == 1n : Nat}:
  match c:
    case 0n:
      L.Bool.false_true({Nat.sub(0n, Nat.sub(0n, 1n)) == 1n : Nat}, h)
    case 1n++p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, L.Nat.sub_zero(p)) : {Nat.sub(1n+p, _) == 1n : Nat}
      L.Nat.succ_sub(p)

# the line l is within the band of first lines: top <= l, and l - top
# fits the h rows
def Win.top_le(+l: Nat, +so: Nat, +top: Nat, h: L.LE(top, Fi.Fin.lo(l, so))) -> L.LE(top, l):
  L.Nat.le_trans(top, Fi.Fin.lo(l, so), l, h, L.Nat.sub_le(l, Nat.min(so, l)))

def Win.row_le(+l: Nat, +so: Nat, +last: Nat, +h: Nat, +top: Nat, hb: L.LE(Fi.Fin.hi(l, so, last, h), top)) -> L.LE(Nat.sub(l, top), Nat.sub(h, 1n)):
  +a = Nat.min(so, Nat.sub(last, l))
  +x = L.Nat.sub_le_add(Nat.add(l, a), Nat.sub(h, 1n), top, hb)
  +y = L.Nat.le_trans(l, Nat.add(l, a), Nat.add(top, Nat.sub(h, 1n)), L.Nat.le_add(l, a), x)
  L.Nat.le_add_sub(l, top, Nat.sub(h, 1n), L.LE.cast_r(l, Nat.add(top, Nat.sub(h, 1n)), Nat.add(Nat.sub(h, 1n), top), L.Nat.add_comm(top, Nat.sub(h, 1n)), y))

def Win.row_lt(+l: Nat, +so: Nat, +last: Nat, +h: Nat, +top: Nat, hb: L.LE(Fi.Fin.hi(l, so, last, h), top), h1: L.LE(1n, h)) -> L.LT(Nat.sub(l, top), h):
  Nat.le_pred_lt(Nat.sub(l, top), h, Win.row_le(l, so, last, h, top, hb), h1)

# The gutter
# ----------

def Gut.le(+o: T.Opts, +n: Nat, +sign: Bool, +c: Nat) -> L.LE(V.View.gutter(o, n, sign, c), Nat.sub(c, 1n)):
  L.Nat.min_le_r(Nat.add(V.View.signw(sign), V.View.numw(o, n)), Nat.sub(c, 1n))

# the text columns: at least one
def Gut.w1(+c: Nat, +g: Nat, hg: L.LE(g, Nat.sub(c, 1n)), h1: L.LE(1n, c)) -> L.LE(1n, Nat.sub(c, g)):
  L.LE.cast_l(Nat.sub(c, Nat.sub(c, 1n)), 1n, Nat.sub(c, g), Nat.sub_pred(c, h1), L.Nat.sub_anti(c, g, Nat.sub(c, 1n), hg))

# a cell y columns into the text, y < c - g: on screen
def Gut.col_lt(+c: Nat, +g: Nat, +y: Nat, hg: L.LE(g, c), hy: L.LT(y, Nat.sub(c, g))) -> L.LT(Nat.add(g, y), c):
  +a = L.Nat.le_add_mono(g, 1n+y, Nat.sub(c, g), L.Nat.lt_le(y, Nat.sub(c, g), hy))
  +b = L.LE.cast_l(Nat.add(g, 1n+y), 1n+Nat.add(g, y), Nat.add(g, Nat.sub(c, g)), Equal.sym(Nat, 1n+Nat.add(g, y), Nat.add(g, 1n+y), L.Nat.add_succ(g, y)), a)
  L.Nat.le_lt(Nat.add(g, y), c, L.LE.cast_r(1n+Nat.add(g, y), Nat.add(g, Nat.sub(c, g)), c, L.Nat.add_sub(c, g, hg), b))

# Files
# -----

def Files.norm(fs: List<&2, T.Buf>) -> List<&2, T.Buf>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{T.Buf{p, ls}, t}:
      T.Buf{p, B.Lines.some(ls)} <> Files.norm(t)

def Files.some_go(fs: List<&2, T.Buf>, acc: List<&2, T.Buf>) -> {B.Files.some(fs, acc) == List.reverse.go(&2, T.Buf, acc, Files.norm(fs)) : List<&2, T.Buf>}:
  match fs:
    case Nil{}:
      {==}
    case Con{T.Buf{p, ls}, t}:
      Files.some_go(t, T.Buf{p, B.Lines.some(ls)} <> acc)

def Files.some_spec(ls: List<&2, String>) -> {Laws.Spec.some(ls) == B.Lines.some(B.Lines.some(ls)) : List<&2, String>}:
  match ls:
    case Nil{}:
      {==}
    case Con{h, u}:
      {==}

def Files.at_norm(fs: List<&2, T.Buf>, i: Nat) -> {Laws.Spec.file(fs, i) == B.Lines.some(B.Buf.lines(B.Files.at(Files.norm(fs), i))) : List<&2, String>}:
  match fs i:
    case Nil{} _:
      {==}
    case Con{T.Buf{p, ls}, t} 0n:
      Files.some_spec(ls)
    case Con{T.Buf{p, ls}, t} 1n+q:
      Files.at_norm(t, q)

# the lines of file i the editor holds are the spec's (A2)
def Files.spec(+fs: List<&2, T.Buf>, -files: List<&2, T.Buf>, +i: Nat, hf: {files == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> {Laws.Spec.file(fs, i) == B.Lines.some(B.Buf.lines(B.Files.at(files, i))) : List<&2, String>}:
  %Equal.sym(List<&2, T.Buf>, files, B.Files.some(fs, Nil{}), hf) : {Laws.Spec.file(fs, i) == B.Lines.some(B.Buf.lines(B.Files.at(_, i))) : List<&2, String>}
  %Equal.sym(List<&2, T.Buf>, B.Files.some(fs, Nil{}), Files.norm(fs), Files.some_go(fs, Nil{})) : {Laws.Spec.file(fs, i) == B.Lines.some(B.Buf.lines(B.Files.at(_, i))) : List<&2, String>}
  Files.at_norm(fs, i)

def Some.count(xs: List<&2, String>) -> L.LE(1n, Laws.Spec.count(B.Lines.some(xs))):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      L.Nat.le_zero(Laws.Spec.count(t))

# The cursor on the text
# ----------------------

# Spec.on_text over the window's lines ls, the frame's gutter g, row and
# column, the line and column read from them, the character it names
def OnText.goal(+ls: List<&2, String>, +rows: Nat, +cols: Nat, +g: Nat, +row: Nat, +fcol: Nat, +l: Nat, +c: Nat, +ch: String) -> Bool:
  +line = Laws.Spec.line(ls, l)
  Bool.and(Nat.is_lt(row, Nat.sub(rows, 2n)), Bool.and(Nat.is_le(g, fcol), Bool.and(Nat.is_lt(fcol, cols), Bool.and(Nat.is_lt(l, Laws.Spec.count(ls)), Bool.and(Nat.is_le(c, Laws.Spec.last(Laws.Spec.chars(line))), String.eq(ch, Laws.Spec.char(line, c)))))))

# a settled window over ls (the spec's lines sl) in normal mode: the
# cursor on the text
def OnText.parts(+ls: List<&2, String>, +sl: List<&2, String>, +rows: Nat, +cols: Nat, +opts: T.Opts, +onfile: Bool, +line: Nat, +col: Nat, +top: Nat, +left: Nat,
  esl: {sl == ls : List<&2, String>}, hne: L.LE(1n, Laws.Spec.count(ls)), fin: Fi.Final.at(ls, rows, cols, opts, onfile, line, col, top, left))
  -> {OnText.goal(sl, rows, cols, V.View.gutter(opts, B.Lines.len(ls), onfile, cols), Nat.sub(line, top), Nat.add(V.View.gutter(opts, B.Lines.len(ls), onfile, cols), Nat.sub(col, left)), Nat.add(top, Nat.sub(line, top)), Nat.add(left, Nat.sub(Nat.add(V.View.gutter(opts, B.Lines.len(ls), onfile, cols), Nat.sub(col, left)), V.View.gutter(opts, B.Lines.len(ls), onfile, cols))), R.Scr.char(X.Text.at(B.Lines.at(ls, line), col))) == True{} : Bool}:
  (f3, r1) = fin
  (f12, r2) = r1
  (fl, r3) = r2
  (fc, r4) = r3
  (bt, bl) = r4
  (bth, btl) = bt
  (blh, bll) = bl
  +g = V.View.gutter(opts, B.Lines.len(ls), onfile, cols)
  +h = Nat.sub(rows, 2n)
  +w = Nat.sub(cols, g)
  +last = M.Move.last_line(ls)
  +lc = M.Move.last_col(ls, line)
  +y = Nat.sub(col, left)
  +row = Nat.sub(line, top)
  +ch = R.Scr.char(X.Text.at(B.Lines.at(ls, line), col))
  +tl = Win.top_le(line, V.View.so_in(h), top, btl)
  +ll = Win.top_le(col, V.View.so_in(w), left, bll)
  +h1 = L.Nat.sub_mono(3n, rows, 2n, f3)
  +c1 = L.Nat.le_trans(1n, 12n, cols, {==}, f12)
  +gl = Gut.le(opts, B.Lines.len(ls), onfile, cols)
  +gc = L.Nat.le_trans(g, Nat.sub(cols, 1n), cols, gl, L.Nat.sub_le(cols, 1n))
  +w1 = Gut.w1(cols, g, gl, c1)
  +el = Equal.sym(Nat, Nat.add(top, row), line, L.Nat.add_sub(line, top, tl))
  +ec = Equal.trans(Nat, col, Nat.add(left, y), Nat.add(left, Nat.sub(Nat.add(g, y), g)), Equal.sym(Nat, Nat.add(left, y), col, L.Nat.add_sub(col, left, ll)), Equal.cong(Nat, Nat, z => Nat.add(left, z), y, Nat.sub(Nat.add(g, y), g), Equal.sym(Nat, Nat.sub(Nat.add(g, y), g), y, L.Nat.add_sub_l(g, y))))
  %Equal.sym(List<&2, String>, sl, ls, esl) : {OnText.goal(_, rows, cols, g, row, Nat.add(g, y), Nat.add(top, row), Nat.add(left, Nat.sub(Nat.add(g, y), g)), ch) == True{} : Bool}
  %el : {OnText.goal(ls, rows, cols, g, row, Nat.add(g, y), _, Nat.add(left, Nat.sub(Nat.add(g, y), g)), ch) == True{} : Bool}
  %ec : {OnText.goal(ls, rows, cols, g, row, Nat.add(g, y), line, _, ch) == True{} : Bool}
  +p1 = Win.row_lt(line, V.View.so_in(h), last, h, top, bth, h1)
  +p3 = Gut.col_lt(cols, g, y, gc, Win.row_lt(col, V.View.so_in(w), lc, w, left, blh, w1))
  +p4 = Nat.le_pred_lt(line, Laws.Spec.count(ls), L.LE.cast_r(line, last, Nat.sub(Laws.Spec.count(ls), 1n), Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), B.Lines.len(ls), Laws.Spec.count(ls), Tx.Count.eq(ls)), fl), hne)
  +el2 = Equal.trans(Nat, X.Text.len(B.Lines.at(ls, line)), Laws.Spec.chars(B.Lines.at(ls, line)), Laws.Spec.chars(Laws.Spec.line(ls, line)), Tx.Chars.eq(B.Lines.at(ls, line)), Equal.cong(String, Nat, z => Laws.Spec.chars(z), B.Lines.at(ls, line), Laws.Spec.line(ls, line), Tx.Line.eq(ls, line)))
  +p5 = L.LE.cast_r(col, lc, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, line))), Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), X.Text.len(B.Lines.at(ls, line)), Laws.Spec.chars(Laws.Spec.line(ls, line)), el2), fc)
  +ech = Equal.trans(String, ch, Laws.Spec.char(B.Lines.at(ls, line), col), Laws.Spec.char(Laws.Spec.line(ls, line), col), Tx.Char.eq(B.Lines.at(ls, line), col), Equal.cong(String, String, z => Laws.Spec.char(z, col), B.Lines.at(ls, line), Laws.Spec.line(ls, line), Tx.Line.eq(ls, line)))
  +line2 = Laws.Spec.line(ls, line)
  And6(Nat.is_lt(row, h), Nat.is_le(g, Nat.add(g, y)), Nat.is_lt(Nat.add(g, y), cols), Nat.is_lt(line, Laws.Spec.count(ls)), Nat.is_le(col, Laws.Spec.last(Laws.Spec.chars(line2))), String.eq(ch, Laws.Spec.char(line2, col)),
    p1, L.Nat.le_add(g, y), p3, p4, p5, Tx.String.eq_same(ch, Laws.Spec.char(line2, col), ech))

def OnText.G(fs: List<&2, T.Buf>, +s: T.St) -> Type:
  {Laws.Spec.on_text(fs, s, S.St.rows(s), S.St.cols(s)) == True{} : Bool}

def OnText.at(m: T.Mode, tgt: T.Tgt, cur: T.Pos, +fs: List<&2, T.Buf>, +files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +want: T.Want, +top: Nat, +left: Nat, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String,
  fin: Fi.Final(T.St{files, folded, dirs, T.Win{tgt, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, m, count, pend, find, hl, opts, rows, cols, msg, stat}), hf: {files == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hm: {m == T.Normal{} : T.Mode})
  -> OnText.G(fs, T.St{files, folded, dirs, T.Win{tgt, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, m, count, pend, find, hl, opts, rows, cols, msg, stat}):
  match m:
    case T.Normal{}:
      match tgt:
        case T.File{+i}:
          match cur:
            case T.Pos{+line, +col}:
              +raw = B.Buf.lines(B.Files.at(files, i))
              OnText.parts(B.Lines.some(raw), Laws.Spec.file(fs, i), rows, cols, opts, True{}, line, col, top, left, Files.spec(fs, files, i, hf), Some.count(raw), fin)
        case T.Dir{+path}:
          match cur:
            case T.Pos{+line, +col}:
              +raw = Maybe.default(&2, List<&2, String>, C.Listing.find(dirs, path), ["../"])
              OnText.parts(B.Lines.some(raw), B.Lines.some(raw), rows, cols, opts, False{}, line, col, top, left, {==}, Some.count(raw), fin)
    case T.Typing{+k, +t}:
      Mode.typing(OnText.G(fs, T.St{files, folded, dirs, T.Win{tgt, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Typing{k, t}, count, pend, find, hl, opts, rows, cols, msg, stat}), k, t, hm)
    case T.Picking{+k, +q, +its, +n, +sel, +ptop, +pv, +levels}:
      Mode.picking(OnText.G(fs, T.St{files, folded, dirs, T.Win{tgt, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Picking{k, q, its, n, sel, ptop, pv, levels}, count, pend, find, hl, opts, rows, cols, msg, stat}), k, q, its, n, sel, ptop, pv, levels, hm)

# a settled editor in normal mode, on the files the start made of fs: the
# cursor on a character of the window's text (R1)
def Screen.on_text(fs: List<&2, T.Buf>, +s: T.St, fin: Fi.Final(s), hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hm: {S.St.mode(s) == T.Normal{} : T.Mode}) -> OnText.G(fs, s):
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          OnText.at(mode, tgt, cur, fs, files, folded, dirs, want, top, left, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, fin, hf, hm)

# Scrolloff
# ---------

def Pick.succ(c: Bool, -a: Nat, -b: Nat) -> {Bool.pick(Nat, c, 1n+a, 1n+b) == 1n+Bool.pick(Nat, c, a, b) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# the spec's min is Nat.min
def Spec.min_eq(a: Nat, +b: Nat) -> {Laws.Spec.min(a, b) == Nat.min(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n++p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.trans(Nat, Bool.pick(Nat, Nat.is_le(p, q), 1n+p, 1n+q), 1n+Bool.pick(Nat, Nat.is_le(p, q), p, q), 1n+Nat.min(p, q), Pick.succ(Nat.is_le(p, q), p, q), Equal.cong(Nat, Nat, x => 1n+x, Laws.Spec.min(p, q), Nat.min(p, q), Spec.min_eq(p, q)))

# Spec.scrolled over the spec's lines sl, the frame's row and the line
# read from it
def Scrolled.goal(+sl: List<&2, String>, +rows: Nat, +row: Nat, +l: Nat) -> Bool:
  +h = Nat.sub(rows, 2n)
  +so = Laws.Spec.min(8n, Nat.div(Nat.sub(h, 1n), 2n))
  +last = Laws.Spec.last(Laws.Spec.count(sl))
  Bool.and(Nat.is_le(Laws.Spec.min(so, l), row), Nat.is_le(Laws.Spec.min(so, Nat.sub(last, l)), Nat.sub(Nat.sub(h, 1n), row)))

# a settled window over ls (the spec's lines sl): 'scrolloff' both ways
def Scrolled.parts(+ls: List<&2, String>, +sl: List<&2, String>, +rows: Nat, +cols: Nat, +opts: T.Opts, +onfile: Bool, +line: Nat, +col: Nat, +top: Nat, +left: Nat,
  esl: {sl == ls : List<&2, String>}, fin: Fi.Final.at(ls, rows, cols, opts, onfile, line, col, top, left))
  -> {Scrolled.goal(sl, rows, Nat.sub(line, top), Nat.add(top, Nat.sub(line, top))) == True{} : Bool}:
  (f3, r1) = fin
  (f12, r2) = r1
  (fl, r3) = r2
  (fc, r4) = r3
  (bt, bl) = r4
  (bth, btl) = bt
  +h = Nat.sub(rows, 2n)
  +k = Nat.sub(h, 1n)
  +dd = Nat.div(k, 2n)
  +so = V.View.so_in(h)
  +so2 = Laws.Spec.min(8n, dd)
  +last = M.Move.last_line(ls)
  +row = Nat.sub(line, top)
  +m = Nat.min(so, line)
  +a = Nat.min(so, Nat.sub(last, line))
  +x1 = L.LE.cast_r(Nat.add(top, m), Nat.add(Nat.sub(line, m), m), line, L.Nat.sub_add(line, m, L.Nat.min_le_r(so, line)), L.Nat.le_addr(top, Nat.sub(line, m), m, btl))
  +tl = L.Nat.le_trans(top, Nat.add(top, m), line, L.Nat.le_add(top, m), x1)
  +el = Equal.sym(Nat, Nat.add(top, row), line, L.Nat.add_sub(line, top, tl))
  %Equal.sym(List<&2, String>, sl, ls, esl) : {Scrolled.goal(_, rows, row, Nat.add(top, row)) == True{} : Bool}
  %el : {Scrolled.goal(ls, rows, row, _) == True{} : Bool}
  +eso = Spec.min_eq(8n, dd)
  +p1 = L.Nat.le_sub_of_add(m, top, line, L.LE.cast_l(Nat.add(top, m), Nat.add(m, top), line, L.Nat.add_comm(top, m), x1))
  +e1 = Equal.trans(Nat, Laws.Spec.min(so2, line), Nat.min(so2, line), m, Spec.min_eq(so2, line), Equal.cong(Nat, Nat, z => Nat.min(z, line), so2, so, eso))
  +q1 = L.LE.cast_l(m, Laws.Spec.min(so2, line), row, Equal.sym(Nat, Laws.Spec.min(so2, line), m, e1), p1)
  +y1 = L.Nat.sub_le_add(Nat.add(line, a), k, top, bth)
  +y2 = L.LE.cast_l(Nat.add(line, a), Nat.add(Nat.add(top, row), a), Nat.add(top, k), Equal.cong(Nat, Nat, z => Nat.add(z, a), line, Nat.add(top, row), el), y1)
  +y3 = L.LE.cast_l(Nat.add(Nat.add(top, row), a), Nat.add(top, Nat.add(row, a)), Nat.add(top, k), L.Nat.add_assoc(top, row, a), y2)
  +y4 = L.Nat.le_add_cancel(top, Nat.add(row, a), k, y3)
  +p2 = L.Nat.le_sub_of_add(a, row, k, L.LE.cast_l(Nat.add(row, a), Nat.add(a, row), k, L.Nat.add_comm(row, a), y4))
  +x = Nat.sub(Laws.Spec.last(Laws.Spec.count(ls)), line)
  +ex = Equal.cong(Nat, Nat, z => Nat.sub(Nat.sub(z, 1n), line), Laws.Spec.count(ls), B.Lines.len(ls), Equal.sym(Nat, B.Lines.len(ls), Laws.Spec.count(ls), Tx.Count.eq(ls)))
  +e2 = Equal.trans(Nat, Laws.Spec.min(so2, x), Nat.min(so2, x), a, Spec.min_eq(so2, x), Equal.trans(Nat, Nat.min(so2, x), Nat.min(so, x), a, Equal.cong(Nat, Nat, z => Nat.min(z, x), so2, so, eso), Equal.cong(Nat, Nat, z => Nat.min(so, z), x, Nat.sub(last, line), ex)))
  +q2 = L.LE.cast_l(a, Laws.Spec.min(so2, x), Nat.sub(k, row), Equal.sym(Nat, Laws.Spec.min(so2, x), a, e2), p2)
  L.And.intro(Nat.is_le(Laws.Spec.min(so2, line), row), Nat.is_le(Laws.Spec.min(so2, x), Nat.sub(k, row)), q1, q2)

def Scrolled.G(fs: List<&2, T.Buf>, +s: T.St) -> Type:
  {Laws.Spec.scrolled(fs, s, S.St.rows(s)) == True{} : Bool}

def Scrolled.at(m: T.Mode, tgt: T.Tgt, cur: T.Pos, +fs: List<&2, T.Buf>, +files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +want: T.Want, +top: Nat, +left: Nat, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String,
  fin: Fi.Final(T.St{files, folded, dirs, T.Win{tgt, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, m, count, pend, find, hl, opts, rows, cols, msg, stat}), hf: {files == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hm: {m == T.Normal{} : T.Mode})
  -> Scrolled.G(fs, T.St{files, folded, dirs, T.Win{tgt, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, m, count, pend, find, hl, opts, rows, cols, msg, stat}):
  match m:
    case T.Normal{}:
      match tgt:
        case T.File{+i}:
          match cur:
            case T.Pos{+line, +col}:
              +raw = B.Buf.lines(B.Files.at(files, i))
              Scrolled.parts(B.Lines.some(raw), Laws.Spec.file(fs, i), rows, cols, opts, True{}, line, col, top, left, Files.spec(fs, files, i, hf), fin)
        case T.Dir{+path}:
          match cur:
            case T.Pos{+line, +col}:
              +raw = Maybe.default(&2, List<&2, String>, C.Listing.find(dirs, path), ["../"])
              Scrolled.parts(B.Lines.some(raw), B.Lines.some(raw), rows, cols, opts, False{}, line, col, top, left, {==}, fin)
    case T.Typing{+k, +t}:
      Mode.typing(Scrolled.G(fs, T.St{files, folded, dirs, T.Win{tgt, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Typing{k, t}, count, pend, find, hl, opts, rows, cols, msg, stat}), k, t, hm)
    case T.Picking{+k, +q, +its, +n, +sel, +ptop, +pv, +levels}:
      Mode.picking(Scrolled.G(fs, T.St{files, folded, dirs, T.Win{tgt, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Picking{k, q, its, n, sel, ptop, pv, levels}, count, pend, find, hl, opts, rows, cols, msg, stat}), k, q, its, n, sel, ptop, pv, levels, hm)

# a settled editor in normal mode, on the files the start made of fs:
# 'scrolloff' holds (R3)
def Screen.scrolled(fs: List<&2, T.Buf>, +s: T.St, fin: Fi.Final(s), hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hm: {S.St.mode(s) == T.Normal{} : T.Mode}) -> Scrolled.G(fs, s):
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          Scrolled.at(mode, tgt, cur, fs, files, folded, dirs, want, top, left, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, fin, hf, hm)
