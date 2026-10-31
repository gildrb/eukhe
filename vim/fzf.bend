# eukhe.com's Neovim: fzf-lua
# ===========================
#
# ibhagwan/fzf-lua as Gil's config opens it: buffers (<leader>fb) and the
# current buffer's lines (<leader>/), in a rounded float 84% x 86% of the
# screen, fzf's list reversed (prompt on top, `--layout reverse`) with the
# count inline right, the builtin preview right of it on wide screens and
# below it on narrow ones (layout flex). Sizes from fzf-lua/win.lua;
# matching and the line's scrolling from fzf's algo.go and terminal.go.

import Base
import ./types.bend as T
import ./text.bend as X
import ./buf.bend as B
import ./box.bend as P

# Geometry
# --------

# the float: its first row and column, its size, whether the preview is
# right of the list (else below), the list window's inner columns and
# rows, the preview's inner columns and rows
type ZGeo is Data:
  ZGeo{row: Nat, col: Nat, w: Nat, h: Nat, side: Bool, mw: Nat, mh: Nat, pw: Nat, ph: Nat}

# winopts height .86, width .84, row and col .5; the preview right:60%
# when the float is wider than 100 columns (flip_columns), else down:45%
def Fzf.geo(+r: Nat, +c: Nat) -> ZGeo:
  +w = Nat.div(Nat.mul(c, 84n), 100n)
  +maxh = Nat.sub(r, 1n)
  +h = Nat.div(Nat.mul(maxh, 86n), 100n)
  +row = Nat.min(Nat.div(Nat.sub(r, h), 2n), Nat.sub(maxh, h))
  +col = Nat.div(Nat.sub(c, w), 2n)
  +side = Nat.is_gt(w, 100n)
  +pws = Nat.sub(Nat.div(Nat.mul(Nat.sub(w, 3n), 6n), 10n), 1n)
  +phs = Nat.sub(Nat.div(Nat.mul(Nat.sub(h, 3n), 45n), 100n), 1n)
  ZGeo{row, col, w, h, side, Bool.pick(Nat, side, Nat.sub(Nat.sub(w, 4n), pws), Nat.sub(w, 2n)), Bool.pick(Nat, side, Nat.sub(h, 2n), Nat.sub(Nat.sub(h, 4n), phs)), Bool.pick(Nat, side, pws, Nat.sub(w, 2n)), Bool.pick(Nat, side, Nat.sub(h, 2n), phs)}

# the list's rows under the prompt and its separator, less the header's
def ZGeo.rows(g: ZGeo, +headers: Nat) -> Nat:
  match g:
    case ZGeo{row, col, w, h, side, mw, mh, pw, ph}:
      Nat.sub(Nat.sub(mh, 2n), headers)

# Matching (fzf's v1 algorithm, scheme default)
# ---------------------------------------------

# fzf's class of a character: 0 white, 1 non-word, 2 delimiter, 3 lower,
# 4 upper, 5 other letter, 6 digit
def Zc.cls(c: Char) -> Nat:
  match c:
    case Chr{+x}:
      +white = Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 9), U32.is_eq(x, 160)))
      +delim = Bool.or(U32.is_eq(x, 47), Bool.or(U32.is_eq(x, 44), Bool.or(U32.is_eq(x, 58), Bool.or(U32.is_eq(x, 59), U32.is_eq(x, 124)))))
      +lower = Bool.and(U32.is_ge(x, 97), U32.is_le(x, 122))
      +upper = Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90))
      +digit = Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))
      +letter = Bool.and(U32.is_ge(x, 128), Nat.is_eq(X.Char.cls(Chr{x}, False{}), 2n))
      Bool.pick(Nat, white, 0n, Bool.pick(Nat, delim, 2n, Bool.pick(Nat, lower, 3n, Bool.pick(Nat, upper, 4n, Bool.pick(Nat, digit, 6n, Bool.pick(Nat, letter, 5n, 1n))))))

# the bonus of a character of class k after one of class p
def Zc.bonus(+p: Nat, +k: Nat) -> Nat:
  +word = Nat.is_gt(k, 1n)
  +boundary = Bool.pick(Nat, Nat.is_eq(p, 0n), 10n, Bool.pick(Nat, Nat.is_eq(p, 2n), 9n, Bool.pick(Nat, Nat.is_eq(p, 1n), 8n, 0n)))
  +camel = Bool.or(Bool.and(Nat.is_eq(p, 3n), Nat.is_eq(k, 4n)), Bool.and(Nat.is_ne(p, 6n), Nat.is_eq(k, 6n)))
  +own = Bool.pick(Nat, Bool.or(Nat.is_eq(k, 1n), Nat.is_eq(k, 2n)), 8n, Bool.pick(Nat, Nat.is_eq(k, 0n), 10n, 0n))
  Bool.pick(Nat, Bool.and(word, Nat.is_gt(boundary, 0n)), boundary, Bool.pick(Nat, camel, 7n, own))

# a character as matched: folded unless the query has a capital
def Zc.fold(+c: Char, +fold: Bool) -> Char:
  Bool.pick(Char, fold, X.Char.fold(c), c)

# forward: the index one past where q's characters first all appear in
# order in s
def Zm.fwd(s: String, q: String, +fold: Bool, +i: Nat) -> Maybe<&2, Nat>:
  match s q:
    case _ SNil{}:
      Some{i}
    case SNil{} SCon{y, yt}:
      None{}
    case SCon{x, +xt} SCon{+y, +yt}:
      X.Bool.when(Maybe<&2, Nat>, Char.is_eq(Zc.fold(x, fold), y), u => Zm.fwd(xt, SCon{y, yt}, fold, 1n+i), u => Zm.fwd(xt, yt, fold, 1n+i))

# backward from the end e: the index where the last match of q (reversed:
# rq) starts
def Zm.back(rs: String, rq: String, +fold: Bool, +i: Nat) -> Nat:
  match rs rq:
    case _ SNil{}:
      i
    case SNil{} SCon{y, yt}:
      i
    case SCon{x, +xt} SCon{+y, +yt}:
      X.Bool.when(Nat, Char.is_eq(Zc.fold(x, fold), y), u => Zm.back(xt, SCon{y, yt}, fold, Nat.sub(i, 1n)), u => Zm.back(xt, yt, fold, Nat.sub(i, 1n)))

# a match: its score and the columns it takes
type Zhit is Data:
  Zhit{score: Nat, cols: List<&2, Nat>}

# fzf's score of s from its start (prev: the class before it), matching
# q greedily: 16 a character, bonuses at word boundaries, doubled on the
# first character, consecutive runs keep their first bonus, gaps cost 3
# then 1 (the score kept above 0 here: fzf's own never drops below it for
# a match)
def Zm.score(s: String, q: String, +fold: Bool, +prev: Nat, +i: Nat, +gap: Bool, +run: Nat, +first: Nat, +sc: Nat, +lost: Nat, +acc: List<&2, Nat>) -> Zhit:
  match s q:
    case _ SNil{}:
      Zhit{Nat.sub(sc, lost), List.reverse(&2, Nat, acc)}
    case SNil{} SCon{y, yt}:
      Zhit{Nat.sub(sc, lost), List.reverse(&2, Nat, acc)}
    case SCon{+x, +xt} SCon{+y, +yt}:
      +k = Zc.cls(x)
      +hit = Char.is_eq(Zc.fold(x, fold), y)
      +b = Zc.bonus(prev, k)
      +first2 = Bool.pick(Nat, Nat.is_eq(run, 0n), b, Bool.pick(Nat, Bool.and(Nat.is_ge(b, 8n), Nat.is_gt(b, first)), b, first))
      +b2 = Bool.pick(Nat, Nat.is_eq(run, 0n), b, Nat.max(b, Nat.max(first2, 4n)))
      +add = Nat.add(16n, Bool.pick(Nat, List.is_empty(&2, Nat, acc), Nat.mul(b2, 2n), b2))
      X.Bool.when(Zhit, hit, u => Zm.score(xt, SCon{y, yt}, fold, k, 1n+i, True{}, 0n, 0n, sc, Nat.add(lost, Bool.pick(Nat, gap, 1n, 3n)), acc), u => Zm.score(xt, yt, fold, k, 1n+i, False{}, 1n+run, first2, Nat.add(sc, add), lost, i <> acc))

def Zm.cls_of(m: Maybe<&2, Char>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{c}:
      Zc.cls(c)

def Zm.prev(s: String, +at: Nat) -> Nat:
  match at:
    case 0n:
      0n
    case 1n+p:
      Zm.cls_of(X.Text.at(s, p))

def Zm.best(+s: String, +q: String, +fold: Bool, +e: Nat) -> Zhit:
  +start = Zm.back(String.reverse(X.Text.take(s, e)), String.reverse(q), fold, e)
  Zm.score(X.Text.drop(s, start), q, fold, Zm.prev(s, start), start, False{}, 0n, 0n, 0n, 0n, Nil{})

def Zm.at(+s: String, +q: String, +fold: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, Zhit>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Some{Zm.best(s, q, fold, e)}

# fzf's match of query q in s (smart case): its score and columns
def Zm.find(+s: String, +q: String) -> Maybe<&2, Zhit>:
  +fold = Bool.not(X.Text.has_upper(q))
  +fq = Bool.pick(String, fold, X.Text.fold(q), q)
  Zm.at(s, fq, fold, Zm.fwd(s, fq, fold, 0n))

# whether every character of q is in s (a quick test before matching)
def Zm.has(+s: String, q: String) -> Bool:
  match q:
    case SNil{}:
      True{}
    case SCon{y, yt}:
      Bool.and(String.contains(s, SCon{y, SNil{}}), Zm.has(s, yt))

# Items
# -----

type Zs is Data:
  Zs{score: Nat, item: T.Item}

def Zs.le(a: Zs, b: Zs) -> Bool:
  match a b:
    case Zs{x, i} Zs{y, j}:
      Nat.is_ge(x, y)

def Zs.items(xs: List<&2, Zs>, +acc: List<&2, T.Item>) -> List<&2, T.Item>:
  match xs:
    case Nil{}:
      List.reverse(&2, T.Item, acc)
    case Con{Zs{x, i}, t}:
      Zs.items(t, i <> acc)

# items sorted by score, ties in their order (--tiebreak index)
def Zs.sort(xs: List<&2, Zs>) -> List<&2, T.Item>:
  Zs.items(List.sort(~Zs, ~Zs.le, xs), Nil{})

def Zl.hit(+i: Nat, +l: Nat, +line: String, m: Maybe<&2, Zhit>, +acc: List<&2, Zs>) -> List<&2, Zs>:
  match m:
    case None{}:
      acc
    case Some{Zhit{score, cols}}:
      Zs{score, T.Item{T.File{i}, T.Pos{l, 0n}, line, cols}} <> acc

def Zl.go(ls: List<&2, String>, fl: List<&2, String>, +i: Nat, +l: Nat, +q: String, +fq: String, +fold: Bool, +acc: List<&2, Zs>) -> List<&2, Zs>:
  match ls fl:
    case Nil{} _:
      List.reverse(&2, Zs, acc)
    case _ Nil{}:
      List.reverse(&2, Zs, acc)
    case Con{+h, ht} Con{+f, ft}:
      +m = X.Bool.when(Maybe<&2, Zhit>, Zm.has(Bool.pick(String, fold, f, h), fq), u => None{}, u => Zm.find(h, q))
      Zl.go(ht, ft, i, 1n+l, q, fq, fold, Zl.hit(i, l, h, m, acc))

def Zl.all(ls: List<&2, String>, +i: Nat, +l: Nat, +acc: List<&2, T.Item>) -> List<&2, T.Item>:
  match ls:
    case Nil{}:
      List.reverse(&2, T.Item, acc)
    case Con{h, t}:
      Zl.all(t, i, 1n+l, T.Item{T.File{i}, T.Pos{l, 0n}, h, Nil{}} <> acc)

# blines: the lines of file i (fl: in lower case) matching q, best first
def Fzf.lines(+ls: List<&2, String>, +fl: List<&2, String>, +i: Nat, +q: String) -> List<&2, T.Item>:
  +fold = Bool.not(X.Text.has_upper(q))
  +fq = Bool.pick(String, fold, X.Text.fold(q), q)
  Bool.pick(List<&2, T.Item>, String.is_empty(q), Zl.all(ls, i, 0n, Nil{}), Zs.sort(Zl.go(ls, fl, i, 0n, q, fq, fold, Nil{})))

# the number of file i's buffer (the order files were first opened)
def Zb.no(bs: List<&2, Nat>, +i: Nat, +n: Nat) -> Nat:
  match bs:
    case Nil{}:
      n
    case Con{b, t}:
      X.Bool.when(Nat, Nat.is_eq(b, i), u => Zb.no(t, i, 1n+n), u => n)

def Zb.bufno(+bs: List<&2, Nat>, +i: Nat) -> Nat:
  1n+Zb.no(bs, i, 0n)

# fzf-lua's blank (utils.nbsp): an en space, U+2002
def Zb.en() -> String:
  " "

# a buffer's entry as fzf-lua's buffers lists it: "[n]", its flags
# (% current, # alternate; a shown, h hidden), its path and line
def Zb.entry(+no: Nat, +maxno: Nat, +flag: String, +shown: Bool, +path: String, +line: Nat) -> String:
  X.Text.leftpad("[" ++ Nat.show(no) ++ "]", Nat.add(3n, X.Text.digits(maxno))) ++ Zb.en() ++ flag ++ Bool.pick(String, shown, "a", "h") ++ "  " ++ Zb.en() ++ Zb.en() ++ path ++ ":" ++ Nat.show(line)

def Zb.line(p: T.Pos) -> Nat:
  match p:
    case T.Pos{line, col}:
      line

def Zb.go(os: List<&2, Nat>, +fs: List<&2, T.Buf>, +bs: List<&2, Nat>, +marks: List<&2, T.Pos>, +cur: Nat, +curpos: T.Pos, +k: Nat, +acc: List<&2, T.Item>) -> List<&2, T.Item>:
  match os:
    case Nil{}:
      List.reverse(&2, T.Item, acc)
    case Con{+i, t}:
      +here = Nat.is_eq(cur, 1n+i)
      +pos = Bool.pick(T.Pos, here, curpos, Maybe.default(&2, T.Pos, List.get(&2, T.Pos, marks, i), T.Pos{0n, 0n}))
      +flag = Bool.pick(String, here, "%", Bool.pick(String, Nat.is_eq(k, Bool.pick(Nat, Nat.is_eq(cur, 0n), 0n, 1n)), "#", Zb.en()))
      +text = Zb.entry(Zb.bufno(bs, i), List.length(&2, Nat, bs), flag, here, B.Buf.path(B.Files.at(fs, i)), 1n+Zb.line(pos))
      Zb.go(t, fs, bs, marks, cur, curpos, 1n+k, T.Item{T.File{i}, pos, text, Nil{}} <> acc)

# the buffers, most recent first: the current one (cur: its file from
# 1; 0 in Oil, whose listing is no buffer) heads the list
def Fzf.buffers(+os: List<&2, Nat>, +fs: List<&2, T.Buf>, +bs: List<&2, Nat>, +marks: List<&2, T.Pos>, +cur: Nat, +curpos: T.Pos) -> List<&2, T.Item>:
  Zb.go(os, fs, bs, marks, cur, curpos, 0n, Nil{})

def Zb.hit(tgt: T.Tgt, pos: T.Pos, +text: String, m: Maybe<&2, Zhit>, +acc: List<&2, Zs>) -> List<&2, Zs>:
  match m:
    case None{}:
      acc
    case Some{Zhit{score, cols}}:
      Zs{score, T.Item{tgt, pos, text, cols}} <> acc

def Zb.hits(its: List<&2, T.Item>, +q: String, +acc: List<&2, Zs>) -> List<&2, Zs>:
  match its:
    case Nil{}:
      List.reverse(&2, Zs, acc)
    case Con{T.Item{tgt, pos, +text, h}, t}:
      Zb.hits(t, q, Zb.hit(tgt, pos, text, Zm.find(text, q), acc))

# the buffers but the header matching q, best first
def Fzf.filter(+its: List<&2, T.Item>, +q: String) -> List<&2, T.Item>:
  Bool.pick(List<&2, T.Item>, String.is_empty(q), its, Zs.sort(Zb.hits(its, q, Nil{})))

# Drawing
# -------

# a row's text as fzf shows it in w cells, and the cells of its matches
type Zrow is Data:
  Zrow{text: String, cols: List<&2, Nat>}

def Zd.lim(cs: List<&2, Nat>, +lim: Nat, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      List.reverse(&2, Nat, acc)
    case Con{+c, t}:
      Zd.lim(t, lim, Bool.pick(List<&2, Nat>, Nat.is_lt(c, lim), c <> acc, acc))

def Zd.move(cs: List<&2, Nat>, +d: Nat, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      List.reverse(&2, Nat, acc)
    case Con{+c, t}:
      Zd.move(t, d, Bool.pick(List<&2, Nat>, Nat.is_ge(c, d), Nat.add(2n, Nat.sub(c, d)) <> acc, acc))

def Zd.left(+t2: String, cols: List<&2, Nat>, +w: Nat) -> Zrow:
  +d = Nat.sub(X.Text.cells(t2), Nat.sub(w, 2n))
  Zrow{"··" ++ X.Text.dropc(t2, d), Zd.move(cols, d, Nil{})}

# fzf's hscroll: a text wider than w cells is cut with "··" at the end;
# when its last match would be cut, it scrolls left (10 cells past the
# match kept, "··" at both ends)
def Zd.fit(+text: String, +cols: List<&2, Nat>, +w: Nat) -> Zrow:
  +n = X.Text.cells(text)
  +last = Maybe.default(&2, Nat, List.last(&2, Nat, cols), 0n)
  +maxe = Bool.pick(Nat, List.is_empty(&2, Nat, cols), 0n, Nat.min(n, Nat.add(1n+last, Nat.min(Nat.sub(Nat.div(w, 2n), 2n), 10n))))
  +head = Nat.is_gt(maxe, Nat.sub(w, 2n))
  +right = Nat.is_gt(Nat.sub(n, maxe), 2n)
  X.Bool.when(Zrow, Nat.is_le(n, w), u => X.Bool.when(Zrow, head, u => Zrow{X.Text.cut(text, Nat.sub(w, 2n)) ++ "··", Zd.lim(cols, Nat.sub(w, 2n), Nil{})}, u => Zd.left(Bool.pick(String, right, X.Text.take(text, maxe) ++ "··", text), cols, w)), u => Zrow{text, cols})

def Zd.shift(cs: List<&2, Nat>, +by: Nat, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      List.reverse(&2, Nat, acc)
    case Con{c, t}:
      Zd.shift(t, by, Nat.add(c, by) <> acc)

# tabs as one blank (fzf --tabstop 1)
def Zd.tabs(s: String, acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{'\t', t}:
      Zd.tabs(t, SCon{' ', acc})
    case SCon{h, t}:
      Zd.tabs(t, SCon{h, acc})

# an item's text as the list shows it: blines put the line's number
# before it ("%5d", then fzf-lua's U+00A0 and a tab, 1 cell at tabstop 1)
def Zd.text(+lines: Bool, it: T.Item) -> Zrow:
  match it:
    case T.Item{tgt, T.Pos{l, c}, +text, +hits}:
      X.Bool.when(Zrow, lines, u => Zrow{text, hits}, u => Zrow{X.Text.right(Nat.show(1n+l), 5n) ++ Bool.pick(String, String.is_empty(text), "", "\u{a0} " ++ Zd.tabs(text, SNil{})), Zd.shift(hits, 7n, Nil{})})

def Zrow.text(r: Zrow) -> String:
  match r:
    case Zrow{text, cols}:
      text

def Zrow.cols(r: Zrow) -> List<&2, Nat>:
  match r:
    case Zrow{text, cols}:
      cols

def Zd.fit_row(r: Zrow, +w: Nat) -> Zrow:
  match r:
    case Zrow{+text, +cols}:
      Zd.fit(text, cols, w)

# the list's rows: n rows of items from the first shown (k: its number
# from 0), item sel (from 1) selected, the scrollbar on rows bs to
# bs + bl; marks from row row of the list window
def Zd.items(n: Nat, its: List<&2, T.Item>, +lines: Bool, +w: Nat, +sel: Nat, +k: Nat, +bs: Nat, +bl: Nat, +row: Nat, +acc: List<&2, String>, +ms: List<&2, T.Mark>) -> (List<&2, String> & List<&2, T.Mark>):
  match n its:
    case 0n _:
      (List.reverse(&2, String, acc), ms)
    case 1n+p Nil{}:
      Zd.items(p, Nil{}, lines, w, sel, 1n+k, bs, bl, 1n+row, X.Text.spaces(w, SNil{}) <> acc, ms)
    case 1n+p Con{it, t}:
      +r = Zd.fit_row(Zd.text(lines, it), Nat.sub(w, 3n))
      +bar = Bool.pick(String, Bool.and(Nat.is_ge(k, bs), Nat.is_lt(k, Nat.add(bs, bl))), "│", " ")
      +line = "▌ " ++ X.Text.fit(Zrow.text(r), Nat.sub(w, 3n)) ++ bar
      +m1 = Bool.pick(List<&2, T.Mark>, Nat.is_eq(sel, 1n+k), T.Mark{row, 0n, w, T.Sel{}} <> ms, ms)
      +m2 = Bool.pick(List<&2, T.Mark>, lines, T.Mark{row, 2n, 5n, T.Number{}} <> m1, m1)
      Zd.items(p, t, lines, w, sel, 1n+k, bs, bl, 1n+row, line <> acc, P.Marks.cols(Zrow.cols(r), row, 2n, Nat.sub(w, 3n), m2))

# the count inline right of the prompt: matched/total (selected)
def Zd.info(+n: Nat, +total: Nat) -> String:
  Nat.show(n) ++ "/" ++ Nat.show(total) ++ " (0)"

def Zd.headers(hs: List<&2, String>, +w: Nat, +acc: List<&2, String>) -> List<&2, String>:
  match hs:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{h, t}:
      Zd.headers(t, w, X.Text.fit("  " ++ h, w) <> acc)

# fzf's scrollbar over rows list rows for n items, the first shown top:
# its first row and its rows (0: none)
def Zd.bar(+rows: Nat, +n: Nat, +top: Nat) -> (Nat & Nat):
  +bl = Nat.max(1n, Nat.div(Nat.mul(rows, rows), Nat.max(n, 1n)))
  +span = Nat.sub(n, rows)
  +bs = Nat.min(Nat.sub(rows, bl), Nat.div(Nat.add(Nat.mul(Nat.mul(2n, Nat.sub(rows, bl)), top), span), Nat.max(Nat.mul(2n, span), 1n)))
  Bool.pick((Nat & Nat), Nat.is_gt(n, rows), (bs, bl), (0n, 0n))

def Zd.main.rows(+mw: Nat, +prompt: String, +hs: List<&2, String>, +pre: List<&2, T.Mark>, ir: (List<&2, String> & List<&2, T.Mark>)) -> (List<&2, String> & List<&2, T.Mark>):
  (irows, imarks) = ir
  (prompt <> (X.Text.rep('─', Nat.sub(mw, 1n)) ++ " ") <> List.append(&2, String, hs, irows), List.append(&2, T.Mark, pre, imarks))

def Zd.main.bar(+lines: Bool, +mw: Nat, +its: List<&2, T.Item>, +sel: Nat, +top: Nat, +rows: Nat, +hn: Nat, b: (Nat & Nat)) -> (List<&2, String> & List<&2, T.Mark>):
  (bs, bl) = b
  Zd.items(rows, List.drop(&2, T.Item, its, top), lines, mw, 1n+sel, top, Nat.add(top, bs), bl, Nat.add(2n, hn), Nil{}, Nil{})

# the list window's rows (mw cells) and marks: the prompt and count, the
# separator, the header, the items
def Zd.main(+lines: Bool, +q: String, +hs: List<&2, String>, +its: List<&2, T.Item>, +total: Nat, +sel: Nat, +top: Nat, +mw: Nat, +mh: Nat) -> (List<&2, String> & List<&2, T.Mark>):
  +n = List.length(&2, T.Item, its)
  +info = Zd.info(n, total)
  +at = Nat.sub(Nat.sub(mw, 1n), X.Text.cells(info))
  +prompt = X.Text.over(X.Text.fit("> " ++ q, mw), at, info)
  +hn = List.length(&2, String, hs)
  +rows = Nat.sub(Nat.sub(mh, 2n), hn)
  +pre = {[T.Mark{0n, 0n, 1n, T.Prompt{}}, T.Mark{0n, at, X.Text.cells(info), T.Count{}}, T.Mark{1n, 0n, Nat.sub(mw, 1n), T.Border{}}, T.Mark{2n, 0n, Bool.pick(Nat, Nat.is_eq(hn, 0n), 0n, mw), T.Dim{}}] : List<&2, T.Mark>}
  Zd.main.rows(mw, prompt, Zd.headers(hs, mw, Nil{}), pre, Zd.main.bar(lines, mw, its, sel, top, rows, hn, Zd.bar(rows, n, top)))

# the preview: its title, its pane, the scrollbar thumb on its right
# border (first row, rows)
type ZPre is Data:
  ZPre{title: String, pane: P.Pane, ts: Nat, tl: Nat}

def Zd.pre(+fs: List<&2, T.Buf>, +bs: List<&2, Nat>, m: Maybe<&2, T.Item>, +pw: Nat, +ph: Nat) -> ZPre:
  match m:
    case None{}:
      ZPre{"", P.Pane{Nil{}, ph, pw, 0n, 1n, False{}, 0n}, 0n, 0n}
    case Some{T.Item{T.File{+i}, T.Pos{+l, c}, text, hits}}:
      +b = B.Files.at(fs, i)
      +ls = B.Buf.lines(b)
      +lc = B.Lines.len(ls)
      +top = P.Pane.zz(l, ph)
      +tl = Nat.min(ph, Nat.div(Nat.add(Nat.mul(ph, ph), Nat.sub(lc, 1n)), Nat.max(lc, 1n)))
      +ts = Nat.min(Nat.sub(ph, tl), Nat.div(Nat.mul(ph, 1n+top), Nat.max(lc, 1n)))
      +name = X.Text.drop(B.Buf.path(b), X.Text.len(B.Path.dir(B.Buf.path(b))))
      ZPre{" buf " ++ Nat.show(Zb.bufno(bs, i)) ++ ": " ++ name ++ " ", P.Pane{B.Lines.drop(ls, top), ph, pw, P.Pane.numw(lc), 1n+top, False{}, Nat.sub(1n+l, top)}, ts, Bool.pick(Nat, Nat.is_lt(tl, lc), tl, 0n)}
    case Some{T.Item{T.Dir{p}, pos, text, hits}}:
      ZPre{"", P.Pane{Nil{}, ph, pw, 0n, 1n, False{}, 0n}, 0n, 0n}

# the preview's rows in their border: the right one the thumb on rows ts
# to ts + tl
def Zd.prows(xs: List<&2, String>, +l: String, +k: Nat, +ts: Nat, +tl: Nat, +acc: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{x, t}:
      +thumb = Bool.and(Nat.is_ge(k, ts), Nat.is_lt(k, Nat.add(ts, tl)))
      Zd.prows(t, l, 1n+k, ts, tl, (l ++ x ++ Bool.pick(String, thumb, " ", "│")) <> acc)

def Zd.thumbs(n: Nat, +row: Nat, +col: Nat, +acc: List<&2, T.Mark>) -> List<&2, T.Mark>:
  match n:
    case 0n:
      acc
    case 1n+p:
      Zd.thumbs(p, 1n+row, col, T.Mark{row, col, 1n, T.Thumb{}} <> acc)

def Zd.boxed(xs: List<&2, String>, +acc: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{x, t}:
      Zd.boxed(t, ("│" ++ x ++ "│") <> acc)

def Zd.join(xs: List<&2, String>, ys: List<&2, String>, +acc: List<&2, String>) -> List<&2, String>:
  match xs ys:
    case Nil{} _:
      List.reverse(&2, String, acc)
    case _ Nil{}:
      List.reverse(&2, String, acc)
    case Con{x, xt} Con{y, yt}:
      Zd.join(xt, yt, ("│" ++ x ++ "│" ++ y) <> acc)

def Zd.titled(+title: String, +row: Nat, +col: Nat, +w: Nat, +acc: List<&2, T.Mark>) -> List<&2, T.Mark>:
  Bool.pick(List<&2, T.Mark>, String.is_empty(title), acc, T.Mark{row, Nat.add(col, P.Box.center_at(title, w)), X.Text.cells(title), T.Title{}} <> acc)

def Zd.pane_of(z: ZPre) -> (List<&2, String> & List<&2, T.Mark>):
  match z:
    case ZPre{t, pane, ts, tl}:
      P.Pane.draw(pane, 0n)

# the float with both windows' rows and marks known
def Zd.box(g: ZGeo, pre: ZPre, +title: String, +mrows: List<&2, String>, +mmarks: List<&2, T.Mark>, +prows: List<&2, String>, +pmarks: List<&2, T.Mark>) -> T.Float:
  match g pre:
    case ZGeo{+row, +col, +w, +h, +side, +mw, +mh, +pw, +ph} ZPre{+ptitle, pane, +ts, +tl}:
      +border = {[T.Mark{0n, 0n, w, T.Border{}}, T.Mark{Nat.sub(h, 1n), 0n, w, T.Border{}}] : List<&2, T.Mark>}
      +pcol = Bool.pick(Nat, side, Nat.add(mw, 3n), 1n)
      +prow = Bool.pick(Nat, side, 1n, Nat.add(mh, 3n))
      +sides = Bool.pick(List<&2, T.Mark>, side, P.Box.sides(Nat.sub(h, 2n), 1n, [0n, 1n+mw, Nat.add(mw, 2n), Nat.sub(w, 1n)], border), P.Box.sides(Nat.sub(h, 2n), 1n, [0n, Nat.sub(w, 1n)], T.Mark{1n+mh, 0n, w, T.Border{}} <> T.Mark{Nat.add(mh, 2n), 0n, w, T.Border{}} <> border))
      +titles = Zd.titled(ptitle, Bool.pick(Nat, side, 0n, Nat.add(mh, 2n)), Bool.pick(Nat, side, Nat.add(mw, 3n), 1n), pw, Zd.titled(title, 0n, 1n, mw, sides))
      +thumbs = Zd.thumbs(tl, Nat.add(prow, ts), Nat.sub(w, 1n), titles)
      +marks = List.append(&2, T.Mark, List.reverse(&2, T.Mark, thumbs), List.append(&2, T.Mark, P.Marks.shift(mmarks, 1n, 1n, Nil{}), P.Marks.shift(pmarks, prow, pcol, Nil{})))
      +pbody = Zd.prows(prows, "│", 0n, ts, tl, Nil{})
      +sidel = {("╭" ++ P.Box.centered(title, mw) ++ "╮┬" ++ P.Box.centered(ptitle, pw) ++ "╮") <> List.append(&2, String, Zd.join(mrows, pbody, Nil{}), ["╰" ++ X.Text.rep('─', mw) ++ "╯┴" ++ X.Text.rep('─', pw) ++ "╯"]) : List<&2, String>}
      +downl = {("╭" ++ P.Box.centered(title, mw) ++ "╮") <> List.append(&2, String, Zd.boxed(mrows, Nil{}), ("╰" ++ X.Text.rep('─', mw) ++ "╯") <> ("├" ++ P.Box.centered(ptitle, pw) ++ "┤") <> List.append(&2, String, pbody, ["╰" ++ X.Text.rep('─', pw) ++ "╯"])) : List<&2, String>}
      T.Float{row, col, w, h, Bool.pick(List<&2, String>, side, sidel, downl), marks}

def Zd.box.pr(+g: ZGeo, +pre: ZPre, +title: String, +mrows: List<&2, String>, +mmarks: List<&2, T.Mark>, pr: (List<&2, String> & List<&2, T.Mark>)) -> T.Float:
  (prows, pmarks) = pr
  Zd.box(g, pre, title, mrows, mmarks, prows, pmarks)

def Zd.with_pre(+g: ZGeo, +title: String, mr: (List<&2, String> & List<&2, T.Mark>), +pre: ZPre) -> T.Float:
  (mrows, mmarks) = mr
  Zd.box.pr(g, pre, title, mrows, mmarks, Zd.pane_of(pre))

def Zd.mh(g: ZGeo) -> Nat:
  match g:
    case ZGeo{row, col, w, h, side, mw, mh, pw, ph}:
      mh

def Zd.mw(g: ZGeo) -> Nat:
  match g:
    case ZGeo{row, col, w, h, side, mw, mh, pw, ph}:
      mw

def Zd.pw(g: ZGeo) -> Nat:
  match g:
    case ZGeo{row, col, w, h, side, mw, mh, pw, ph}:
      pw

def Zd.ph(g: ZGeo) -> Nat:
  match g:
    case ZGeo{row, col, w, h, side, mw, mh, pw, ph}:
      ph

# fzf-lua's float on a screen of r rows and c columns: blines (lines) or
# buffers, the title, the query, the header rows, the items matched of
# total, the selected one; the list scrolls to keep 3 rows below it
# (--scroll-off 3)
def Fzf.float(+lines: Bool, +fs: List<&2, T.Buf>, +bs: List<&2, Nat>, +title: String, +q: String, +hs: List<&2, String>, +its: List<&2, T.Item>, +total: Nat, +sel: Nat, +r: Nat, +c: Nat) -> T.Float:
  +g = Fzf.geo(r, c)
  +rows = ZGeo.rows(g, List.length(&2, String, hs))
  +top = Nat.min(Nat.sub(Nat.add(sel, 4n), rows), Nat.sub(List.length(&2, T.Item, its), rows))
  Zd.with_pre(g, title, Zd.main(lines, q, hs, its, total, sel, top, Zd.mw(g), Zd.mh(g)), Zd.pre(fs, bs, List.get(&2, T.Item, its, sel), Zd.pw(g), Zd.ph(g)))
