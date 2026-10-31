# eukhe.com's Neovim: the screen
# ==============================
#
# What the screen shows (Frame): the text rows with the sign and number
# columns, the statusline (" %f %m%= %l:%c ", laststatus=3), the command
# line, a picker's float, and where the cursor is.

import Base
import ./types.bend as T
import ./text.bend as X
import ./buf.bend as B
import ./view.bend as V
import ./st.bend as S
import ./core.bend as C
import ./pick.bend as P
import ./fff.bend as FF
import ./fzf.bend as Z

# the statusline's ruler: the line and the byte column ('%l:%c'; 0 on an
# empty line); Oil's lines hold a hidden "/001 " before each name
def Scr.ruler(+s: T.St) -> String:
  +line = C.St.text(s)
  +oil = Bool.pick(Nat, C.St.on_file(s), 0n, 5n)
  +c = Bool.pick(Nat, String.is_empty(line), Bool.pick(Nat, C.St.on_file(s), 0n, 6n), Nat.add(1n+oil, X.Text.bytes(line, C.St.col(s))))
  Nat.show(1n+C.St.line(s)) ++ ":" ++ Nat.show(c)

# the statusline, c cells: " %f %m" left, " %l:%c " right
def Scr.status(+name: String, +flag: String, +ruler: String, +c: Nat) -> String:
  +right = " " ++ ruler ++ " "
  X.Text.fit(" " ++ name ++ " " ++ flag, Nat.sub(c, X.Text.cells(right))) ++ right

def Scr.status_of(+s: T.St, m: T.Mode) -> String:
  match m:
    case T.Picking{+kind, +q, its, n, sel, top, pv, levels}:
      +fff = P.Pick.is_fff(kind)
      +bytes = X.Text.bytes(q, X.Text.len(q))
      Scr.status(Bool.pick(String, fff, "fffile search", "term:////1:/bin/sh"), Bool.pick(String, fff, "", "[-]"), "1:" ++ Nat.show(Nat.add(Bool.pick(Nat, fff, 6n, 3n), bytes)), S.St.cols(s))
    case T.Normal{}:
      Scr.status(B.Tgt.name(S.St.files(s), S.Win.tgt(S.St.win(s))), "", Scr.ruler(s), S.St.cols(s))
    case T.Typing{kind, text}:
      Scr.status(B.Tgt.name(S.St.files(s), S.Win.tgt(S.St.win(s))), "", Scr.ruler(s), S.St.cols(s))

# the character under the cursor; " " on an empty line
def Scr.char(m: Maybe<&2, Char>) -> String:
  match m:
    case None{}:
      " "
    case Some{c}:
      SCon{c, SNil{}}

def Scr.prefix(k: T.Line) -> String:
  match k:
    case T.Colon{}:
      ":"
    case T.Slash{}:
      "/"
    case T.Quest{}:
      "?"

def Scr.colon(k: T.Line) -> Bool:
  match k:
    case T.Colon{}:
      True{}
    case T.Slash{}:
      False{}
    case T.Quest{}:
      False{}

def Scr.hls(o: T.Opts) -> Bool:
  match o:
    case T.Opts{nu, rnu, hls}:
      hls

# the search the screen highlights: while typing / or ?, the text so far
# ('incsearch'); else the last search, when 'hlsearch' is on and not
# cleared
def Scr.lit(+s: T.St, m: T.Mode) -> Maybe<&2, T.Find>:
  match m:
    case T.Typing{kind, +text}:
      Bool.pick(Maybe<&2, T.Find>, Bool.or(String.is_empty(text), Scr.colon(kind)), None{}, Some{T.Find{text, False{}, False{}}})
    case T.Normal{}:
      Bool.pick(Maybe<&2, T.Find>, Bool.and(S.St.hl(s), Scr.hls(S.St.opts(s))), S.St.find(s), None{})
    case T.Picking{kind, q, its, n, sel, top, pv, levels}:
      Bool.pick(Maybe<&2, T.Find>, Bool.and(S.St.hl(s), Scr.hls(S.St.opts(s))), S.St.find(s), None{})

def Scr.hits(+s: T.St, m: Maybe<&2, T.Find>) -> List<&2, T.Span>:
  match m:
    case None{}:
      Nil{}
    case Some{f}:
      +w = S.St.win(s)
      V.View.hits(C.St.lines(s), C.St.folds(s), f, S.Win.top(w), C.St.h(s), S.Win.left(w), C.St.w(s), C.St.g(s))

def Scr.fff_row(g: FF.Geo) -> (Nat & Nat):
  match g:
    case FF.Geo{row, col, w, h, side, pre, lw, lh, pw, ph}:
      (Nat.add(row, Bool.pick(Nat, Bool.or(side, Bool.not(pre)), 1n, Nat.add(ph, 2n))), col)

def Scr.fzf_row(g: Z.ZGeo) -> (Nat & Nat):
  match g:
    case Z.ZGeo{row, col, w, h, side, mw, mh, pw, ph}:
      (1n+row, col)

def Scr.caret(rc: (Nat & Nat), +by: Nat) -> T.Cell:
  match rc:
    case (r, c):
      T.Cell{r, Nat.add(c, by)}

# what the command line shows of a command being typed: its end, so the
# cursor after it stays on screen (one cell is left for the cursor)
def Scr.typed(+line: String, +cols: Nat) -> String:
  X.Text.drop(line, Nat.sub(X.Text.len(line), Nat.sub(cols, 1n)))

# the cursor's cell: in the text; on the command line after its text; in
# a picker after its query
def Scr.cell(+s: T.St, m: T.Mode) -> T.Cell:
  match m:
    case T.Normal{}:
      +w = S.St.win(s)
      T.Cell{Nat.sub(C.St.line(s), S.Win.top(w)), Nat.add(C.St.g(s), Nat.sub(C.St.col(s), S.Win.left(w)))}
    case T.Typing{kind, +text}:
      T.Cell{Nat.sub(S.St.rows(s), 1n), X.Text.cells(Scr.typed(Scr.prefix(kind) ++ text, S.St.cols(s)))}
    case T.Picking{+kind, +q, its, n, sel, top, pv, levels}:
      +r = S.St.rows(s)
      +c = S.St.cols(s)
      X.Bool.when(T.Cell, P.Pick.is_fff(kind), u => Scr.caret(Scr.fzf_row(Z.Fzf.geo(r, c)), Nat.add(3n, X.Text.cells(q))), u => Scr.caret(Scr.fff_row(FF.Fff.geo(r, c)), Nat.add(4n, X.Text.cells(q))))

# the command line: what is typed, else the message with the search count
# right of it, ending where 'showcmd' starts (11 columns from the edge);
# a message wider than the screen is cut at its edge
def Scr.msg(+s: T.St) -> String:
  +stat = S.St.stat(s)
  Bool.pick(String, String.is_empty(stat), S.St.msg(s), X.Text.fit(S.St.msg(s), Nat.sub(Nat.sub(S.St.cols(s), 13n), X.Text.cells(stat))) ++ stat)

def Scr.cmd(+s: T.St, m: T.Mode) -> String:
  match m:
    case T.Typing{kind, text}:
      Scr.typed(Scr.prefix(kind) ++ text, S.St.cols(s))
    case T.Normal{}:
      X.Text.cut(Scr.msg(s), S.St.cols(s))
    case T.Picking{kind, q, its, n, sel, top, pv, levels}:
      X.Text.cut(Scr.msg(s), S.St.cols(s))


def Scr.under(+s: T.St, m: T.Mode) -> String:
  match m:
    case T.Normal{}:
      Scr.char(X.Text.at(C.St.text(s), C.St.col(s)))
    case T.Typing{kind, text}:
      " "
    case T.Picking{kind, q, its, n, sel, top, pv, levels}:
      " "

def Scr.float(+s: T.St, m: T.Mode) -> Maybe<&2, T.Float>:
  match m:
    case T.Normal{}:
      None{}
    case T.Typing{kind, text}:
      None{}
    case T.Picking{kind, q, its, n, sel, top, pv, levels}:
      Some{P.Pick.float(s, kind, q, its, n, sel, pv)}

def Scr.cl(m: T.Mode) -> Bool:
  match m:
    case T.Normal{}:
      True{}
    case T.Typing{kind, text}:
      True{}
    case T.Picking{kind, q, its, n, sel, top, pv, levels}:
      False{}

# the cursor's cell kept inside the float, when one is open (a float cut
# to a small screen may leave the prompt's caret past its edges)
def Scr.inside(c: T.Cell, m: Maybe<&2, T.Float>) -> T.Cell:
  match c m:
    case _ None{}:
      c
    case T.Cell{+r, +k} Some{T.Float{+row, +col, +width, +height, lines, marks}}:
      T.Cell{Nat.min(Nat.max(r, row), Nat.sub(Nat.add(row, height), 1n)), Nat.min(Nat.max(k, col), Nat.sub(Nat.add(col, width), 1n))}

# what the screen shows
def Scr.frame(+s: T.St) -> T.Frame:
  +w = S.St.win(s)
  +ls = C.St.lines(s)
  +n = B.Lines.len(ls)
  +h = C.St.h(s)
  +m = S.St.mode(s)
  +numw = V.View.numw(S.St.opts(s), n)
  +nums = V.View.nums(h, S.St.opts(s), S.Win.top(w), C.St.line(s), Nat.sub(n, 1n), numw, C.St.on_file(s))
  +fl = Scr.float(s, m)
  T.Frame{S.Win.tgt(w), S.Win.top(w), S.Win.left(w), C.St.g(s), nums, Scr.inside(Scr.cell(s, m), fl), Scr.under(s, m), Scr.cmd(s, m), Scr.hits(s, Scr.lit(s, m)), V.View.bar(n, h, S.Win.top(w), Nat.sub(S.St.cols(s), 1n)), Scr.cl(m), Scr.status_of(s, m), fl}
