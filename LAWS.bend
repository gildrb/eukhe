# eukhe.com's Neovim: the laws
# ============================
#
# Each law is a claim about the editor's shipped entry (vim/vim.bend):
# Vim.init (the files and the screen size), Vim.step (one event: a key, a
# click, the wheel, a new size) and Vim.frame (what the screen shows),
# Vim.lines (an Oil listing). The host paints Frame and runs Act; it
# decides nothing. A law over `evs` holds after EVERY sequence of events
# from the start, for every set of files and every screen size.
# PROOF.bend proves every law; `bend PROOF.bend --verdict` checks them.
#
# Requirements
#
# R1 The cursor is always on one cell of the screen: on a character of a line (or column 0 of an empty line) in the text rows, on the command line while typing a command, or inside the picker's float. Never between rows, never past a line's end, never off screen; after any sequence of events.
# R2 Motions behave as Neovim's: j k move one line (no further than the first and last), h l one character within the line, 0 and $ to the line's first and last character, gg and G to the first and last line; Esc returns to normal mode from anything.
# R3 'scrolloff' 8 (as much of it as the window holds): the cursor keeps that many lines above and below it on screen, unless the buffer ends first.
# R4 The screen fits: rows x cols cells from the last size event (at least 3 x 12); the number column one entry per text row, each exactly the gutter wide; the statusline exactly cols cells; search hits and the scrollbar inside the text rows; a float inside the screen, each of its rows exactly its width.
# R5 A click on a text cell puts the cursor on that line (the last line when below the text) and on that column (the line's last character when past its end).
# R6 Oil never traps: every listing starts with "../"; "-" goes to the parent folder (at the root it stays); Ctrl-c in a listing (normal mode) returns to a file; "-" from a file opens its folder with the cursor on the file's entry.
# R7 The host never does anything the files did not ask for: the only text ever copied is the install command, and every URL opened appears in a file.
# A1 Every character of a file takes one cell (the site's font is monospace, every glyph checked at build); files hold no wide characters.
# A2 A file with no lines shows one empty line, as Neovim does; past the last file, the window shows one empty line.
# A3 The motion laws (R2, R5) hold from normal mode: after an Esc, which closes a picker, cancels a command line and drops a count or a waiting key.
# A4 j, k, gg and G keep the column ('nostartofline'): a cursor short of its line's end stays on that column, or on the new line's last character when the line is shorter; a cursor at its line's end stays at least as far right.
# R8 The window always shows a real buffer: one of the files, a folder of their paths, or the root; the start shows the first file; Esc never changes what the window shows.
# A5 After Esc the command line may still show the last message or search, as in Neovim; while a command line or a picker is open, the window behind it is not checked for 'scrolloff'.

import Base
import ./vim/types.bend as T
import ./vim/vim.bend as V

# Terms
# -----

def Spec.install() -> String:
  "curl -fsSL https://eukhe.com/install | sh"

def Spec.min(+a: Nat, +b: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_le(a, b), a, b)

def Spec.max(+a: Nat, +b: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_le(a, b), b, a)

# the last place a cursor may take on a line of n characters
def Spec.last(n: Nat) -> Nat:
  Nat.sub(n, 1n)

def Spec.key(name: String) -> T.Ev:
  T.EvKey{name}

# evs, then e
def Spec.snoc(evs: List<&2, T.Ev>, e: T.Ev) -> List<&2, T.Ev>:
  match evs:
    case Nil{}:
      [e]
    case Con{h, t}:
      Con{h, Spec.snoc(t, e)}

def Spec.after(s: T.Step) -> T.St:
  match s:
    case T.Step{st, act}:
      st

def Spec.act(s: T.Step) -> T.Act:
  match s:
    case T.Step{st, act}:
      act

# the editor after the events evs, from s
def Spec.replay(evs: List<&2, T.Ev>, s: T.St) -> T.St:
  match evs:
    case Nil{}:
      s
    case Con{e, t}:
      Spec.replay(t, Spec.after(V.Vim.step(s, e)))

# the editor after evs, from the start with files fs on a rows x cols screen
def Spec.run(fs: List<&2, T.Buf>, rows: Nat, cols: Nat, evs: List<&2, T.Ev>) -> T.St:
  Spec.replay(evs, V.Vim.init(fs, rows, cols))

# the screen size after evs: the last size event's, else the first; at
# least 3 rows and 12 columns
def Spec.rows.go(evs: List<&2, T.Ev>, r: Nat) -> Nat:
  match evs:
    case Nil{}:
      r
    case Con{T.EvSize{rows, cols}, t}:
      Spec.rows.go(t, rows)
    case Con{T.EvKey{name}, t}:
      Spec.rows.go(t, r)
    case Con{T.EvClick{row, col}, t}:
      Spec.rows.go(t, r)
    case Con{T.EvWheel{down, notches}, t}:
      Spec.rows.go(t, r)

def Spec.cols.go(evs: List<&2, T.Ev>, c: Nat) -> Nat:
  match evs:
    case Nil{}:
      c
    case Con{T.EvSize{rows, cols}, t}:
      Spec.cols.go(t, cols)
    case Con{T.EvKey{name}, t}:
      Spec.cols.go(t, c)
    case Con{T.EvClick{row, col}, t}:
      Spec.cols.go(t, c)
    case Con{T.EvWheel{down, notches}, t}:
      Spec.cols.go(t, c)

def Spec.rows(rows: Nat, evs: List<&2, T.Ev>) -> Nat:
  Spec.max(Spec.rows.go(evs, rows), 3n)

def Spec.cols(cols: Nat, evs: List<&2, T.Ev>) -> Nat:
  Spec.max(Spec.cols.go(evs, cols), 12n)

# Text

def Spec.chars(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      1n+Spec.chars(t)

# the cells a string takes: fff's prompt goose (U+1FABF) two, every other
# character one
def Spec.cells(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{Chr{x}, t}:
      Nat.add(Bool.pick(Nat, U32.is_eq(x, 129727), 2n, 1n), Spec.cells(t))

# character c of s, as a string; " " past its end
def Spec.char(s: String, c: Nat) -> String:
  match s c:
    case SNil{} _:
      " "
    case SCon{h, t} 0n:
      SCon{h, SNil{}}
    case SCon{h, t} 1n+p:
      Spec.char(t, p)

def Spec.prefix(p: String, s: String) -> Bool:
  match p s:
    case SNil{} _:
      True{}
    case SCon{a, pt} SNil{}:
      False{}
    case SCon{a, pt} SCon{b, st}:
      Bool.and(Char.is_eq(a, b), Spec.prefix(pt, st))

# whether u appears in s
def Spec.within(+u: String, s: String) -> Bool:
  match s:
    case SNil{}:
      String.is_empty(u)
    case SCon{h, +t}:
      Bool.or(Spec.prefix(u, SCon{h, t}), Spec.within(u, t))

def Spec.in_lines(+u: String, ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Spec.within(u, h), Spec.in_lines(u, t))

def Spec.in_files(+u: String, fs: List<&2, T.Buf>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{T.Buf{path, lines}, t}:
      Bool.or(Spec.in_lines(u, lines), Spec.in_files(u, t))

# Lines

def Spec.count(ls: List<&2, String>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+Spec.count(t)

def Spec.line(ls: List<&2, String>, i: Nat) -> String:
  match ls i:
    case Nil{} _:
      ""
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      Spec.line(t, p)

def Spec.head(ls: List<&2, String>) -> String:
  Spec.line(ls, 0n)

# at least one line
def Spec.some(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      [""]
    case Con{h, t}:
      Con{h, t}

# the lines of file i of fs (A2)
def Spec.file(fs: List<&2, T.Buf>, i: Nat) -> List<&2, String>:
  match fs i:
    case Nil{} _:
      [""]
    case Con{T.Buf{path, lines}, t} 0n:
      Spec.some(lines)
    case Con{b, t} 1n+p:
      Spec.file(t, p)

def Spec.nfiles(fs: List<&2, T.Buf>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Con{b, t}:
      1n+Spec.nfiles(t)

def Spec.path(fs: List<&2, T.Buf>, i: Nat) -> String:
  match fs i:
    case Nil{} _:
      ""
    case Con{T.Buf{path, lines}, t} 0n:
      path
    case Con{b, t} 1n+p:
      Spec.path(t, p)

# the folder of a path: up to and with its last "/"; "" for none
def Spec.dir.go(s: String, +seen: String, +best: String) -> String:
  match s:
    case SNil{}:
      best
    case SCon{+h, t}:
      +next = seen ++ SCon{h, SNil{}}
      Spec.dir.go(t, next, Bool.pick(String, Char.is_eq(h, '/'), next, best))

def Spec.dir(s: String) -> String:
  Spec.dir.go(s, "", "")

# the name of a path in its folder: after its last "/"
def Spec.base.go(s: String, +cur: String) -> String:
  match s:
    case SNil{}:
      cur
    case SCon{+h, t}:
      Spec.base.go(t, Bool.pick(String, Char.is_eq(h, '/'), "", cur ++ SCon{h, SNil{}}))

def Spec.base(s: String) -> String:
  Spec.base.go(s, "")

# the parent of a folder "a/b/": "a/"; of "a/": ""; the root "" stays
def Spec.drop_last(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{h, SNil{}}:
      ""
    case SCon{h, t}:
      SCon{h, Spec.drop_last(t)}

def Spec.parent(d: String) -> String:
  Spec.dir(Spec.drop_last(d))

# The frame

def F.tgt(f: T.Frame) -> T.Tgt:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, cur, char, cmd, hits, bar, cl, status, float}:
      tgt

def F.top(f: T.Frame) -> Nat:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, cur, char, cmd, hits, bar, cl, status, float}:
      top

def F.left(f: T.Frame) -> Nat:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, cur, char, cmd, hits, bar, cl, status, float}:
      left

def F.gutter(f: T.Frame) -> Nat:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, cur, char, cmd, hits, bar, cl, status, float}:
      gutter

def F.nums(f: T.Frame) -> List<&2, String>:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, cur, char, cmd, hits, bar, cl, status, float}:
      nums

def F.row(f: T.Frame) -> Nat:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, T.Cell{row, col}, char, cmd, hits, bar, cl, status, float}:
      row

def F.col(f: T.Frame) -> Nat:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, T.Cell{row, col}, char, cmd, hits, bar, cl, status, float}:
      col

def F.char(f: T.Frame) -> String:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, cur, char, cmd, hits, bar, cl, status, float}:
      char

def F.hits(f: T.Frame) -> List<&2, T.Span>:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, cur, char, cmd, hits, bar, cl, status, float}:
      hits

def F.bar(f: T.Frame) -> T.Span:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, cur, char, cmd, hits, bar, cl, status, float}:
      bar

def F.status(f: T.Frame) -> String:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, cur, char, cmd, hits, bar, cl, status, float}:
      status

def F.float(f: T.Frame) -> Maybe<&2, T.Float>:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, cur, char, cmd, hits, bar, cl, status, float}:
      float

def Spec.is_file(t: T.Tgt) -> Bool:
  match t:
    case T.File{i}:
      True{}
    case T.Dir{path}:
      False{}

def Spec.is_dir(t: T.Tgt, d: String) -> Bool:
  match t:
    case T.File{i}:
      False{}
    case T.Dir{path}:
      String.eq(path, d)

def Spec.same_tgt(a: T.Tgt, b: T.Tgt) -> Bool:
  match a b:
    case T.File{i} T.File{j}:
      Nat.is_eq(i, j)
    case T.Dir{p} T.Dir{q}:
      String.eq(p, q)
    case T.File{i} T.Dir{q}:
      False{}
    case T.Dir{p} T.File{j}:
      False{}

# the lines the window of s shows: a file's (A2), or an Oil listing
def Spec.lines.of(fs: List<&2, T.Buf>, +s: T.St, t: T.Tgt) -> List<&2, String>:
  match t:
    case T.File{i}:
      Spec.file(fs, i)
    case T.Dir{path}:
      V.Vim.lines(s)

def Spec.lines(fs: List<&2, T.Buf>, +s: T.St) -> List<&2, String>:
  Spec.lines.of(fs, s, F.tgt(V.Vim.frame(s)))

# the cursor's line and column in the window's text, read from the frame
def Spec.at_line(+f: T.Frame) -> Nat:
  Nat.add(F.top(f), F.row(f))

def Spec.at_col(+f: T.Frame) -> Nat:
  Nat.add(F.left(f), Nat.sub(F.col(f), F.gutter(f)))

# the cursor is on the text (R1): in a text row, right of the gutter, on
# an existing line, on one of its characters (column 0 when empty), and
# the frame names the character under it
def Spec.on_text(fs: List<&2, T.Buf>, +s: T.St, +rows: Nat, +cols: Nat) -> Bool:
  +f = V.Vim.frame(s)
  +ls = Spec.lines(fs, s)
  +l = Spec.at_line(f)
  +c = Spec.at_col(f)
  +line = Spec.line(ls, l)
  Bool.and(Nat.is_lt(F.row(f), Nat.sub(rows, 2n)),
  Bool.and(Nat.is_le(F.gutter(f), F.col(f)),
  Bool.and(Nat.is_lt(F.col(f), cols),
  Bool.and(Nat.is_lt(l, Spec.count(ls)),
  Bool.and(Nat.is_le(c, Spec.last(Spec.chars(line))),
  String.eq(F.char(f), Spec.char(line, c)))))))

# a box (row, col, height, width) inside the screen, and a cell in it
def Spec.box_in(+row: Nat, +col: Nat, +h: Nat, +w: Nat, +rows: Nat, +cols: Nat) -> Bool:
  Bool.and(Nat.is_le(Nat.add(row, h), rows), Nat.is_le(Nat.add(col, w), cols))

def Spec.cell_in(+r: Nat, +c: Nat, +row: Nat, +col: Nat, +h: Nat, +w: Nat) -> Bool:
  Bool.and(Bool.and(Nat.is_le(row, r), Nat.is_lt(r, Nat.add(row, h))), Bool.and(Nat.is_le(col, c), Nat.is_lt(c, Nat.add(col, w))))

# the cursor anywhere (R1): in a float, inside it; else on the command
# line or on the text
def Spec.cursor_in(fs: List<&2, T.Buf>, +s: T.St, +f: T.Frame, +rows: Nat, +cols: Nat, m: Maybe<&2, T.Float>) -> Bool:
  match m:
    case Some{T.Float{row, col, width, height, lines, marks}}:
      Spec.cell_in(F.row(f), F.col(f), row, col, height, width)
    case None{}:
      Bool.or(Bool.and(Nat.is_eq(F.row(f), Nat.sub(rows, 1n)), Nat.is_lt(F.col(f), cols)), Spec.on_text(fs, s, rows, cols))

def Spec.cursor_ok(fs: List<&2, T.Buf>, +s: T.St, +rows: Nat, +cols: Nat) -> Bool:
  +f = V.Vim.frame(s)
  Spec.cursor_in(fs, s, f, rows, cols, F.float(f))

# every string of ls exactly w cells
def Spec.all_cells(ls: List<&2, String>, +w: Nat) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Nat.is_eq(Spec.cells(h), w), Spec.all_cells(t, w))

def Spec.count_marks(ls: List<&2, T.Mark>, +h: Nat, +w: Nat) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{T.Mark{row, col, len, group}, t}:
      Bool.and(Bool.and(Nat.is_lt(row, h), Nat.is_le(Nat.add(col, len), w)), Spec.count_marks(t, h, w))

def Spec.spans_in(ls: List<&2, T.Span>, +h: Nat, +g: Nat, +cols: Nat) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{T.Span{row, +col, +len}, t}:
      Bool.and(Bool.and(Bool.and(Nat.is_lt(row, h), Nat.is_le(g, col)), Bool.and(Nat.is_lt(0n, len), Nat.is_le(Nat.add(col, len), cols))), Spec.spans_in(t, h, g, cols))

def Spec.lines_count(ls: List<&2, String>) -> Nat:
  Spec.count(ls)

def Spec.float_ok(m: Maybe<&2, T.Float>, +rows: Nat, +cols: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{T.Float{row, col, +width, +height, +lines, marks}}:
      Bool.and(Spec.box_in(row, col, height, width, rows, cols),
      Bool.and(Nat.is_eq(Spec.lines_count(lines), height),
      Bool.and(Spec.all_cells(lines, width), Spec.count_marks(marks, height, width))))

def Spec.bar_ok(b: T.Span, +h: Nat) -> Bool:
  match b:
    case T.Span{row, col, len}:
      Nat.is_le(Nat.add(row, len), h)

# the screen fits (R4)
def Spec.fits(+s: T.St, +rows: Nat, +cols: Nat) -> Bool:
  +f = V.Vim.frame(s)
  +h = Nat.sub(rows, 2n)
  +g = F.gutter(f)
  Bool.and(Nat.is_lt(g, cols),
  Bool.and(Nat.is_eq(Spec.count(F.nums(f)), h),
  Bool.and(Spec.all_cells(F.nums(f), g),
  Bool.and(Nat.is_eq(Spec.cells(F.status(f)), cols),
  Bool.and(Spec.spans_in(F.hits(f), h, g, cols),
  Bool.and(Spec.bar_ok(F.bar(f), h), Spec.float_ok(F.float(f), rows, cols)))))))

# 'scrolloff' (R3): so = min(8, (h - 1) / 2) lines above and below the
# cursor, unless the buffer ends first
def Spec.scrolled(fs: List<&2, T.Buf>, +s: T.St, +rows: Nat) -> Bool:
  +f = V.Vim.frame(s)
  +h = Nat.sub(rows, 2n)
  +so = Spec.min(8n, Nat.div(Nat.sub(h, 1n), 2n))
  +l = Spec.at_line(f)
  +last = Spec.last(Spec.count(Spec.lines(fs, s)))
  Bool.and(Nat.is_le(Spec.min(so, l), F.row(f)), Nat.is_le(Spec.min(so, Nat.sub(last, l)), Nat.sub(Nat.sub(h, 1n), F.row(f))))

# where a key moved the cursor: from frame a to frame b, in the same
# window (R2)
def Spec.moved(fs: List<&2, T.Buf>, +s1: T.St, +s2: T.St, +line: Nat, +col: Nat) -> Bool:
  +a = V.Vim.frame(s1)
  +b = V.Vim.frame(s2)
  Bool.and(Spec.same_tgt(F.tgt(a), F.tgt(b)), Bool.and(Nat.is_eq(Spec.at_line(b), line), Nat.is_eq(Spec.at_col(b), col)))

def Spec.moved_line(fs: List<&2, T.Buf>, +s1: T.St, +s2: T.St, +line: Nat) -> Bool:
  +a = V.Vim.frame(s1)
  +b = V.Vim.frame(s2)
  Bool.and(Spec.same_tgt(F.tgt(a), F.tgt(b)), Nat.is_eq(Spec.at_line(b), line))

# the editor in normal mode after evs (A3)
def Spec.normal(fs: List<&2, T.Buf>, rows: Nat, cols: Nat, evs: List<&2, T.Ev>) -> T.St:
  Spec.run(fs, rows, cols, Spec.snoc(evs, Spec.key("<Esc>")))

def Spec.press(+s: T.St, name: String) -> T.St:
  Spec.after(V.Vim.step(s, Spec.key(name)))

# what the host does is asked for by the files (R7)
def Spec.honest(fs: List<&2, T.Buf>, a: T.Act) -> Bool:
  match a:
    case T.Nothing{}:
      True{}
    case T.CopyText{text}:
      String.eq(text, Spec.install())
    case T.OpenUrl{url}:
      Spec.in_files(url, fs)

# p implies q
def Spec.implies(p: Bool, q: Bool) -> Bool:
  Bool.or(Bool.not(p), q)

# The claims the motion, mouse and Oil laws make, from normal mode after
# evs (A3)

def Claim.j(+fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  +l = Spec.at_line(V.Vim.frame(s))
  Spec.moved_line(fs, s, Spec.press(s, "j"), Spec.min(1n+l, Spec.last(Spec.count(Spec.lines(fs, s)))))

def Claim.k(fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  Spec.moved_line(fs, s, Spec.press(s, "k"), Nat.sub(Spec.at_line(V.Vim.frame(s)), 1n))

def Claim.gg(fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  Spec.moved_line(fs, s, Spec.press(Spec.press(s, "g"), "g"), 0n)

def Claim.G(+fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  Spec.moved_line(fs, s, Spec.press(s, "G"), Spec.last(Spec.count(Spec.lines(fs, s))))

def Claim.zero(fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  Spec.moved(fs, s, Spec.press(s, "0"), Spec.at_line(V.Vim.frame(s)), 0n)

def Claim.dollar(+fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  +l = Spec.at_line(V.Vim.frame(s))
  Spec.moved(fs, s, Spec.press(s, "$"), l, Spec.last(Spec.chars(Spec.line(Spec.lines(fs, s), l))))

def Claim.h(fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  +f = V.Vim.frame(s)
  Spec.moved(fs, s, Spec.press(s, "h"), Spec.at_line(f), Nat.sub(Spec.at_col(f), 1n))

def Claim.l(+fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  +f = V.Vim.frame(s)
  +l = Spec.at_line(f)
  Spec.moved(fs, s, Spec.press(s, "l"), l, Spec.min(1n+Spec.at_col(f), Spec.last(Spec.chars(Spec.line(Spec.lines(fs, s), l)))))

# a click on cell (r, c) of a screen of rows x cols
def Claim.click(+fs: List<&2, T.Buf>, +s: T.St, +rows: Nat, +cols: Nat, +r: Nat, +c: Nat) -> Bool:
  +f = V.Vim.frame(s)
  +g = F.gutter(f)
  +ls = Spec.lines(fs, s)
  +l = Spec.min(Nat.add(F.top(f), r), Spec.last(Spec.count(ls)))
  +into = Bool.and(Nat.is_lt(r, Nat.sub(rows, 2n)), Bool.and(Nat.is_le(g, c), Nat.is_lt(c, cols)))
  Spec.implies(into, Spec.moved(fs, s, Spec.after(V.Vim.step(s, T.EvClick{r, c})), l, Spec.min(Nat.add(F.left(f), Nat.sub(c, g)), Spec.last(Spec.chars(Spec.line(ls, l))))))

def Claim.up_entry(+s: T.St) -> Bool:
  Bool.pick(Bool, Spec.is_file(F.tgt(V.Vim.frame(s))), True{}, String.eq(Spec.head(V.Vim.lines(s)), "../"))

def Claim.parent.of(+s: T.St, t: T.Tgt) -> Bool:
  match t:
    case T.File{i}:
      True{}
    case T.Dir{path}:
      Spec.is_dir(F.tgt(V.Vim.frame(Spec.press(s, "-"))), Spec.parent(path))

def Claim.parent(+s: T.St) -> Bool:
  Claim.parent.of(s, F.tgt(V.Vim.frame(s)))

def Claim.open.of(+fs: List<&2, T.Buf>, +s: T.St, t: T.Tgt) -> Bool:
  match t:
    case T.Dir{path}:
      True{}
    case T.File{+i}:
      +s2 = Spec.press(s, "-")
      +p = Spec.path(fs, i)
      Spec.implies(Nat.is_lt(i, Spec.nfiles(fs)), Bool.and(Spec.is_dir(F.tgt(V.Vim.frame(s2)), Spec.dir(p)), String.eq(Spec.line(V.Vim.lines(s2), Spec.at_line(V.Vim.frame(s2))), Spec.base(p))))

def Claim.open(fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  Claim.open.of(fs, s, F.tgt(V.Vim.frame(s)))

def Example.start() -> Bool:
  +f = V.Vim.frame(V.Vim.init([T.Buf{"index.md", ["ab", "c"]}], 10n, 40n))
  Bool.and(Bool.and(Nat.is_eq(F.row(f), 0n), Nat.is_eq(F.col(f), 6n)), String.eq(F.char(f), "a"))

# A4: from frame a to frame b, a vertical motion kept the column
def Claim.vcol(+fs: List<&2, T.Buf>, +s1: T.St, +s2: T.St) -> Bool:
  +a = V.Vim.frame(s1)
  +b = V.Vim.frame(s2)
  +c = Spec.at_col(a)
  +last = Spec.last(Spec.chars(Spec.line(Spec.lines(fs, s1), Spec.at_line(a))))
  +want = Spec.min(c, Spec.last(Spec.chars(Spec.line(Spec.lines(fs, s2), Spec.at_line(b)))))
  Bool.pick(Bool, Nat.is_lt(c, last), Nat.is_eq(Spec.at_col(b), want), Nat.is_le(want, Spec.at_col(b)))

def Claim.vcol_j(fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  Claim.vcol(fs, s, Spec.press(s, "j"))

def Claim.vcol_k(fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  Claim.vcol(fs, s, Spec.press(s, "k"))

def Claim.vcol_gg(fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  Claim.vcol(fs, s, Spec.press(Spec.press(s, "g"), "g"))

def Claim.vcol_G(fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  Claim.vcol(fs, s, Spec.press(s, "G"))

def F.cmd(f: T.Frame) -> String:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, cur, char, cmd, hits, bar, cl, status, float}:
      cmd

def F.cl(f: T.Frame) -> Bool:
  match f:
    case T.Frame{tgt, top, left, gutter, nums, cur, char, cmd, hits, bar, cl, status, float}:
      cl

def Spec.is_none(m: Maybe<&2, T.Float>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

def Spec.bar_col(b: T.Span) -> Nat:
  match b:
    case T.Span{row, col, len}:
      col

# R4: the scrollbar in the last column, the command line within the
# screen, the cursorline shown exactly when no float is open
def Spec.edges(+s: T.St, +cols: Nat) -> Bool:
  +f = V.Vim.frame(s)
  +bar = Nat.is_eq(Spec.bar_col(F.bar(f)), Nat.sub(cols, 1n))
  Bool.and(bar, Bool.and(Nat.is_le(Spec.cells(F.cmd(f)), cols), Bool.not(Bool.xor(F.cl(f), Spec.is_none(F.float(f))))))

# R1: a cursor on the command line sits right after what it shows, on
# screen
def Spec.on_cmdline(+s: T.St, +rows: Nat, +cols: Nat) -> Bool:
  +f = V.Vim.frame(s)
  +there = Bool.and(Spec.is_none(F.float(f)), Nat.is_eq(F.row(f), Nat.sub(rows, 1n)))
  Spec.implies(there, Bool.and(Nat.is_eq(F.col(f), Spec.cells(F.cmd(f))), Bool.and(Nat.is_lt(F.col(f), cols), Bool.not(String.is_empty(F.cmd(f))))))

# R8: the window shows a real buffer: a file of fs (file 0 when fs is
# empty), or the folder of some file's path, or the root
def Spec.ends_slash(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, SNil{}}:
      Char.is_eq(h, '/')
    case SCon{h, t}:
      Spec.ends_slash(t)

def Spec.is_folder(+d: String, fs: List<&2, T.Buf>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{T.Buf{path, lines}, t}:
      Bool.or(Spec.prefix(d, path), Spec.is_folder(d, t))

def Spec.real(fs: List<&2, T.Buf>, t: T.Tgt) -> Bool:
  match t:
    case T.File{i}:
      Nat.is_lt(i, Spec.max(Spec.nfiles(fs), 1n))
    case T.Dir{+d}:
      Bool.or(String.is_empty(d), Bool.and(Spec.ends_slash(d), Spec.is_folder(d, fs)))

# R7: an opened URL is a web address written in a file
def Spec.url_ok(fs: List<&2, T.Buf>, a: T.Act) -> Bool:
  match a:
    case T.Nothing{}:
      True{}
    case T.CopyText{text}:
      True{}
    case T.OpenUrl{+url}:
      Bool.and(Bool.or(Spec.prefix("https://", url), Spec.prefix("http://", url)), Spec.in_files(url, fs))

# R3 outside Esc: with no float open and the cursor in the text rows,
# scrolloff holds
def Spec.scrolled_any(fs: List<&2, T.Buf>, +s: T.St, +rows: Nat) -> Bool:
  +f = V.Vim.frame(s)
  Spec.implies(Bool.and(Spec.is_none(F.float(f)), Nat.is_lt(F.row(f), Nat.sub(rows, 2n))), Spec.scrolled(fs, s, rows))

# Laws
# ----

# ---- the cursor ----

# LAW cursor_ok: after any events from the start, the cursor is inside
# the picker's float when one is open, else on the command line or on a
# character of the window's text (R1).
law cursor_ok:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Spec.cursor_ok(fs, Spec.run(fs, rows, cols, evs), Spec.rows(rows, evs), Spec.cols(cols, evs)) == True{} : Bool}

# LAW cursor_on_text: after any events and an Esc, the cursor is on a
# character of the window's text, and the frame names that character
# (R1, A3).
law cursor_on_text:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Spec.on_text(fs, Spec.normal(fs, rows, cols, evs), Spec.rows(rows, evs), Spec.cols(cols, evs)) == True{} : Bool}

# LAW scrolloff: after any events, in normal mode, the cursor keeps
# min(8, (h - 1) / 2) lines on screen above and below it unless the
# buffer ends first (R3).
law scrolloff:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Spec.scrolled(fs, Spec.normal(fs, rows, cols, evs), Spec.rows(rows, evs)) == True{} : Bool}

# LAW fits: after any events, the screen is the last size asked for (at
# least 3 x 12) and every part of the frame fits it (R4).
law fits:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Spec.fits(Spec.run(fs, rows, cols, evs), Spec.rows(rows, evs), Spec.cols(cols, evs)) == True{} : Bool}

# LAW cmdline_cursor: after any events, a cursor on the command line
# (no float open) sits right after the text it shows, on screen (R1).
law cmdline_cursor:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Spec.on_cmdline(Spec.run(fs, rows, cols, evs), Spec.rows(rows, evs), Spec.cols(cols, evs)) == True{} : Bool}

# LAW edges: after any events, the scrollbar is in the last column, the
# command line fits the screen, and the cursorline shows exactly when no
# float is open (R4).
law edges:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Spec.edges(Spec.run(fs, rows, cols, evs), Spec.cols(cols, evs)) == True{} : Bool}

# LAW esc_closes: after any events and an Esc, no float is open (A3).
law esc_closes:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {F.float(V.Vim.frame(Spec.normal(fs, rows, cols, evs))) == None{} : Maybe<&2, T.Float>}

# ---- motions (R2), from normal mode after any events ----

# LAW key_j: j moves to the next line, and stays on the last.
law key_j:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.j(fs, Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_k: k moves to the line before, and stays on the first.
law key_k:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.k(fs, Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_gg: gg moves to the first line.
law key_gg:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.gg(fs, Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_G: G moves to the last line.
law key_G:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.G(fs, Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_0: 0 moves to the line's first character.
law key_0:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.zero(fs, Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_dollar: $ moves to the line's last character.
law key_dollar:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.dollar(fs, Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_h: h moves one character left, and stays on the first.
law key_h:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.h(fs, Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_l: l moves one character right, and stays on the last.
law key_l:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.l(fs, Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW col_j: j keeps the column (A4).
law col_j:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.vcol_j(fs, Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW col_k: k keeps the column (A4).
law col_k:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.vcol_k(fs, Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW col_gg: gg keeps the column (A4).
law col_gg:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.vcol_gg(fs, Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW col_G: G keeps the column (A4).
law col_G:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.vcol_G(fs, Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# ---- the mouse (R5) ----

# LAW click: a click on text cell (r, c), right of the gutter, puts the
# cursor on line top + r (the last line when below the text) and column
# left + c - gutter (the line's last character when past its end).
law click:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  for +r: Nat
  for +c: Nat
  {Claim.click(fs, Spec.normal(fs, rows, cols, evs), Spec.rows(rows, evs), Spec.cols(cols, evs), r, c) == True{} : Bool}

# ---- Oil (R6) ----

# LAW oil_up_entry: after any events, an Oil listing starts with "../".
law oil_up_entry:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.up_entry(Spec.run(fs, rows, cols, evs)) == True{} : Bool}

# LAW oil_parent: in a listing, "-" shows the parent folder; at the root
# it stays.
law oil_parent:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.parent(Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW oil_close: after any events, Esc then Ctrl-c shows a file.
law oil_close:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Spec.is_file(F.tgt(V.Vim.frame(Spec.press(Spec.normal(fs, rows, cols, evs), "<C-c>")))) == True{} : Bool}

# LAW oil_open: in a file (one of fs), "-" shows the file's folder with
# the cursor on the file's entry.
law oil_open:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Claim.open(fs, Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# ---- the host (R7) ----

# LAW honest: after any events, the next one makes the host copy only the
# install command and open only a URL written in a file.
law honest:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  for e: T.Ev
  {Spec.honest(fs, Spec.act(V.Vim.step(Spec.run(fs, rows, cols, evs), e))) == True{} : Bool}

# ---- examples ----

# LAW start_example: the start on a 10 x 40 screen: the first file's
# first character, right of a 6-cell gutter (2 signs, 4 numbers).
law start_example:
  {Example.start() == True{} : Bool}

# ---- buffers (R8) ----

# LAW real_buffer: after any events, the window shows a file of fs, a
# folder of their paths, or the root.
law real_buffer:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Spec.real(fs, F.tgt(V.Vim.frame(Spec.run(fs, rows, cols, evs)))) == True{} : Bool}

# LAW start_file: the start shows the first file.
law start_file:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  {F.tgt(V.Vim.frame(V.Vim.init(fs, rows, cols))) == T.File{0n} : T.Tgt}

# LAW esc_keeps: Esc never changes what the window shows.
law esc_keeps:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Spec.same_tgt(F.tgt(V.Vim.frame(Spec.run(fs, rows, cols, evs))), F.tgt(V.Vim.frame(Spec.normal(fs, rows, cols, evs)))) == True{} : Bool}

# LAW scrolloff_any: after any events, with no float open and the cursor
# in the text rows, scrolloff holds (R3).
law scrolloff_any:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Spec.scrolled_any(fs, Spec.run(fs, rows, cols, evs), Spec.rows(rows, evs)) == True{} : Bool}

# LAW urls: after any events, the next one opens only a web address
# (http:// or https://) written in a file (R7).
law urls:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  for e: T.Ev
  {Spec.url_ok(fs, Spec.act(V.Vim.step(Spec.run(fs, rows, cols, evs), e))) == True{} : Bool}
