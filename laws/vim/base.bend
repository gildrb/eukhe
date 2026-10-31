# eukhe.com's Neovim: the spec helpers the laws share
# ===================================================
#
# The terms every section of laws/vim/ uses (LAWS.bend lists the
# requirements). Each section imports this file as Laws.

import Base
import ../../vim/types.bend as T
import ../../vim/vim.bend as V

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
def Spec.moved(+s1: T.St, +s2: T.St, +line: Nat, +col: Nat) -> Bool:
  +a = V.Vim.frame(s1)
  +b = V.Vim.frame(s2)
  Bool.and(Spec.same_tgt(F.tgt(a), F.tgt(b)), Bool.and(Nat.is_eq(Spec.at_line(b), line), Nat.is_eq(Spec.at_col(b), col)))

def Spec.moved_line(+s1: T.St, +s2: T.St, +line: Nat) -> Bool:
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
  Spec.moved_line(s, Spec.press(s, "j"), Spec.min(1n+l, Spec.last(Spec.count(Spec.lines(fs, s)))))

def Claim.k(+s: T.St) -> Bool:
  Spec.moved_line(s, Spec.press(s, "k"), Nat.sub(Spec.at_line(V.Vim.frame(s)), 1n))

def Claim.gg(+s: T.St) -> Bool:
  Spec.moved_line(s, Spec.press(Spec.press(s, "g"), "g"), 0n)

def Claim.G(+fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  Spec.moved_line(s, Spec.press(s, "G"), Spec.last(Spec.count(Spec.lines(fs, s))))

def Claim.zero(+s: T.St) -> Bool:
  Spec.moved(s, Spec.press(s, "0"), Spec.at_line(V.Vim.frame(s)), 0n)

def Claim.dollar(+fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  +l = Spec.at_line(V.Vim.frame(s))
  Spec.moved(s, Spec.press(s, "$"), l, Spec.last(Spec.chars(Spec.line(Spec.lines(fs, s), l))))

def Claim.h(+s: T.St) -> Bool:
  +f = V.Vim.frame(s)
  Spec.moved(s, Spec.press(s, "h"), Spec.at_line(f), Nat.sub(Spec.at_col(f), 1n))

def Claim.l(+fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  +f = V.Vim.frame(s)
  +l = Spec.at_line(f)
  Spec.moved(s, Spec.press(s, "l"), l, Spec.min(1n+Spec.at_col(f), Spec.last(Spec.chars(Spec.line(Spec.lines(fs, s), l)))))

# a click on cell (r, c) of a screen of rows x cols
def Claim.click(+fs: List<&2, T.Buf>, +s: T.St, +rows: Nat, +cols: Nat, +r: Nat, +c: Nat) -> Bool:
  +f = V.Vim.frame(s)
  +g = F.gutter(f)
  +ls = Spec.lines(fs, s)
  +l = Spec.min(Nat.add(F.top(f), r), Spec.last(Spec.count(ls)))
  +into = Bool.and(Nat.is_lt(r, Nat.sub(rows, 2n)), Bool.and(Nat.is_le(g, c), Nat.is_lt(c, cols)))
  Spec.implies(into, Spec.moved(s, Spec.after(V.Vim.step(s, T.EvClick{r, c})), l, Spec.min(Nat.add(F.left(f), Nat.sub(c, g)), Spec.last(Spec.chars(Spec.line(ls, l))))))

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
      Spec.implies(Bool.and(Nat.is_lt(i, Spec.nfiles(fs)), Bool.not(String.is_empty(Spec.base(p)))), Bool.and(Spec.is_dir(F.tgt(V.Vim.frame(s2)), Spec.dir(p)), String.eq(Spec.line(V.Vim.lines(s2), Spec.at_line(V.Vim.frame(s2))), Spec.base(p))))

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

# R1: ":" opens the command line with the cursor after it
def Claim.colon(+s: T.St, +rows: Nat) -> Bool:
  +f = V.Vim.frame(Spec.press(s, ":"))
  Bool.and(Bool.and(Nat.is_eq(F.row(f), Nat.sub(rows, 1n)), Nat.is_eq(F.col(f), 1n)), String.eq(F.cmd(f), ":"))

# R4: ":5<CR>" goes to line 5 (the last when shorter)
def Claim.ex_line(+fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  +s2 = Spec.press(Spec.press(Spec.press(s, ":"), "5"), "<CR>")
  Spec.moved_line(s, s2, Spec.min(4n, Spec.last(Spec.count(Spec.lines(fs, s)))))

# R8: Esc in normal mode changes nothing on screen
def Claim.esc_idle(+s: T.St) -> Bool:
  +a = V.Vim.frame(s)
  +b = V.Vim.frame(Spec.press(s, "<Esc>"))
  Bool.and(Bool.and(Spec.same_tgt(F.tgt(a), F.tgt(b)), Bool.and(Nat.is_eq(F.top(a), F.top(b)), Nat.is_eq(F.left(a), F.left(b)))), Bool.and(Nat.is_eq(F.row(a), F.row(b)), Nat.is_eq(F.col(a), F.col(b))))

# R6: "-" then Ctrl-c returns to the file it left
def Claim.back(+s: T.St) -> Bool:
  +a = V.Vim.frame(s)
  +b = V.Vim.frame(Spec.press(Spec.press(s, "-"), "<C-c>"))
  Bool.pick(Bool, Spec.is_file(F.tgt(a)), Spec.same_tgt(F.tgt(a), F.tgt(b)), True{})

# R6: a listing holds every child of its folder and nothing else
def Spec.drop_prefix(p: String, s: String) -> String:
  match p s:
    case SNil{} _:
      s
    case SCon{a, pt} SNil{}:
      ""
    case SCon{a, pt} SCon{b, st}:
      Spec.drop_prefix(pt, st)

def Spec.has_slash(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      Bool.or(Char.is_eq(h, '/'), Spec.has_slash(t))

# s up to and with its first "/"
def Spec.upto_slash(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+h, t}:
      Bool.pick(String, Char.is_eq(h, '/'), SCon{h, SNil{}}, SCon{h, Spec.upto_slash(t)})

def Spec.child(+d: String, +p: String) -> String:
  +rest = Spec.drop_prefix(d, p)
  Bool.pick(String, Spec.has_slash(rest), Spec.upto_slash(rest), rest)

def Spec.has_line(+x: String, ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(String.eq(h, x), Spec.has_line(x, t))

# every file under d has its child in ls
def Spec.covers(+d: String, fs: List<&2, T.Buf>, +ls: List<&2, String>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{T.Buf{+path, lines}, t}:
      +here = Bool.and(Spec.prefix(d, path), Bool.not(String.eq(d, path)))
      Bool.and(Spec.implies(here, Spec.has_line(Spec.child(d, path), ls)), Spec.covers(d, t, ls))

def Spec.is_child(+d: String, +x: String, fs: List<&2, T.Buf>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{T.Buf{+path, lines}, t}:
      Bool.or(Bool.and(Bool.and(Spec.prefix(d, path), Bool.not(String.eq(d, path))), String.eq(Spec.child(d, path), x)), Spec.is_child(d, x, t))

# every line after "../" is a child of d
def Spec.only(+d: String, ls: List<&2, String>, +fs: List<&2, T.Buf>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Spec.is_child(d, h, fs), Spec.only(d, t, fs))

def Spec.tail(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def Claim.listing.of(+fs: List<&2, T.Buf>, +s: T.St, t: T.Tgt) -> Bool:
  match t:
    case T.File{i}:
      True{}
    case T.Dir{+d}:
      +ls = V.Vim.lines(s)
      Bool.and(Spec.covers(d, fs, ls), Spec.only(d, Spec.tail(ls), fs))

def Claim.listing(fs: List<&2, T.Buf>, +s: T.St) -> Bool:
  Claim.listing.of(fs, s, F.tgt(V.Vim.frame(s)))

# R3: j scrolls only as far as scrolloff needs; below the cursor Neovim
# keeps min(8, h / 2) lines
def Claim.j_view(fs: List<&2, T.Buf>, +s: T.St, +rows: Nat) -> Bool:
  +a = V.Vim.frame(s)
  +b = V.Vim.frame(Spec.press(s, "j"))
  +h = Nat.sub(rows, 2n)
  +so = Spec.min(8n, Nat.div(h, 2n))
  +l = Spec.at_line(b)
  +last = Spec.last(Spec.count(Spec.lines(fs, s)))
  +need = Nat.add(l, Spec.min(so, Nat.sub(last, l)))
  +bottom = Nat.add(F.top(a), Nat.sub(h, 1n))
  Nat.is_eq(F.top(b), Bool.pick(Nat, Nat.is_le(need, bottom), F.top(a), Nat.sub(need, Nat.sub(h, 1n))))
