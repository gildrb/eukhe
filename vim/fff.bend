# eukhe.com's Neovim: fff
# =======================
#
# dmtrKovalenko/fff as Gil's config opens it: find files (<leader>ff,
# <leader><leader>) and live grep (<leader>fg, <leader>fw), the prompt on
# top (layout.prompt_position "top"), the preview right of the list on
# screens of 130 columns and more, above it on narrower ones (flex), none
# when the list would keep fewer than 10 rows. Every size comes from
# fff/lua/fff/layout.lua.

import Base
import ./types.bend as T
import ./text.bend as X
import ./buf.bend as B
import ./find.bend as F
import ./box.bend as P

# Geometry
# --------

# the picker's box on screen: its first row and column, its size in
# cells, whether the preview is right of the list (else above it),
# whether there is a preview, the list's columns and rows, the preview's
# columns and rows
type Geo is Data:
  Geo{row: Nat, col: Nat, w: Nat, h: Nat, side: Bool, pre: Bool, lw: Nat, lh: Nat, pw: Nat, ph: Nat}

# the box of fff on a screen of r rows and c columns: 80% x 80% of it,
# centered over the rows above the statusline
def Fff.geo(+r: Nat, +c: Nat) -> Geo:
  +width = Nat.div(Nat.mul(c, 8n), 10n)
  +usable = Nat.sub(r, 2n)
  +height = Nat.min(Nat.div(Nat.mul(r, 8n), 10n), usable)
  +row = Bool.pick(Nat, Nat.is_ge(height, usable), 0n, 1n+Nat.div(Nat.sub(usable, height), 2n))
  +col = Bool.pick(Nat, Nat.is_ge(width, c), 0n, 1n+Nat.div(Nat.sub(c, width), 2n))
  +side = Nat.is_ge(c, 130n)
  +pw = Nat.div(Nat.mul(width, 5n), 10n)
  +ph = Nat.div(Nat.mul(height, 5n), 10n)
  +lh_side = Nat.sub(height, 4n)
  +lh_top = Nat.sub(Nat.sub(Nat.sub(height, 4n), ph), 3n)
  +pre = Nat.is_ge(Bool.pick(Nat, side, lh_side, lh_top), 10n)
  +iw = Nat.sub(width, 2n)
  +lw = Bool.pick(Nat, Bool.and(side, pre), Nat.sub(Nat.sub(iw, pw), 1n), iw)
  +lh = Bool.pick(Nat, side, lh_side, Bool.pick(Nat, pre, lh_top, Nat.sub(height, 6n)))
  +h = Bool.pick(Nat, side, height, Nat.sub(height, 2n))
  Geo{row, col, width, h, side, pre, lw, lh, Bool.pick(Nat, side, pw, iw), Bool.pick(Nat, side, Nat.sub(height, 2n), ph)}

def Geo.lh(g: Geo) -> Nat:
  match g:
    case Geo{row, col, w, h, side, pre, lw, lh, pw, ph}:
      lh

# the prompt's row in the box
def Geo.prompt(g: Geo) -> Nat:
  match g:
    case Geo{row, col, w, h, side, pre, lw, lh, pw, ph}:
      Bool.pick(Nat, Bool.or(side, Bool.not(pre)), 1n, Nat.add(ph, 2n))

# Matching files
# --------------
#
# fff (frizbee) forgives typos: a file matches when the longest run of the
# query's characters it holds in order leaves out at most max_typos of
# them (len / 4, at least 2, at most 6).

def Lcs.row(cs: List<&2, Char>, +c: Char, +diag: Nat, +left: Nat, ups: List<&2, Nat>, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match cs ups:
    case Nil{} _:
      List.reverse(&2, Nat, acc)
    case _ Nil{}:
      List.reverse(&2, Nat, acc)
    case Con{+q, qt} Con{+up, ut}:
      +v = Bool.pick(Nat, Char.is_eq(X.Char.fold(c), q), 1n+diag, Nat.max(up, left))
      Lcs.row(qt, c, up, v, ut, v <> acc)

def Lcs.go(s: String, +q: List<&2, Char>, +prev: List<&2, Nat>) -> Nat:
  match s:
    case SNil{}:
      Maybe.default(&2, Nat, List.last(&2, Nat, prev), 0n)
    case SCon{c, t}:
      Lcs.go(t, q, Lcs.row(q, c, 0n, 0n, prev, Nil{}))

# the most characters of q (folded) that s holds in order
def Lcs.len(+s: String, +q: String) -> Nat:
  +qs = String.to_list(q)
  Lcs.go(s, qs, List.replicate(Nat, List.length(&2, Char, qs), 0n))

def Greedy.go(s: String, q: String, +i: Nat, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match s q:
    case _ SNil{}:
      List.reverse(&2, Nat, acc)
    case SNil{} SCon{y, yt}:
      List.reverse(&2, Nat, acc)
    case SCon{x, +xt} SCon{+y, +yt}:
      X.Bool.when(List<&2, Nat>, Char.is_eq(X.Char.fold(x), y), u => Greedy.go(xt, SCon{y, yt}, 1n+i, acc), u => Greedy.go(xt, yt, 1n+i, i <> acc))

# the columns of s a left-to-right match of q (folded) takes
def Greedy.cols(s: String, q: String) -> List<&2, Nat>:
  Greedy.go(s, q, 0n, Nil{})

def Fff.typos(+n: Nat) -> Nat:
  Nat.min(6n, Nat.max(2n, Nat.div(n, 4n)))

# a file's name: its path after the last "/"
def Fff.name(+path: String) -> String:
  X.Text.drop(path, X.Text.len(B.Path.dir(path)))

# a file's folder as fff shows it: its path less the name and the "/"
def Fff.dir(+path: String) -> String:
  +d = B.Path.dir(path)
  X.Text.take(d, Nat.sub(X.Text.len(d), 1n))

# fff's order with no query: folders first by path, then names
def Fff.le(a: T.Item, b: T.Item) -> Bool:
  match a b:
    case T.Item{t1, p1, +x, h1} T.Item{t2, p2, +y, h2}:
      +dx = Fff.dir(x)
      +dy = Fff.dir(y)
      Bool.or(String.is_lt(dx, dy), Bool.and(String.eq(dx, dy), String.is_le(Fff.name(x), Fff.name(y))))

# a matched file's rank: the characters matched, then whole runs of the
# query in its name and path, then a short path
def Fff.score(+path: String, +q: String, +k: Nat) -> Nat:
  +fp = X.Text.fold(path)
  +name = Bool.pick(Nat, String.contains(X.Text.fold(Fff.name(path)), q), 40n, 0n)
  +whole = Bool.pick(Nat, String.contains(fp, q), 20n, 0n)
  Nat.sub(Nat.add(Nat.mul(k, 100n), Nat.add(name, whole)), Nat.min(X.Text.len(path), 19n))

type Scored is Data:
  Scored{score: Nat, item: T.Item}

def Scored.le(a: Scored, b: Scored) -> Bool:
  match a b:
    case Scored{x, i} Scored{y, j}:
      Nat.is_ge(x, y)

def Scored.items(xs: List<&2, Scored>, +acc: List<&2, T.Item>) -> List<&2, T.Item>:
  match xs:
    case Nil{}:
      List.reverse(&2, T.Item, acc)
    case Con{Scored{x, i}, t}:
      Scored.items(t, i <> acc)

def Fff.match(fs: List<&2, T.Item>, +q: String, +need: Nat, +acc: List<&2, Scored>) -> List<&2, Scored>:
  match fs:
    case Nil{}:
      List.reverse(&2, Scored, acc)
    case Con{T.Item{tgt, pos, +path, h}, t}:
      +k = Lcs.len(path, q)
      +item = {T.Item{tgt, pos, path, Greedy.cols(path, q)} : T.Item}
      Fff.match(t, q, need, Bool.pick(List<&2, Scored>, Nat.is_ge(k, need), Scored{Fff.score(path, q, k), item} <> acc, acc))

def Fff.all(fs: List<&2, T.Buf>, +i: Nat, +acc: List<&2, T.Item>) -> List<&2, T.Item>:
  match fs:
    case Nil{}:
      List.reverse(&2, T.Item, acc)
    case Con{T.Buf{p, ls}, t}:
      Fff.all(t, 1n+i, T.Item{T.File{i}, T.Pos{0n, 0n}, p, Nil{}} <> acc)

# the files matching query q (all of them for none), in fff's order
def Fff.files(+fs: List<&2, T.Buf>, +q: String) -> List<&2, T.Item>:
  +all = List.sort(~T.Item, ~Fff.le, Fff.all(fs, 0n, Nil{}))
  +fq = X.Text.fold(q)
  +n = X.Text.len(q)
  +need = Nat.max(1n, Nat.sub(n, Fff.typos(n)))
  Bool.pick(List<&2, T.Item>, String.is_empty(q), all, Scored.items(List.sort(~Scored, ~Scored.le, Fff.match(all, fq, need, Nil{})), Nil{}))

# Live grep
# ---------
#
# Plain text, smart case, one item per matching line (its first match),
# the line shown without its leading blanks (grep.trim_whitespace).

def Grep.cap() -> Nat:
  40n

def Grep.shift(cs: List<&2, Nat>, +by: Nat, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      List.reverse(&2, Nat, acc)
    case Con{c, t}:
      Grep.shift(t, by, Nat.sub(c, by) <> acc)

# the first column where pat starts in s, from column c (a match per
# line is what the list shows; its highlight is that match)
def Grep.cols(s: String, +pat: String, +c: Nat) -> List<&2, Nat>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{+h, +t}:
      X.Bool.when(List<&2, Nat>, X.Text.prefix(pat, SCon{h, t}), u => Grep.cols(t, pat, 1n+c), u => [c])

def Grep.line(+i: Nat, +l: Nat, +line: String, cs: List<&2, Nat>, +acc: List<&2, T.Item>) -> List<&2, T.Item>:
  match cs:
    case Nil{}:
      acc
    case Con{+c, t}:
      +ind = X.Text.indent(line, 0n)
      T.Item{T.File{i}, T.Pos{l, c}, X.Text.drop(line, ind), Grep.shift(Con{c, t}, ind, Nil{})} <> acc

# the matching lines of one file, while room is left
def Grep.lines(ls: List<&2, String>, fl: List<&2, String>, +room: Nat, +i: Nat, +l: Nat, +pat: String, +fold: Bool, +acc: List<&2, T.Item>) -> (Nat & List<&2, T.Item>):
  match ls fl:
    case Nil{} _:
      (room, acc)
    case _ Nil{}:
      (room, acc)
    case Con{+h, ht} Con{+f, ft}:
      +s = Bool.pick(String, fold, f, h)
      +hit = Bool.and(Nat.is_gt(room, 0n), String.contains(s, pat))
      +cs = X.Bool.when(List<&2, Nat>, hit, u => Nil{}, u => Grep.cols(s, pat, 0n))
      Grep.lines(ht, ft, Bool.pick(Nat, hit, Nat.sub(room, 1n), room), i, 1n+l, pat, fold, Grep.line(i, l, h, cs, acc))

def Grep.done(ra: (Nat & List<&2, T.Item>)) -> List<&2, T.Item>:
  match ra:
    case (room, acc):
      List.reverse(&2, T.Item, acc)

def Grep.file(ls: List<&2, String>, fl: List<&2, String>, +i: Nat, +pat: String, +fold: Bool, ra: (Nat & List<&2, T.Item>)) -> (Nat & List<&2, T.Item>):
  match ra:
    case (+room, +acc):
      X.Bool.when((Nat & List<&2, T.Item>), Nat.is_eq(room, 0n), u => Grep.lines(ls, fl, room, i, 0n, pat, fold, acc), u => (room, acc))

def Grep.next(fs: List<&2, T.Buf>, fls: List<&2, List<&2, String>>, +i: Nat, +pat: String, +fold: Bool, ra: (Nat & List<&2, T.Item>)) -> List<&2, T.Item>:
  match fs fls:
    case Nil{} _:
      Grep.done(ra)
    case _ Nil{}:
      Grep.done(ra)
    case Con{T.Buf{p, ls}, t} Con{fl, flt}:
      Grep.next(t, flt, 1n+i, pat, fold, Grep.file(ls, fl, i, pat, fold, ra))



# every line of every file holding q (smart case), at most Grep.cap()
def Fff.grep(+fs: List<&2, T.Buf>, +fls: List<&2, List<&2, String>>, +q: String) -> List<&2, T.Item>:
  +fold = Bool.not(X.Text.has_upper(q))
  +pat = Bool.pick(String, fold, X.Text.fold(q), q)
  X.Bool.when(List<&2, T.Item>, String.is_empty(q), u => Grep.next(fs, fls, 0n, pat, fold, (Grep.cap(), Nil{})), u => Nil{})

# Drawing
# -------

# a file's row of the list: the sign column, its name and folder,
# "(current)" right for the file the picker was opened from
def Fff.file_row(+path: String, +w: Nat, +current: Bool) -> String:
  +base = X.Text.fit("  " ++ Fff.name(path) ++ " " ++ Fff.dir(path), w)
  Bool.pick(String, current, X.Text.over(base, Nat.sub(w, 10n), " (current)"), base)

# matched path columns as cells of a file's row: the name's from cell 2,
# the folder's after the name and a space; the "/" between is not shown
def Fff.hits(cs: List<&2, Nat>, +ns: Nat, +nl: Nat, +row: Nat, +col: Nat, +w: Nat, +acc: List<&2, T.Mark>) -> List<&2, T.Mark>:
  match cs:
    case Nil{}:
      acc
    case Con{+c, t}:
      +named = Nat.is_ge(c, ns)
      +at = Bool.pick(Nat, named, Nat.add(2n, Nat.sub(c, ns)), Nat.add(Nat.add(3n, nl), c))
      +shown = Bool.and(Bool.or(named, Nat.is_lt(1n+c, ns)), Nat.is_lt(at, w))
      Fff.hits(t, ns, nl, row, col, w, Bool.pick(List<&2, T.Mark>, shown, T.Mark{row, Nat.add(col, at), 1n, T.Match{}} <> acc, acc))

# the marks of a file's row: the folder dimmed, "(current)" dimmed, the
# matched characters
def Fff.file_marks(+path: String, hits: List<&2, Nat>, +row: Nat, +col: Nat, +w: Nat, +current: Bool, +acc: List<&2, T.Mark>) -> List<&2, T.Mark>:
  +nl = X.Text.len(Fff.name(path))
  +dl = X.Text.len(Fff.dir(path))
  +dim = Bool.pick(List<&2, T.Mark>, Nat.is_eq(dl, 0n), acc, T.Mark{row, Nat.add(col, Nat.add(3n, nl)), dl, T.Dim{}} <> acc)
  +cur = Bool.pick(List<&2, T.Mark>, current, T.Mark{row, Nat.add(col, Nat.sub(w, 9n)), 9n, T.Dim{}} <> dim, dim)
  Fff.hits(hits, Nat.sub(X.Text.len(path), nl), nl, row, col, w, cur)

def Tgt.index(t: T.Tgt) -> Nat:
  match t:
    case T.File{i}:
      i
    case T.Dir{path}:
      0n

def Item.index(it: T.Item) -> Nat:
  match it:
    case T.Item{tgt, pos, text, hits}:
      Tgt.index(tgt)

def Item.pos(it: T.Item) -> T.Pos:
  match it:
    case T.Item{tgt, pos, text, hits}:
      pos

def Item.text(it: T.Item) -> String:
  match it:
    case T.Item{tgt, pos, text, hits}:
      text

# the rows (w cells) and marks of the files list: k rows of the page
# holding the selection (sel: its row counted from 1), the box's row row0
# first
def Fff.file_rows(k: Nat, its: List<&2, T.Item>, +w: Nat, +sel: Nat, +cur: Nat, +row0: Nat, +acc: List<&2, String>, +ms: List<&2, T.Mark>) -> (List<&2, String> & List<&2, T.Mark>):
  match k its:
    case 0n _:
      (List.reverse(&2, String, acc), ms)
    case 1n+p Nil{}:
      Fff.file_rows(p, Nil{}, w, Nat.sub(sel, 1n), cur, 1n+row0, X.Text.spaces(w, SNil{}) <> acc, ms)
    case 1n+p Con{T.Item{tgt, pos, +path, hits}, t}:
      +current = Nat.is_eq(cur, 1n+Tgt.index(tgt))
      +ms2 = Fff.file_marks(path, hits, row0, 1n, w, current, ms)
      +ms3 = Bool.pick(List<&2, T.Mark>, Nat.is_eq(sel, 1n), T.Mark{row0, 1n, w, T.Sel{}} <> ms2, ms2)
      Fff.file_rows(p, t, w, Nat.sub(sel, 1n), cur, 1n+row0, Fff.file_row(path, w, current) <> acc, ms3)

# Live grep's list
# ----------------

# a row of live grep's list: its text (w cells), its marks (row 0, cells
# from the list's first) and the number of its match from 1 (0: a file's
# header)
type GLine is Data:
  GLine{text: String, marks: List<&2, T.Mark>, item: Nat}

# a file's header: its name and folder, as the files list shows them
def Grep.header(+path: String, +w: Nat) -> GLine:
  +nl = X.Text.len(Fff.name(path))
  +dl = X.Text.len(Fff.dir(path))
  GLine{X.Text.fit("  " ++ Fff.name(path) ++ " " ++ Fff.dir(path), w), Bool.pick(List<&2, T.Mark>, Nat.is_eq(dl, 0n), Nil{}, [T.Mark{0n, Nat.add(3n, nl), dl, T.Dim{}}]), 0n}

# a match: " :line:col  text" after the sign column, the text cut with "…"
# to the cells the list leaves it
def Grep.match(+loc: String, +content: String, hits: List<&2, Nat>, +w: Nat, +k: Nat) -> GLine:
  +pre = Nat.add(3n, X.Text.len(loc))
  +avail = Nat.sub(Nat.sub(w, pre), 2n)
  +long = Bool.and(Nat.is_gt(X.Text.cells(content), avail), Nat.is_gt(avail, 3n))
  +shown = Bool.pick(String, long, X.Text.cut(content, Nat.sub(avail, 1n)) ++ "…", content)
  +lim = Bool.pick(Nat, long, Nat.sub(avail, 1n), X.Text.cells(content))
  GLine{X.Text.fit("   " ++ loc ++ "  " ++ shown, w), P.Marks.cols(hits, 0n, Nat.add(2n, pre), lim, [T.Mark{0n, 3n, X.Text.len(loc), T.Number{}}]), k}

# the list's rows for matches its: each file's header, then its matches
def Grep.glines(its: List<&2, T.Item>, +fs: List<&2, T.Buf>, +w: Nat, +last: Nat, +k: Nat, +acc: List<&2, GLine>) -> List<&2, GLine>:
  match its:
    case Nil{}:
      List.reverse(&2, GLine, acc)
    case Con{T.Item{tgt, T.Pos{+l, +c}, +text, +hits}, t}:
      +i = Tgt.index(tgt)
      +b = B.Files.at(fs, i)
      +ind = Nat.sub(c, Maybe.default(&2, Nat, List.head(&2, Nat, hits), 0n))
      +loc = ":" ++ Nat.show(1n+l) ++ ":" ++ Nat.show(Nat.add(1n+ind, X.Text.bytes(text, Nat.sub(c, ind))))
      +m = Grep.match(loc, text, hits, w, 1n+k)
      Grep.glines(t, fs, w, 1n+i, 1n+k, Bool.pick(List<&2, GLine>, Nat.is_eq(last, 1n+i), m <> acc, m <> Grep.header(B.Buf.path(b), w) <> acc))

def Grep.tip(+s: String, +w: Nat) -> GLine:
  GLine{X.Text.fit("  " ++ s, w), Bool.pick(List<&2, T.Mark>, String.is_empty(s), Nil{}, [T.Mark{0n, 2n, X.Text.cells(s), T.Dim{}}]), 0n}

def Grep.tips(xs: List<&2, String>, +w: Nat, +acc: List<&2, GLine>) -> List<&2, GLine>:
  match xs:
    case Nil{}:
      List.reverse(&2, GLine, acc)
    case Con{x, t}:
      Grep.tips(t, w, Grep.tip(x, w) <> acc)

# the list with nothing found: what to type, or that nothing matched, and
# the tips
def Grep.empty(+q: String, +w: Nat) -> List<&2, GLine>:
  +say = Bool.pick(String, String.is_empty(q), "  Start typing to search file contents...", "  No matches found.")
  Grep.tips(["", say, "", "  Tips:", "    \"pattern *.rs\"    search only in Rust files", "    \"pattern /src/\"   limit search to src/ directory", "    \"!test pattern\"   exclude test files", ""], w, Nil{})

# the row of match k (from 1) among the list's rows
def Grep.cline(gs: List<&2, GLine>, +k: Nat, +i: Nat) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{GLine{text, ms, +item}, t}:
      X.Bool.when(Nat, Nat.is_eq(item, k), u => Grep.cline(t, k, 1n+i), u => i)

# the rows of live grep's list: n of them from the first shown, the match
# sel (from 1) selected, the box's row row0 first
def Grep.rows(n: Nat, gs: List<&2, GLine>, +w: Nat, +sel: Nat, +row0: Nat, +acc: List<&2, String>, +ms: List<&2, T.Mark>) -> (List<&2, String> & List<&2, T.Mark>):
  match n gs:
    case 0n _:
      (List.reverse(&2, String, acc), ms)
    case 1n+p Nil{}:
      Grep.rows(p, Nil{}, w, sel, 1n+row0, X.Text.spaces(w, SNil{}) <> acc, ms)
    case 1n+p Con{GLine{text, marks, +item}, t}:
      +ms2 = P.Marks.shift(marks, row0, 1n, ms)
      +ms3 = Bool.pick(List<&2, T.Mark>, Bool.and(Nat.is_eq(item, sel), Nat.is_gt(sel, 0n)), T.Mark{row0, 1n, w, T.Sel{}} <> ms2, ms2)
      Grep.rows(p, t, w, sel, 1n+row0, text <> acc, ms3)

# Preview
# -------

# the preview's first line: where <C-d> and <C-u> left it (pv, from 1),
# else the top for files, the match with 8 rows above it for grep
def Fff.ptop(+grep: Bool, +fs: List<&2, T.Buf>, m: Maybe<&2, T.Item>, +pw: Nat, +pv: Nat) -> Nat:
  match m:
    case None{}:
      0n
    case Some{T.Item{tgt, T.Pos{+l, c}, text, hits}}:
      +b = B.Files.at(fs, Tgt.index(tgt))
      +ls = B.Buf.lines(b)
      +nw = Bool.pick(Nat, grep, P.Pane.numw(B.Lines.len(ls)), 0n)
      Bool.pick(Nat, Nat.is_gt(pv, 0n), Nat.sub(pv, 1n), Bool.pick(Nat, grep, P.Pane.zt(ls, l, Nat.sub(pw, nw), P.Pane.wraps(B.Buf.path(b))), 0n))

# the preview's title and pane for the selected item
def Fff.pane(+grep: Bool, +fs: List<&2, T.Buf>, m: Maybe<&2, T.Item>, +top: Nat, +pw: Nat, +ph: Nat) -> (String & P.Pane):
  match m:
    case None{}:
      (" Preview ", P.Pane{["No preview available"], ph, pw, Bool.pick(Nat, grep, 4n, 0n), 1n, False{}, 0n})
    case Some{T.Item{tgt, T.Pos{+l, c}, text, hits}}:
      +b = B.Files.at(fs, Tgt.index(tgt))
      +path = B.Buf.path(b)
      +ls = B.Buf.lines(b)
      +nw = Bool.pick(Nat, grep, P.Pane.numw(B.Lines.len(ls)), 0n)
      +title = " " ++ path ++ Bool.pick(String, grep, ":" ++ Nat.show(1n+l), "") ++ " "
      (title, P.Pane{B.Lines.drop(ls, top), ph, pw, nw, 1n+top, P.Pane.wraps(path), 0n})

# The float
# ---------

def Rows.box(xs: List<&2, String>, +l: String, +r: String, +acc: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{x, t}:
      Rows.box(t, l, r, (l ++ x ++ r) <> acc)

def Rows.pair(xs: List<&2, String>, ys: List<&2, String>, +acc: List<&2, String>) -> List<&2, String>:
  match xs ys:
    case Nil{} _:
      List.reverse(&2, String, acc)
    case _ Nil{}:
      List.reverse(&2, String, acc)
    case Con{x, xt} Con{y, yt}:
      Rows.pair(xt, yt, ("│" ++ x ++ "│" ++ y ++ "│") <> acc)

def Rows.first(xs: List<&2, String>) -> String:
  Maybe.default(&2, String, List.head(&2, String, xs), SNil{})

def Rows.second(xs: List<&2, String>) -> String:
  Maybe.default(&2, String, List.get(&2, String, xs, 1n), SNil{})

# the files list's or live grep's rows and marks, the first at box row
# row0
def Fff.list(+grep: Bool, +fs: List<&2, T.Buf>, +q: String, +its: List<&2, T.Item>, +sel: Nat, +top: Nat, +cur: Nat, +lw: Nat, +lh: Nat, +row0: Nat) -> (List<&2, String> & List<&2, T.Mark>):
  +page = Nat.mul(Nat.div(sel, Nat.max(lh, 1n)), lh)
  +gs = Bool.pick(List<&2, GLine>, List.is_empty(&2, T.Item, its), Grep.empty(q, lw), Grep.glines(List.take(&2, T.Item, its, Nat.add(sel, Nat.add(lh, 1n))), fs, lw, 0n, 0n, Nil{}))
  +gtop = Nat.min(Nat.sub(Nat.add(Grep.cline(gs, 1n+sel, 0n), 9n), lh), Nat.sub(List.length(&2, GLine, gs), lh))
  X.Bool.when((List<&2, String> & List<&2, T.Mark>), grep, u => Fff.file_rows(lh, List.drop(&2, T.Item, its, page), lw, Nat.sub(1n+sel, page), cur, row0, Nil{}, Nil{}), u => Grep.rows(lh, List.drop(&2, GLine, gs, gtop), lw, 1n+sel, row0, Nil{}, Nil{}))

# what the prompt shows right: the files matched of all (just all for a
# query under two characters), or live grep's mode
def Fff.right(+grep: Bool, +q: String, +n: Nat, +total: Nat) -> String:
  Bool.pick(String, grep, "<S-Tab> plain", Bool.pick(String, Nat.is_lt(X.Text.len(q), 2n), Nat.show(total), Nat.show(n) ++ "/" ++ Nat.show(total)))

# where what shows right of the prompt starts: window column width - 2 -
# its length (virt_text_win_col)
def Fff.right_at(+right: String, +lw: Nat) -> Nat:
  Nat.sub(Nat.sub(lw, 2n), X.Text.cells(right))

# the prompt's row: the goose, the query, what shows right
def Fff.prompt(+right: String, +q: String, +lw: Nat) -> String:
  X.Text.over(X.Text.fit("🪿 " ++ q, lw), Fff.right_at(right, lw), right)

def Fff.prompt_marks(+grep: Bool, +right: String, +r: Nat, +lw: Nat) -> List<&2, T.Mark>:
  +n = X.Text.cells(right)
  [T.Mark{r, 1n, 2n, T.Prompt{}}, T.Mark{r, Nat.add(1n, Fff.right_at(right, lw)), n, Bool.pick(T.Group, grep, T.Dim{}, T.Count{})}]

def Fff.cat(xs: List<&2, T.Mark>, ys: List<&2, T.Mark>) -> List<&2, T.Mark>:
  List.append(&2, T.Mark, xs, ys)

# the box with the preview right of the list
def Fff.side(+row: Nat, +col: Nat, +w: Nat, +h: Nat, +lw: Nat, +pw: Nat, +title: String, +ptitle: String, +prompt: String, pm: List<&2, T.Mark>, lr: (List<&2, String> & List<&2, T.Mark>), pr: (List<&2, String> & List<&2, T.Mark>)) -> T.Float:
  (lrows, lmarks) = lr
  (+prows, pmarks) = pr
  +r0 = "┌" ++ P.Box.titled(title, lw) ++ "┬" ++ P.Box.titled(ptitle, pw) ++ "┐"
  +r1 = "│" ++ prompt ++ "│" ++ Rows.first(prows) ++ "│"
  +r2 = "├" ++ X.Text.rep('─', lw) ++ "┤" ++ Rows.second(prows) ++ "│"
  +last = "└" ++ X.Text.rep('─', lw) ++ "┴" ++ X.Text.rep('─', pw) ++ "┘"
  +lines = {r0 <> r1 <> r2 <> List.append(&2, String, Rows.pair(lrows, List.drop(&2, String, prows, 2n), Nil{}), [last]) : List<&2, String>}
  +border = P.Box.sides(Nat.sub(h, 2n), 1n, [0n, 1n+lw, Nat.sub(w, 1n)], {[T.Mark{0n, 0n, w, T.Border{}}, T.Mark{Nat.sub(h, 1n), 0n, w, T.Border{}}, T.Mark{2n, 0n, Nat.add(lw, 2n), T.Border{}}] : List<&2, T.Mark>})
  +titles = {[T.Mark{0n, 1n, X.Text.cells(title), T.Title{}}, T.Mark{0n, Nat.add(lw, 2n), X.Text.cells(ptitle), T.Title{}}] : List<&2, T.Mark>}
  T.Float{row, col, w, h, lines, Fff.cat(border, Fff.cat(titles, Fff.cat(pm, Fff.cat(lmarks, P.Marks.shift(pmarks, 1n, Nat.add(lw, 2n), Nil{})))))}

# the box with the preview above the list
def Fff.top(+row: Nat, +col: Nat, +w: Nat, +h: Nat, +lw: Nat, +ph: Nat, +title: String, +ptitle: String, +prompt: String, pm: List<&2, T.Mark>, lr: (List<&2, String> & List<&2, T.Mark>), pr: (List<&2, String> & List<&2, T.Mark>)) -> T.Float:
  (lrows, lmarks) = lr
  (prows, pmarks) = pr
  +r0 = "┌" ++ P.Box.titled(ptitle, lw) ++ "┐"
  +ri = "├" ++ P.Box.titled(title, lw) ++ "┤"
  +rp = "│" ++ prompt ++ "│"
  +rs = "├" ++ X.Text.rep('─', lw) ++ "┤"
  +last = "└" ++ X.Text.rep('─', lw) ++ "┘"
  +lines = {r0 <> List.append(&2, String, Rows.box(prows, "│", "│", Nil{}), ri <> rp <> rs <> List.append(&2, String, Rows.box(lrows, "│", "│", Nil{}), [last])) : List<&2, String>}
  +border = P.Box.sides(Nat.sub(h, 2n), 1n, [0n, Nat.sub(w, 1n)], {[T.Mark{0n, 0n, w, T.Border{}}, T.Mark{1n+ph, 0n, w, T.Border{}}, T.Mark{Nat.add(ph, 3n), 0n, w, T.Border{}}, T.Mark{Nat.sub(h, 1n), 0n, w, T.Border{}}] : List<&2, T.Mark>})
  +titles = {[T.Mark{0n, 1n, X.Text.cells(ptitle), T.Title{}}, T.Mark{1n+ph, 1n, X.Text.cells(title), T.Title{}}] : List<&2, T.Mark>}
  T.Float{row, col, w, h, lines, Fff.cat(border, Fff.cat(titles, Fff.cat(pm, Fff.cat(lmarks, P.Marks.shift(pmarks, 1n, 1n, Nil{})))))}

# the box without a preview
def Fff.bare(+row: Nat, +col: Nat, +w: Nat, +h: Nat, +lw: Nat, +title: String, +prompt: String, pm: List<&2, T.Mark>, lr: (List<&2, String> & List<&2, T.Mark>)) -> T.Float:
  (lrows, lmarks) = lr
  +r0 = "┌" ++ P.Box.titled(title, lw) ++ "┐"
  +rp = "│" ++ prompt ++ "│"
  +rs = "├" ++ X.Text.rep('─', lw) ++ "┤"
  +last = "└" ++ X.Text.rep('─', lw) ++ "┘"
  +lines = {r0 <> rp <> rs <> List.append(&2, String, Rows.box(lrows, "│", "│", Nil{}), [last]) : List<&2, String>}
  +border = P.Box.sides(Nat.sub(h, 2n), 1n, [0n, Nat.sub(w, 1n)], {[T.Mark{0n, 0n, w, T.Border{}}, T.Mark{2n, 0n, w, T.Border{}}, T.Mark{Nat.sub(h, 1n), 0n, w, T.Border{}}] : List<&2, T.Mark>})
  T.Float{row, col, w, h, lines, Fff.cat(border, Fff.cat({[T.Mark{0n, 1n, X.Text.cells(title), T.Title{}}] : List<&2, T.Mark>}, Fff.cat(pm, lmarks)))}

def Fff.framed.rows(+row: Nat, +col: Nat, +w: Nat, +h: Nat, +side: Bool, +lw: Nat, +pw: Nat, +ph: Nat, +title: String, +ptitle: String, +prompt: String, +pm: List<&2, T.Mark>, +lrows: List<&2, String>, +lmarks: List<&2, T.Mark>, pr: (List<&2, String> & List<&2, T.Mark>)) -> T.Float:
  (+prows, +pmarks) = pr
  X.Bool.when(T.Float, side, u => Fff.top(row, col, w, h, lw, ph, title, ptitle, prompt, pm, (lrows, lmarks), (prows, pmarks)), u => Fff.side(row, col, w, h, lw, pw, title, ptitle, prompt, pm, (lrows, lmarks), (prows, pmarks)))

# the box with a preview, right of the list or above it
def Fff.framed(+row: Nat, +col: Nat, +w: Nat, +h: Nat, +side: Bool, +lw: Nat, +pw: Nat, +ph: Nat, +title: String, +prompt: String, +pm: List<&2, T.Mark>, +lrows: List<&2, String>, +lmarks: List<&2, T.Mark>, tp: (String & P.Pane)) -> T.Float:
  (ptitle, pane) = tp
  Fff.framed.rows(row, col, w, h, side, lw, pw, ph, title, ptitle, prompt, pm, lrows, lmarks, P.Pane.draw(pane, 0n))

# the box, its list's rows and marks lr given
def Fff.box(+row: Nat, +col: Nat, +w: Nat, +h: Nat, +side: Bool, +pre: Bool, +lw: Nat, +pw: Nat, +ph: Nat, +title: String, +prompt: String, +pm: List<&2, T.Mark>, lr: (List<&2, String> & List<&2, T.Mark>), +grep: Bool, +fs: List<&2, T.Buf>, +item: Maybe<&2, T.Item>, +pv: Nat) -> T.Float:
  (+lrows, +lmarks) = lr
  X.Bool.when(T.Float, pre, u => Fff.bare(row, col, w, h, lw, title, prompt, pm, (lrows, lmarks)), u => Fff.framed(row, col, w, h, side, lw, pw, ph, title, prompt, pm, lrows, lmarks, Fff.pane(grep, fs, item, Fff.ptop(grep, fs, item, pw, pv), pw, ph)))

# fff's float in box g: the query q, the items its (all files matched, or
# grep's matches), the selected one, the list's first row (grep), the
# preview's first line (pv, from 1; 0: where fff puts it), the file the
# picker was opened from (from 1; 0: none)
def Fff.draw(g: Geo, +grep: Bool, +fs: List<&2, T.Buf>, +q: String, +its: List<&2, T.Item>, +sel: Nat, +top: Nat, +pv: Nat, +cur: Nat) -> T.Float:
  match g:
    case Geo{+row, +col, +w, +h, +side, +pre, +lw, +lh, +pw, +ph}:
      +right = Fff.right(grep, q, List.length(&2, T.Item, its), B.Files.len(fs))
      +prow = Bool.pick(Nat, Bool.or(side, Bool.not(pre)), 1n, Nat.add(ph, 2n))
      +title = Bool.pick(String, grep, " Live Grep ", " FFFiles ")
      lr = Fff.list(grep, fs, q, its, sel, top, Bool.pick(Nat, String.is_empty(q), 0n, cur), lw, lh, Nat.add(prow, 2n))
      Fff.box(row, col, w, h, side, pre, lw, pw, ph, title, Fff.prompt(right, q, lw), Fff.prompt_marks(grep, right, prow, lw), lr, grep, fs, List.get(&2, T.Item, its, sel), pv)

# fff's float on a screen of r rows and c columns
def Fff.float(+grep: Bool, +fs: List<&2, T.Buf>, +q: String, +its: List<&2, T.Item>, +sel: Nat, +top: Nat, +pv: Nat, +cur: Nat, +r: Nat, +c: Nat) -> T.Float:
  Fff.draw(Fff.geo(r, c), grep, fs, q, its, sel, top, pv, cur)
