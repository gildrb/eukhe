# eukhe.com's Neovim: commands
# ============================
#
# Searching (/ ? n N * #), links under the cursor (gf, gx), Oil's Enter,
# and the Ex commands of the command line (:).

import Base
import ./types.bend as T
import ./text.bend as X
import ./buf.bend as B
import ./find.bend as F
import ./st.bend as S
import ./core.bend as C

# the install command: the one line yy copies
def Vim.install() -> String:
  "curl -fsSL https://eukhe.com/install | sh"

# Messages
# --------

def Msg.e21() -> String:
  "E21: Cannot make changes, 'modifiable' is off"

def Msg.e35() -> String:
  "E35: No previous regular expression"

def Msg.e45() -> String:
  "E45: 'readonly' option is set (add ! to override)"

def Msg.e212() -> String:
  "E212: Can't open file for writing"

def Msg.e348() -> String:
  "E348: No string under cursor"

def Msg.e444() -> String:
  "E444: Cannot close last window"

# the message on the command line, the search count cleared
def Msg.say(+s: T.St, +m: String) -> T.St:
  S.St.set_stat(S.St.set_msg(s, m), "")

# Searching
# ---------

def Search.back(f: T.Find) -> Bool:
  match f:
    case T.Find{text, back, word}:
      back

def Search.text(f: T.Find) -> String:
  match f:
    case T.Find{text, back, word}:
      text

# the search as the command line echoes it: "/memory", "?\<AGENT\>"
def Search.say(f: T.Find, +back: Bool) -> String:
  match f:
    case T.Find{+text, b, +word}:
      Bool.pick(String, back, "?", "/") ++ Bool.pick(String, word, "\\<" ++ text ++ "\\>", text)

def Search.land(+s: T.St, +f: T.Find, +back: Bool, found: F.Found) -> T.St:
  match found:
    case F.Lost{}:
      Msg.say(s, "E486: Pattern not found: " ++ Search.text(f))
    case F.Found{+p, +wrapped}:
      +s2 = C.Win.go(C.Win.jump(s), p, False{})
      S.St.set_stat(S.St.set_msg(s2, Search.say(f, back)), F.Find.count(C.St.lines(s2), C.St.folds(s2), f, p, wrapped))

# search f from the cursor (flip: the other way than f goes); the cursor
# lands on the match, the hits are highlighted, the command line shows the
# search and its count
def Search.go(+s: T.St, +f: T.Find, +flip: Bool) -> T.St:
  +back = Bool.xor(Search.back(f), flip)
  +s2 = S.St.set_hl(S.St.set_find(s, Some{f}), True{})
  +ls = C.St.lines(s2)
  +cur = S.Win.cur(S.St.win(s2))
  +fls = C.St.folds(s2)
  +found = X.Bool.when(F.Found, back, u => F.Find.next(ls, fls, f, cur), u => F.Find.prev(ls, fls, f, cur))
  Search.land(s2, f, back, found)

def Search.again.at(+s: T.St, +flip: Bool, m: Maybe<&2, T.Find>) -> T.St:
  match m:
    case None{}:
      Msg.say(s, Msg.e35())
    case Some{f}:
      Search.go(s, f, flip)

# n and N: the last search again, the same way or the other
def Search.again(+s: T.St, +flip: Bool) -> T.St:
  Search.again.at(s, flip, S.St.find(s))

# * and #: the word under the cursor, whole, forward or back
def Search.star(+s: T.St, +back: Bool) -> T.St:
  +word = F.Word.at(C.St.text(s), C.St.col(s))
  X.Bool.when(T.St, String.is_empty(word), u => Search.go(s, T.Find{word, back, True{}}, False{}), u => Msg.say(s, Msg.e348()))

def Search.last(+s: T.St, +back: Bool, m: Maybe<&2, T.Find>) -> T.St:
  match m:
    case None{}:
      Msg.say(s, Msg.e35())
    case Some{T.Find{text, b, word}}:
      Search.go(s, T.Find{text, back, word}, False{})

# / and ? Enter: a new search; an empty one repeats the last pattern
def Search.run(+s: T.St, +text: String, +back: Bool) -> T.St:
  X.Bool.when(T.St, String.is_empty(text), u => Search.go(s, T.Find{text, back, False{}}, False{}), u => Search.last(s, back, S.St.find(s)))

# Paths and links (gf, gx, Oil's Enter)
# --------------------------------------

def Path.find.dir(+s: T.St, +dir: String, entries: List<&2, String>) -> Maybe<&2, T.St>:
  match entries:
    case Nil{}:
      None{}
    case Con{h, t}:
      Some{C.Oil.dir(s, dir)}

def Path.find.file(+s: T.St, +path: String, m: Maybe<&2, Nat>) -> Maybe<&2, T.St>:
  match m:
    case Some{i}:
      Some{C.Win.open_file(s, i)}
    case None{}:
      +dir = Bool.pick(String, Bool.or(String.is_empty(path), B.Path.is_dir(path)), path, path ++ "/")
      Path.find.dir(s, dir, B.Oil.collect(S.St.files(s), dir, True{}, B.Oil.collect(S.St.files(s), dir, False{}, Nil{})))

# the file or folder at path ("." and "" are the root): a folder opens in
# Oil, a file where its cursor was left; None when there is neither
def Path.find(+s: T.St, +path: String) -> Maybe<&2, T.St>:
  +p = Bool.pick(String, Bool.or(String.eq(path, "."), String.eq(path, "./")), "", path)
  Path.find.file(s, p, B.Files.find(S.St.files(s), p))

def Link.big.go(s: String, +c: Nat, +i: Nat, +acc: String, +ended: Bool) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{+h, +t}:
      +blank = Nat.is_eq(X.Char.cls(h, True{}), 0n)
      X.Bool.when(String, blank, u => Link.big.go(t, c, 1n+i, SCon{h, acc}, False{}), u => X.Bool.when(String, Nat.is_gt(i, c), u => Link.big.go(t, c, 1n+i, SNil{}, False{}), u => String.reverse(acc)))

# the WORD under column c: the run of non-blank characters holding it
def Link.big(line: String, +c: Nat) -> String:
  Link.big.go(line, c, 0n, SNil{}, False{})

def Link.inner.go(s: String, +acc: String, +open: Bool) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{+h, +t}:
      X.Bool.when(String, open, u => X.Bool.when(String, Char.is_eq(h, '('), u => Link.inner.go(t, acc, False{}), u => Link.inner.go(t, SNil{}, True{})), u => X.Bool.when(String, Char.is_eq(h, ')'), u => Link.inner.go(t, SCon{h, acc}, True{}), u => String.reverse(acc)))

# the brackets and quotes Link.trim drops before a WORD
def Link.opens(+c: Char) -> Bool:
  Bool.or(Char.is_eq(c, '('), Bool.or(Char.is_eq(c, '['), Bool.or(Char.is_eq(c, '<'), Bool.or(Char.is_eq(c, '`'), Char.is_eq(c, '"')))))

# the brackets, quotes and punctuation Link.trim drops after a WORD
def Link.closes(+c: Char) -> Bool:
  Bool.or(Char.is_eq(c, ')'), Bool.or(Char.is_eq(c, ']'), Bool.or(Char.is_eq(c, '>'), Bool.or(Char.is_eq(c, '.'), Bool.or(Char.is_eq(c, ','), Bool.or(Char.is_eq(c, ':'), Bool.or(Char.is_eq(c, ';'), Bool.or(Char.is_eq(c, '`'), Char.is_eq(c, '"')))))))))

def Link.trim.l(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, +t}:
      X.Bool.when(String, Link.opens(h), u => SCon{h, t}, u => Link.trim.l(t))

def Link.trim.rl(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, +t}:
      X.Bool.when(String, Link.closes(h), u => SCon{h, t}, u => Link.trim.rl(t))

def Link.trim.r(+s: String) -> String:
  String.reverse(Link.trim.rl(String.reverse(s)))

def Link.trim(+w: String) -> String:
  String.reverse(Link.trim.l(String.reverse(Link.trim.r(Link.trim.l(w)))))

# what a WORD points to: the URL or path inside a Markdown link's "(..)",
# else the WORD without the brackets and punctuation around it
def Link.target(+w: String) -> String:
  +inner = Link.inner.go(w, SNil{}, False{})
  Bool.pick(String, String.is_empty(inner), Link.trim(w), inner)

# whether s is a web address
def Link.is_url(+s: String) -> Bool:
  Bool.or(X.Text.prefix("https://", s), X.Text.prefix("http://", s))

def Link.gf.at(+s: T.St, +t: String, m: Maybe<&2, T.St>) -> T.St:
  match m:
    case None{}:
      Msg.say(s, "E447: Can't find file \"" ++ t ++ "\" in path")
    case Some{s2}:
      s2

# gf: the file or folder under the cursor
def Link.gf(+s: T.St) -> T.St:
  +t = Link.target(Link.big(C.St.text(s), C.St.col(s)))
  Link.gf.at(s, t, Path.find(s, t))

# gx: the web address under the cursor opens in the browser; a path, as
# gf (a folder's listing holds no web address: only file windows open one)
def Link.gx(+s: T.St) -> T.Step:
  +t = Link.target(Link.big(C.St.text(s), C.St.col(s)))
  X.Bool.when(T.Step, Bool.and(C.St.on_file(s), Link.is_url(t)), u => T.Step{Link.gf(s), T.Nothing{}}, u => T.Step{s, T.OpenUrl{t}})

def Oil.enter.at(+s: T.St, +n: Nat, t: T.Tgt) -> T.St:
  match t:
    case T.File{i}:
      +l = Nat.add(C.St.line(s), n)
      C.Win.go(s, T.Pos{l, X.Text.first(B.Lines.at(C.St.lines(s), l))}, False{})
    case T.Dir{+path}:
      +entry = C.St.text(s)
      X.Bool.when(T.St, String.eq(entry, "../"), u => X.Bool.when(T.St, String.is_empty(entry), u => Link.gf.at(s, path ++ entry, Path.find(s, path ++ entry)), u => s), u => X.Bool.when(T.St, String.is_empty(path), u => C.Oil.dir(s, B.Path.up(path)), u => s))

# Enter: in Oil, the entry under the cursor opens ("../": the folder
# above; in the root, nothing); elsewhere, + (the next line's first
# non-blank)
def Oil.enter(+s: T.St, +n: Nat) -> T.St:
  Oil.enter.at(s, n, S.Win.tgt(S.St.win(s)))

# Ex commands
# -----------

# the command line's text, its leading and trailing blanks dropped
def Ex.trim(s: String) -> String:
  match s:
    case SCon{' ', t}:
      Ex.trim(t)
    case t:
      t

def Ex.strip(+s: String) -> String:
  String.reverse(Ex.trim(String.reverse(Ex.trim(s))))

def Ex.names() -> List<&2, String>:
  ["q", "q!", "quit", "qa", "qa!", "qall", "wq", "x", "xa", "w", "write", "w!",
   "noh", "nohlsearch", "Oil", "bn", "bnext", "bp", "bprevious",
   "set nu", "set number", "set nonu", "set nonumber", "set rnu", "set relativenumber",
   "set nornu", "set norelativenumber", "set hls", "set hlsearch", "set nohls", "set nohlsearch"]

# the position of s in xs; its length when absent
def Ex.find(xs: List<&2, String>, +s: String, +n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{x, rest}:
      X.Bool.when(Nat, String.eq(x, s), u => Ex.find(rest, s, 1n+n), u => n)

def Opts.set(o: T.Opts, +which: Nat, +on: Bool) -> T.Opts:
  match o:
    case T.Opts{+nu, +rnu, +hls}:
      Bool.pick(T.Opts, Nat.is_eq(which, 0n), T.Opts{on, rnu, hls}, Bool.pick(T.Opts, Nat.is_eq(which, 1n), T.Opts{nu, on, hls}, T.Opts{nu, rnu, on}))

# a setting changed: the window refits, the number column may change width
def Ex.set(+s: T.St, +which: Nat, +on: Bool) -> T.St:
  +s2 = S.St.set_opts(s, Opts.set(S.St.opts(s), which, on))
  C.Win.settle(Bool.pick(T.St, Nat.is_eq(which, 2n), S.St.set_hl(s2, Bool.and(on, S.St.hl(s2))), s2))

def Ex.here(t: T.Tgt) -> Nat:
  match t:
    case T.File{i}:
      i
    case T.Dir{path}:
      0n

# the next (or previous) opened buffer in file order (:bn :bp)
def Ex.cycle(+s: T.St, +back: Bool) -> T.St:
  +os = List.sort(~Nat, ~Nat.is_le, S.St.opened(s))
  +here = Ex.here(S.Win.tgt(S.St.win(s)))
  +after = F.Cols.first_after(os, here)
  +before = F.Cols.last_before(os, here, None{})
  +first = List.head(&2, Nat, os)
  +lastb = F.Cols.last(os, None{})
  C.Win.to(s, Bool.pick(Maybe<&2, Nat>, back, Maybe.or(&2, Nat, before, lastb), Maybe.or(&2, Nat, after, first)))

def Ex.named(+s: T.St, +cmd: String, n: Nat) -> T.St:
  match n:
    case 0n:
      Msg.say(s, Msg.e444())
    case 1n:
      Msg.say(s, Msg.e444())
    case 2n:
      Msg.say(s, Msg.e444())
    case 3n:
      Msg.say(s, Msg.e444())
    case 4n:
      Msg.say(s, Msg.e444())
    case 5n:
      Msg.say(s, Msg.e444())
    case 6n:
      Msg.say(s, Msg.e45())
    case 7n:
      Msg.say(s, Msg.e45())
    case 8n:
      Msg.say(s, Msg.e45())
    case 9n:
      Msg.say(s, Msg.e45())
    case 10n:
      Msg.say(s, Msg.e45())
    case 11n:
      Msg.say(s, Msg.e212())
    case 12n:
      S.St.set_hl(s, False{})
    case 13n:
      S.St.set_hl(s, False{})
    case 14n:
      C.Oil.here(s)
    case 15n:
      Ex.cycle(s, False{})
    case 16n:
      Ex.cycle(s, False{})
    case 17n:
      Ex.cycle(s, True{})
    case 18n:
      Ex.cycle(s, True{})
    case 19n:
      Ex.set(s, 0n, True{})
    case 20n:
      Ex.set(s, 0n, True{})
    case 21n:
      Ex.set(s, 0n, False{})
    case 22n:
      Ex.set(s, 0n, False{})
    case 23n:
      Ex.set(s, 1n, True{})
    case 24n:
      Ex.set(s, 1n, True{})
    case 25n:
      Ex.set(s, 1n, False{})
    case 26n:
      Ex.set(s, 1n, False{})
    case 27n:
      Ex.set(s, 2n, True{})
    case 28n:
      Ex.set(s, 2n, True{})
    case 29n:
      Ex.set(s, 2n, False{})
    case 30n:
      Ex.set(s, 2n, False{})
    case 31n+p:
      Bool.pick(T.St, String.is_empty(cmd), s, Msg.say(s, "E492: Not an editor command: " ++ cmd))

def Ex.edit(+s: T.St, +cmd: String, +e: Bool, +edit: Bool, +oil: Bool) -> T.St:
  +path = Ex.strip(X.Text.drop(cmd, Bool.pick(Nat, e, 2n, Bool.pick(Nat, edit, 5n, 4n))))
  X.Bool.when(T.St, Bool.or(e, Bool.or(edit, oil)), u => Ex.named(s, cmd, Ex.find(Ex.names(), cmd, 0n)), u => Link.gf.at(s, path, Path.find(s, path)))

def Ex.num(+s: T.St, +cmd: String, m: Maybe<&2, Nat>) -> T.St:
  match m:
    case Some{n}:
      C.Win.go_line(C.Win.jump(s), Nat.sub(n, 1n))
    case None{}:
      Ex.edit(s, cmd, X.Text.prefix("e ", cmd), X.Text.prefix("edit ", cmd), X.Text.prefix("Oil ", cmd))

# what :text does; the command line keeps showing it unless the command
# says something else
def Ex.run(+s: T.St, +text: String) -> T.St:
  +cmd = Ex.strip(text)
  Ex.num(Msg.say(s, Bool.pick(String, String.is_empty(cmd), "", ":" ++ text)), cmd, Nat.read(cmd))

# the command line run
def Line.run(+s: T.St, kind: T.Line, +text: String) -> T.St:
  match kind:
    case T.Colon{}:
      Ex.run(s, text)
    case T.Slash{}:
      Search.run(s, text, False{})
    case T.Quest{}:
      Search.run(s, text, True{})
