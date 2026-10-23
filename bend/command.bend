# command: the paths of the slash commands (the table of
# crates/eukhe-types/src/slash_commands.rs, with the argument lists the
# interface adds; crates/eukhe-tui/src/command_paths.rs builds it). A
# line is the text after the leading '/', as char codes; a word is the
# text between two spaces (code 32). A path is a list of names: a
# command, a subcommand, an argument. laws/command.bend states
# the laws; bend/ffi_command.bend is the entry of the compiled core.
#
# The table is flat: one entry per declared path, in menu order. An
# entry names its path (canonical, lowercase), the aliases of its last
# name, and three flags:
#   run   Enter on the bare path runs it (its default)
#   free  a word that names no child is the start of the path's
#         argument text
#   arg   the path expects text after it (a completion leaves a space)
#
# resolve: the path a submitted line runs, the menu a bare path opens,
# an unknown word, or no command. menu: the rows a typed line shows
# below its last word (the command names are the interface's fuzzy
# ranking). key: what Tab or Enter does to the line, with or without a
# selected row.

import Base

type Ent is Data:
  Ent{path: List<&2, List<&2, Nat>>, alias: List<&2, List<&2, Nat>>, run: Bool, free: Bool, arg: Bool}

def Ent.path(e: Ent) -> List<&2, List<&2, Nat>>:
  match e:
    case Ent{p, a, r, f, g}:
      p

def Ent.alias(e: Ent) -> List<&2, List<&2, Nat>>:
  match e:
    case Ent{p, a, r, f, g}:
      a

def Ent.run(e: Ent) -> Bool:
  match e:
    case Ent{p, a, r, f, g}:
      r

def Ent.free(e: Ent) -> Bool:
  match e:
    case Ent{p, a, r, f, g}:
      f

def Ent.arg(e: Ent) -> Bool:
  match e:
    case Ent{p, a, r, f, g}:
      g

# Where a walk over the words of a line stands: at the root, at a
# declared path (with its entry), in a path's argument text, at an
# unknown word below a path, or at a first word that is no command.
type St is Data:
  Top{}
  Walk{path: List<&2, List<&2, Nat>>, ent: Ent}
  Rest{path: List<&2, List<&2, Nat>>, words: List<&2, List<&2, Nat>>}
  Lost{path: List<&2, List<&2, Nat>>, word: List<&2, Nat>}
  Stray{}

# What a submitted line does: run a path with its argument text, open
# the menu of a bare path that has no default, report an unknown word
# below a path, or name no command (the interface's own handling).
type Res is Data:
  Runs{path: List<&2, List<&2, Nat>>, args: List<&2, Nat>}
  Opens{path: List<&2, List<&2, Nat>>}
  Unknown{path: List<&2, List<&2, Nat>>, word: List<&2, Nat>}
  NoCmd{}

# The menu of a typed line: the command names (ranked by the
# interface), the rows of the children of a path (their places in the
# table), or none.
type Menu is Data:
  Names{}
  Kids{path: List<&2, List<&2, Nat>>, items: List<&2, Nat>}
  Shut{}

# A selected row of the open menu (its place in the table), or none.
type Sel is Data:
  NoRow{}
  Row{i: Nat}

type Press is Data:
  Tab{}
  Enter{}

# A key's answer: the new line, whether the menu opens at it, and
# whether the line is submitted.
type Out is Data:
  Out{line: List<&2, Nat>, open: Bool, submit: Bool}

# Words
# -----

# the space between two words
def space() -> Nat:
  32n

def low.pick(b: Bool, c: Nat) -> Nat:
  match b:
    case True{}:
      Nat.add(c, 32n)
    case False{}:
      c

# a char in lowercase (A-Z only: the names are ASCII)
def low(+c: Nat) -> Nat:
  low.pick(Bool.and(Nat.is_le(65n, c), Nat.is_le(c, 90n)), c)

def lows(w: List<&2, Nat>) -> List<&2, Nat>:
  match w:
    case Nil{}:
      Nil{}
    case Con{+c, r}:
      low(c) <> lows(r)

def same(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, ys}:
      False{}
    case Con{x, xs} Nil{}:
      False{}
    case Con{x, xs} Con{y, ys}:
      Bool.and(Nat.is_eq(x, y), same(xs, ys))

def same_path(a: List<&2, List<&2, Nat>>, b: List<&2, List<&2, Nat>>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, ys}:
      False{}
    case Con{x, xs} Nil{}:
      False{}
    case Con{x, xs} Con{y, ys}:
      Bool.and(same(x, y), same_path(xs, ys))

# x is a prefix of n
def starts(x: List<&2, Nat>, n: List<&2, Nat>) -> Bool:
  match x n:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, ys}:
      True{}
    case Con{a, as} Nil{}:
      False{}
    case Con{a, as} Con{y, ys}:
      Bool.and(Nat.is_eq(a, y), starts(as, ys))

# one of xs is x
def has(xs: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(same(x, y), has(rest, x))

# one of xs starts with x
def has_start(xs: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(starts(x, y), has_start(rest, x))

def put_word(c: Nat, ws: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match ws:
    case Nil{}:
      [[c]]
    case Con{w, rest}:
      (c <> w) <> rest

def words.at(b: Bool, c: Nat, ws: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match b:
    case True{}:
      Nil{} <> ws
    case False{}:
      put_word(c, ws)

# the words of a line, split at every space (an empty word between two
# spaces stays: free text keeps its spacing); never empty
def words(cs: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match cs:
    case Nil{}:
      [Nil{}]
    case Con{+c, r}:
      words.at(Nat.is_eq(c, 32n), c, words(r))

# w, then each word of ws after a space
def join.go(ws: List<&2, List<&2, Nat>>, w: List<&2, Nat>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      w
    case Con{v, rest}:
      List.append(&2, Nat, w, 32n <> join.go(rest, v))

# the words of ws with a space between two words
def join(ws: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, rest}:
      join.go(rest, w)

def cut.cons(w: List<&2, Nat>, r: List<&2, List<&2, Nat>> & List<&2, Nat>) -> List<&2, List<&2, Nat>> & List<&2, Nat>:
  (a, b) = r
  (w <> a, b)

def cut.go(ws: List<&2, List<&2, Nat>>, w: List<&2, Nat>) -> List<&2, List<&2, Nat>> & List<&2, Nat>:
  match ws:
    case Nil{}:
      (Nil{}, w)
    case Con{v, rest}:
      cut.cons(w, cut.go(rest, v))

# the words before the last, and the last
def cut(ws: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>> & List<&2, Nat>:
  match ws:
    case Nil{}:
      (Nil{}, Nil{})
    case Con{w, rest}:
      cut.go(rest, w)

# The table
# ---------

# p is q and one more name
def kid(q: List<&2, List<&2, Nat>>, p: List<&2, List<&2, Nat>>) -> Bool:
  match q p:
    case Nil{} Nil{}:
      False{}
    case Nil{} Con{y, ys}:
      List.is_empty(&2, List<&2, Nat>, ys)
    case Con{x, xs} Nil{}:
      False{}
    case Con{x, xs} Con{y, ys}:
      Bool.and(same(x, y), kid(xs, ys))

def last.go(p: List<&2, List<&2, Nat>>, x: List<&2, Nat>) -> List<&2, Nat>:
  match p:
    case Nil{}:
      x
    case Con{y, rest}:
      last.go(rest, y)

# the last name of a path (none for the root)
def last(p: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match p:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      last.go(rest, x)

def pick(b: Bool, e: Ent, r: Maybe<&2, Ent>) -> Maybe<&2, Ent>:
  match b:
    case True{}:
      Some{e}
    case False{}:
      r

# the first entry of path p
def by_path(t: List<&2, Ent>, +p: List<&2, List<&2, Nat>>) -> Maybe<&2, Ent>:
  match t:
    case Nil{}:
      None{}
    case Con{+e, rest}:
      pick(same_path(Ent.path(e), p), e, by_path(rest, p))

# the first child of q with the alias x
def by_alias(t: List<&2, Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> Maybe<&2, Ent>:
  match t:
    case Nil{}:
      None{}
    case Con{+e, rest}:
      pick(Bool.and(kid(q, Ent.path(e)), has(Ent.alias(e), x)), e, by_alias(rest, q, x))

def search.alias(m: Maybe<&2, Ent>, t: List<&2, Ent>, q: List<&2, List<&2, Nat>>, x: List<&2, Nat>) -> Maybe<&2, Ent>:
  match m:
    case Some{e}:
      Some{e}
    case None{}:
      by_alias(t, q, x)

# the child of q a word x (lowercase) names: by its name first, then by
# an alias
def search(+t: List<&2, Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> Maybe<&2, Ent>:
  search.alias(by_path(t, List.append(&2, List<&2, Nat>, q, [x])), t, q, x)

# q has a child
def kids.any(t: List<&2, Ent>, +q: List<&2, List<&2, Nat>>) -> Bool:
  match t:
    case Nil{}:
      False{}
    case Con{e, rest}:
      Bool.or(kid(q, Ent.path(e)), kids.any(rest, q))

# Enter on the bare path of e runs it: it has a default, or no child
def done(+t: List<&2, Ent>, +e: Ent) -> Bool:
  Bool.or(Ent.run(e), Bool.not(kids.any(t, Ent.path(e))))

# The walk
# --------

def step.top(m: Maybe<&2, Ent>) -> St:
  match m:
    case Some{+e}:
      Walk{Ent.path(e), e}
    case None{}:
      Stray{}

def step.miss(free: Bool, q: List<&2, List<&2, Nat>>, w: List<&2, Nat>) -> St:
  match free:
    case True{}:
      Rest{q, [w]}
    case False{}:
      Lost{q, w}

def step.walk(m: Maybe<&2, Ent>, q: List<&2, List<&2, Nat>>, free: Bool, w: List<&2, Nat>) -> St:
  match m:
    case Some{+e}:
      Walk{Ent.path(e), e}
    case None{}:
      step.miss(free, q, w)

# a word that is not empty
def step.word(s: St, +t: List<&2, Ent>, +w: List<&2, Nat>) -> St:
  match s:
    case Top{}:
      step.top(search(t, Nil{}, lows(w)))
    case Walk{+q, e}:
      step.walk(search(t, q, lows(w)), q, Ent.free(e), w)
    case Rest{q, ws}:
      Rest{q, List.append(&2, List<&2, Nat>, ws, [w])}
    case Lost{q, x}:
      Lost{q, x}
    case Stray{}:
      Stray{}

# an empty word (two spaces in a row): argument text keeps it, a walk
# skips it
def step.empty(s: St) -> St:
  match s:
    case Top{}:
      Top{}
    case Walk{q, e}:
      Walk{q, e}
    case Rest{q, ws}:
      Rest{q, List.append(&2, List<&2, Nat>, ws, [Nil{}])}
    case Lost{q, x}:
      Lost{q, x}
    case Stray{}:
      Stray{}

def step(s: St, +t: List<&2, Ent>, w: List<&2, Nat>) -> St:
  match w:
    case Nil{}:
      step.empty(s)
    case Con{c, r}:
      step.word(s, t, c <> r)

def walk(ws: List<&2, List<&2, Nat>>, +t: List<&2, Ent>, s: St) -> St:
  match ws:
    case Nil{}:
      s
    case Con{w, rest}:
      walk(rest, t, step(s, t, w))

# resolve
# -------

def finish.at(d: Bool, q: List<&2, List<&2, Nat>>) -> Res:
  match d:
    case True{}:
      Runs{q, Nil{}}
    case False{}:
      Opens{q}

def finish(s: St, +t: List<&2, Ent>) -> Res:
  match s:
    case Top{}:
      NoCmd{}
    case Walk{q, +e}:
      finish.at(done(t, e), q)
    case Rest{q, ws}:
      Runs{q, join(ws)}
    case Lost{q, w}:
      Unknown{q, w}
    case Stray{}:
      NoCmd{}

# what a submitted line does
def resolve(+t: List<&2, Ent>, line: List<&2, Nat>) -> Res:
  finish(walk(words(line), t, Top{}), t)

# menu
# ----

def items.at(b: Bool, i: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      i <> r
    case False{}:
      r

# e's last name, or one of its aliases, starts with x
def opens_with(+x: List<&2, Nat>, +e: Ent) -> Bool:
  Bool.or(starts(x, last(Ent.path(e))), has_start(Ent.alias(e), x))

# the places (from i) of the children of q that start with x
def items(t: List<&2, Ent>, +i: Nat, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> List<&2, Nat>:
  match t:
    case Nil{}:
      Nil{}
    case Con{+e, rest}:
      items.at(Bool.and(kid(q, Ent.path(e)), opens_with(x, e)), i, items(rest, 1n+i, q, x))

def menu.at(s: St, +t: List<&2, Ent>, p: List<&2, Nat>) -> Menu:
  match s:
    case Top{}:
      Shut{}
    case Walk{+q, e}:
      Kids{q, items(t, 0n, q, lows(p))}
    case Rest{q, ws}:
      Shut{}
    case Lost{q, w}:
      Shut{}
    case Stray{}:
      Shut{}

def menu.go(d: List<&2, List<&2, Nat>>, p: List<&2, Nat>, +t: List<&2, Ent>) -> Menu:
  match d:
    case Nil{}:
      Names{}
    case Con{w, rest}:
      menu.at(walk(w <> rest, t, Top{}), t, p)

def menu.cut(c: List<&2, List<&2, Nat>> & List<&2, Nat>, +t: List<&2, Ent>) -> Menu:
  (d, p) = c
  menu.go(d, p, t)

# the menu of a typed line
def menu(+t: List<&2, Ent>, line: List<&2, Nat>) -> Menu:
  menu.cut(cut(words(line)), t)

# key
# ---

# the line of a path, then a space when b
def spaced(b: Bool, l: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      List.append(&2, Nat, l, [32n])
    case False{}:
      l

def key.enter(r: Res, line: List<&2, Nat>) -> Out:
  match r:
    case Runs{q, a}:
      Out{line, False{}, True{}}
    case Opens{q}:
      Out{List.append(&2, Nat, join(q), [32n]), True{}, False{}}
    case Unknown{q, w}:
      Out{line, False{}, True{}}
    case NoCmd{}:
      Out{line, False{}, True{}}

# no row: Tab opens the menu of the line; Enter submits it unless it is
# a bare path with no default, whose menu opens instead
def key.bare(k: Press, +t: List<&2, Ent>, +line: List<&2, Nat>) -> Out:
  match k:
    case Tab{}:
      Out{line, True{}, False{}}
    case Enter{}:
      key.enter(resolve(t, line), line)

# Tab on a row: its path, a space when it has children or expects text,
# and its menu opens when it has children
def key.tab(+kids: Bool, arg: Bool, l: List<&2, Nat>) -> Out:
  Out{spaced(Bool.or(kids, arg), l), kids, False{}}

def key.typed(d: Bool, l: List<&2, Nat>, line: List<&2, Nat>) -> Out:
  match d:
    case True{}:
      Out{line, False{}, True{}}
    case False{}:
      Out{List.append(&2, Nat, l, [32n]), True{}, False{}}

def key.fresh(kids: Bool, arg: Bool, l: List<&2, Nat>) -> Out:
  match kids:
    case True{}:
      Out{List.append(&2, Nat, l, [32n]), True{}, False{}}
    case False{}:
      match arg:
        case True{}:
          Out{List.append(&2, Nat, l, [32n]), False{}, False{}}
        case False{}:
          Out{l, False{}, True{}}

# Enter on a row. Typed in full (its name or an alias): a bare path that
# runs is submitted, any other opens its menu. Typed in part: the row
# completes; it descends into its children, waits for text it expects,
# or is submitted.
def key.row_enter(typed: Bool, d: Bool, kids: Bool, arg: Bool, l: List<&2, Nat>, line: List<&2, Nat>) -> Out:
  match typed:
    case True{}:
      key.typed(d, l, line)
    case False{}:
      key.fresh(kids, arg, l)

# the word x names e: its last name or an alias
def names(+x: List<&2, Nat>, +e: Ent) -> Bool:
  Bool.or(same(x, last(Ent.path(e))), has(Ent.alias(e), x))

def key.pick(k: Press, +e: Ent, +t: List<&2, Ent>, line: List<&2, Nat>, p: List<&2, Nat>) -> Out:
  match k:
    case Tab{}:
      key.tab(kids.any(t, Ent.path(e)), Ent.arg(e), join(Ent.path(e)))
    case Enter{}:
      key.row_enter(names(lows(p), e), done(t, e), kids.any(t, Ent.path(e)), Ent.arg(e), join(Ent.path(e)), line)

def key.row(m: Maybe<&2, Ent>, k: Press, +t: List<&2, Ent>, +line: List<&2, Nat>, p: List<&2, Nat>) -> Out:
  match m:
    case None{}:
      key.bare(k, t, line)
    case Some{+e}:
      key.pick(k, e, t, line, p)

def row.kid(b: Bool, e: Ent) -> Maybe<&2, Ent>:
  match b:
    case True{}:
      Some{e}
    case False{}:
      None{}

def row.of(m: Maybe<&2, Ent>, +q: List<&2, List<&2, Nat>>) -> Maybe<&2, Ent>:
  match m:
    case None{}:
      None{}
    case Some{+e}:
      row.kid(kid(q, Ent.path(e)), e)

# the selected row, when it is a child of q
def row(sel: Sel, +t: List<&2, Ent>, +q: List<&2, List<&2, Nat>>) -> Maybe<&2, Ent>:
  match sel:
    case NoRow{}:
      None{}
    case Row{i}:
      row.of(List.get(&2, Ent, t, i), q)

def key.at(s: St, +t: List<&2, Ent>, +line: List<&2, Nat>, p: List<&2, Nat>, sel: Sel, k: Press) -> Out:
  match s:
    case Top{}:
      key.row(row(sel, t, Nil{}), k, t, line, p)
    case Walk{+q, e}:
      key.row(row(sel, t, q), k, t, line, p)
    case Rest{q, ws}:
      key.bare(k, t, line)
    case Lost{q, w}:
      key.bare(k, t, line)
    case Stray{}:
      key.bare(k, t, line)

def key.cut(c: List<&2, List<&2, Nat>> & List<&2, Nat>, +t: List<&2, Ent>, +line: List<&2, Nat>, sel: Sel, k: Press) -> Out:
  (d, p) = c
  key.at(walk(d, t, Top{}), t, line, p, sel, k)

# what Tab or Enter does to a typed line (sel: the selected row)
def key(+t: List<&2, Ent>, +line: List<&2, Nat>, sel: Sel, k: Press) -> Out:
  key.cut(cut(words(line)), t, line, sel, k)
