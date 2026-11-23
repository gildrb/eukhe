# eukhe.com's Neovim: finding
# ===========================
#
# Search (/ ? n N * #), grep across files and the pickers' lists. Patterns
# are literal text. With 'ignorecase' and 'smartcase' a pattern without a
# capital letter matches either case.

import Base
import ./types.bend as T
import ./text.bend as X
import ./buf.bend as B

# Matches on a line
# -----------------

# whether a match ending before s is a whole word's end: s does not go
# on with a word character
def Hit.end_ok(s: String, +word: Bool) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{h, t}:
      Bool.or(Bool.not(word), Nat.is_ne(X.Char.cls(h, False{}), 2n))

def Hit.go(s: String, +pat: String, +plen: Nat, +word: Bool, +prev: Nat, +c: Nat, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match s:
    case SNil{}:
      List.reverse(&2, Nat, acc)
    case SCon{+h, +t}:
      +start = Bool.or(Bool.not(word), Nat.is_ne(prev, 2n))
      +hit = Bool.and(start, Bool.and(X.Text.prefix(pat, SCon{h, t}), Hit.end_ok(X.Text.drop(SCon{h, t}, plen), word)))
      Hit.go(t, pat, plen, word, X.Char.cls(h, False{}), 1n+c, Bool.pick(List<&2, Nat>, hit, c <> acc, acc))

# the columns where pat matches line, left to right; none for an empty
# pattern. fold: compare in lower case (pat already folded); word: whole
# words only
# the columns where pat starts in s, from column c (no word test)
def Hit.plain(s: String, +pat: String, +c: Nat, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match s:
    case SNil{}:
      List.reverse(&2, Nat, acc)
    case SCon{+h, +t}:
      Hit.plain(t, pat, 1n+c, Bool.pick(List<&2, Nat>, X.Text.prefix(pat, SCon{h, t}), c <> acc, acc))

def Hit.line(+line: String, +fline: String, +pat: String, +fold: Bool, +word: Bool) -> List<&2, Nat>:
  match pat:
    case SNil{}:
      Nil{}
    case SCon{+h, +t}:
      +s = Bool.pick(String, fold, fline, line)
      X.Bool.when(List<&2, Nat>, String.contains(s, SCon{h, t}), u => Nil{}, u => X.Bool.when(List<&2, Nat>, word, u => Hit.plain(s, SCon{h, t}, 0n, Nil{}), u => Hit.go(s, SCon{h, t}, X.Text.len(SCon{h, t}), word, 0n, 0n, Nil{})))

# whether a search folds case: 'ignorecase' with 'smartcase' (a pattern
# with a capital matches its case), but * and # always fold
def Find.fold(+text: String, +word: Bool) -> Bool:
  Bool.or(word, Bool.not(X.Text.has_upper(text)))

def Find.pat(+text: String, +word: Bool) -> String:
  Bool.pick(String, Find.fold(text, word), X.Text.fold(text), text)

# the columns where search f matches line (fline: it in lower case)
def Find.hits(f: T.Find, line: String, fline: String) -> List<&2, Nat>:
  match f:
    case T.Find{+text, back, +word}:
      Hit.line(line, fline, Find.pat(text, word), Find.fold(text, word), word)

# the matches at columns before lim among cs (k) and all of them (n),
# added to k and n
def Count.add(cs: List<&2, Nat>, +lim: Nat, +k: Nat, +n: Nat) -> (Nat & Nat):
  match cs:
    case Nil{}:
      (k, n)
    case Con{+c, t}:
      Count.add(t, lim, Bool.pick(Nat, Nat.is_lt(c, lim), 1n+k, k), 1n+n)

def Count.step(cs: List<&2, Nat>, +lim: Nat, kn: (Nat & Nat)) -> (Nat & Nat):
  match kn:
    case (k, n):
      Count.add(cs, lim, k, n)

def Count.go(ls: List<&2, String>, fls: List<&2, String>, +f: T.Find, +l: Nat, +line: Nat, +col: Nat, kn: (Nat & Nat)) -> (Nat & Nat):
  match ls fls:
    case Nil{} _:
      kn
    case _ Nil{}:
      kn
    case Con{h, t} Con{fh, ft}:
      +lim = Bool.pick(Nat, Nat.is_lt(l, line), 4294967295n, Bool.pick(Nat, Nat.is_eq(l, line), 1n+col, 0n))
      Count.go(t, ft, f, 1n+l, line, col, Count.step(Find.hits(f, h, fh), lim, kn))

def Count.show(+k: Nat) -> String:
  Bool.pick(String, Nat.is_gt(k, 99n), ">99", Nat.show(k))

def Count.say(kn: (Nat & Nat), +wrapped: Bool) -> String:
  match kn:
    case (k, n):
      Bool.pick(String, wrapped, "W ", "") ++ "[" ++ Count.show(k) ++ "/" ++ Count.show(n) ++ "]"

# the search count shown right of the command line ('shortmess' without
# S): "[k/n]", the match at the cursor among all of the buffer's; "W "
# before it when the search wrapped around
def Find.count(ls: List<&2, String>, fls: List<&2, String>, +f: T.Find, p: T.Pos, +wrapped: Bool) -> String:
  match p:
    case T.Pos{line, col}:
      Count.say(Count.go(ls, fls, f, 0n, line, col, (0n, 0n)), wrapped)

# Searching a buffer
# ------------------

def Cols.first_after(cs: List<&2, Nat>, +c: Nat) -> Maybe<&2, Nat>:
  match cs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      X.Bool.when(Maybe<&2, Nat>, Nat.is_gt(h, c), u => Cols.first_after(t, c), u => Some{h})

def Cols.last_before(cs: List<&2, Nat>, +c: Nat, +best: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match cs:
    case Nil{}:
      best
    case Con{+h, t}:
      X.Bool.when(Maybe<&2, Nat>, Nat.is_lt(h, c), u => best, u => Cols.last_before(t, c, Some{h}))

def Cols.last(cs: List<&2, Nat>, +best: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match cs:
    case Nil{}:
      best
    case Con{h, t}:
      Cols.last(t, Some{h})

def Find.pick(m: Maybe<&2, Nat>, +l: Nat, rest: Unit -> Maybe<&2, T.Pos>) -> Maybe<&2, T.Pos>:
  match m:
    case None{}:
      rest(Unit{})
    case Some{c}:
      Some{T.Pos{l, c}}

# the first line, from line l down in ls, with a match: its line and first
# column
def Find.down(ls: List<&2, String>, fls: List<&2, String>, +f: T.Find, +l: Nat) -> Maybe<&2, T.Pos>:
  match ls fls:
    case Nil{} _:
      None{}
    case _ Nil{}:
      None{}
    case Con{h, t} Con{fh, ft}:
      Find.pick(List.head(&2, Nat, Find.hits(f, h, fh)), l, u => Find.down(t, ft, f, 1n+l))

# the first line, from line l up in ls (lines nearest first), with a
# match: its line and last column
def Find.up(ls: List<&2, String>, fls: List<&2, String>, +f: T.Find, +l: Nat) -> Maybe<&2, T.Pos>:
  match ls fls:
    case Nil{} _:
      None{}
    case _ Nil{}:
      None{}
    case Con{h, t} Con{fh, ft}:
      Find.pick(Cols.last(Find.hits(f, h, fh), None{}), l, u => Find.up(t, ft, f, Nat.sub(l, 1n)))

# where a search goes from p, and whether it wrapped around the buffer's
# end ('wrapscan'); None when nothing matches
type Found is Data:
  NoHit{}
  Found{pos: T.Pos, wrapped: Bool}

def Found.of(m: Maybe<&2, T.Pos>, +wrapped: Bool, rest: Unit -> Found) -> Found:
  match m:
    case None{}:
      rest(Unit{})
    case Some{p}:
      Found{p, wrapped}

def Found.col(m: Maybe<&2, Nat>, +line: Nat, rest: Unit -> Found) -> Found:
  match m:
    case None{}:
      rest(Unit{})
    case Some{c}:
      Found{T.Pos{line, c}, False{}}

# a search forward from p: the line's matches after the cursor, the lines
# below, then from the top down to the cursor's line
def Find.next(+ls: List<&2, String>, +fls: List<&2, String>, +f: T.Find, p: T.Pos) -> Found:
  match p:
    case T.Pos{+line, +col}:
      +here = Cols.first_after(Find.hits(f, B.Lines.at(ls, line), B.Lines.at(fls, line)), col)
      Found.col(here, line, u => Found.of(Find.down(B.Lines.drop(ls, 1n+line), B.Lines.drop(fls, 1n+line), f, 1n+line), False{}, u => Found.of(Find.down(B.Lines.take(ls, 1n+line), B.Lines.take(fls, 1n+line), f, 0n), True{}, u => NoHit{})))

# a search back from p: the line's matches before the cursor, the lines
# above, then from the bottom up to the cursor's line
def Find.prev(+ls: List<&2, String>, +fls: List<&2, String>, +f: T.Find, p: T.Pos) -> Found:
  match p:
    case T.Pos{+line, +col}:
      +here = Cols.last_before(Find.hits(f, B.Lines.at(ls, line), B.Lines.at(fls, line)), col, None{})
      +n = B.Lines.len(ls)
      Found.col(here, line, u => Found.of(Find.up(List.reverse(&2, String, B.Lines.take(ls, line)), List.reverse(&2, String, B.Lines.take(fls, line)), f, Nat.sub(line, 1n)), False{}, u => Found.of(Find.up(List.reverse(&2, String, B.Lines.drop(ls, line)), List.reverse(&2, String, B.Lines.drop(fls, line)), f, Nat.sub(n, 1n)), True{}, u => NoHit{})))

# The word under the cursor (* and #)
# ----------------------------------

def Word.at.go(s: String, +c: Nat, +i: Nat, +inword: Bool, +acc: String) -> String:
  match s:
    case SNil{}:
      Bool.pick(String, inword, String.reverse(acc), SNil{})
    case SCon{+h, +t}:
      +w = Nat.is_eq(X.Char.cls(h, False{}), 2n)
      X.Bool.when(String, w, u => X.Bool.when(String, Bool.and(inword, Nat.is_gt(i, c)), u => Word.at.go(t, c, 1n+i, False{}, SNil{}), u => String.reverse(acc)), u => Word.at.go(t, c, 1n+i, True{}, SCon{h, Bool.pick(String, inword, acc, SNil{})}))

# the word * searches for: the run of word characters under the cursor,
# else the next one on its line; "" when none
def Word.at(line: String, +c: Nat) -> String:
  Word.at.go(line, c, 0n, False{}, SNil{})

# Fuzzy matching (pickers)
# ------------------------

# whether every character of q appears in s, in order; q already folded
def Fuzzy.has(s: String, q: String) -> Bool:
  match s q:
    case _ SNil{}:
      True{}
    case SNil{} SCon{y, yt}:
      False{}
    case SCon{x, +xt} SCon{+y, +yt}:
      X.Bool.when(Bool, Char.is_eq(X.Char.fold(x), y), u => Fuzzy.has(xt, SCon{y, yt}), u => Fuzzy.has(xt, yt))

