# eukhe.com's Neovim: motions
# ===========================
#
# Where each motion puts the cursor, on a buffer's lines. A position past
# a line's end, or past the last line, is pulled back onto the text.

import Base
import ./types.bend as T
import ./text.bend as X
import ./buf.bend as B

# The cursor's room
# -----------------

# the last line of ls
def Move.last_line(ls: List<&2, String>) -> Nat:
  Nat.sub(B.Lines.len(ls), 1n)

# the last column of line l
def Move.last_col(ls: List<&2, String>, l: Nat) -> Nat:
  X.Text.last(X.Text.len(B.Lines.at(ls, l)))

# p pulled onto the text: its line at most the last, its column at most
# that line's last
def Move.clamp(+ls: List<&2, String>, p: T.Pos) -> T.Pos:
  match p:
    case T.Pos{line, col}:
      +l = Nat.min(line, Move.last_line(ls))
      T.Pos{l, Nat.min(col, Move.last_col(ls, l))}

# the column want gives on line l
def Move.aim(+ls: List<&2, String>, +l: Nat, w: T.Want) -> Nat:
  match w:
    case T.Col{n}:
      Nat.min(n, Move.last_col(ls, l))
    case T.End{}:
      Move.last_col(ls, l)

# Words
# -----
#
# Vim's word motions walk characters across lines. A line's end counts
# as a blank; an empty line is a word of its own for w and b.

# the class of the first character of s; blank (0) when s is empty
def Word.head(s: String, +big: Bool) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      X.Char.cls(h, big)

# w, from the run of class k on: rest is the cursor's line from the
# cursor, after the lines below; skip the run, then blanks; stop on the
# next non-blank character, or on an empty line reached by crossing a
# line's end; at the buffer's end, the last character
def Word.w.go(after: List<&2, String>, rest: String, +big: Bool, +k: Nat, +l: Nat, +c: Nat) -> T.Pos:
  match after rest:
    case Nil{} SNil{}:
      T.Pos{l, Nat.sub(c, 1n)}
    case Con{+nl, nt} SNil{}:
      X.Bool.when(T.Pos, String.is_empty(nl), u => Word.w.go(nt, nl, big, 0n, 1n+l, 0n), u => T.Pos{1n+l, 0n})
    case +a SCon{+h, t}:
      +cls = X.Char.cls(h, big)
      +stop = Bool.and(Nat.is_ne(cls, 0n), Nat.is_ne(cls, k))
      X.Bool.when(T.Pos, stop, u => Word.w.go(a, t, big, Bool.pick(Nat, Nat.is_eq(cls, k), k, 0n), l, 1n+c), u => T.Pos{l, c})

# the position after w from p
def Word.w(+ls: List<&2, String>, p: T.Pos, +big: Bool) -> T.Pos:
  match p:
    case T.Pos{+line, +col}:
      +rest = X.Text.drop(B.Lines.at(ls, line), col)
      Move.clamp(ls, Word.w.go(B.Lines.drop(ls, 1n+line), rest, big, Word.head(rest, big), line, col))

# e: from one past the cursor, skip blanks across lines, then the run of
# the class found; stop on the run's last character
def Word.e.go(after: List<&2, String>, rest: String, +big: Bool, +k: Nat, +l: Nat, +c: Nat) -> T.Pos:
  match after rest:
    case Nil{} SNil{}:
      T.Pos{l, Nat.sub(c, 1n)}
    case Con{+nl, nt} SNil{}:
      X.Bool.when(T.Pos, Nat.is_eq(k, 0n), u => T.Pos{l, Nat.sub(c, 1n)}, u => Word.e.go(nt, nl, big, 0n, 1n+l, 0n))
    case +a SCon{+h, t}:
      +cls = X.Char.cls(h, big)
      X.Bool.when(T.Pos, Bool.and(Nat.is_ne(k, 0n), Nat.is_ne(cls, k)), u => Word.e.go(a, t, big, cls, l, 1n+c), u => T.Pos{l, Nat.sub(c, 1n)})

# the position after e from p
def Word.e(+ls: List<&2, String>, p: T.Pos, +big: Bool) -> T.Pos:
  match p:
    case T.Pos{+line, +col}:
      +rest = X.Text.drop(B.Lines.at(ls, line), 1n+col)
      Move.clamp(ls, Word.e.go(B.Lines.drop(ls, 1n+line), rest, big, 0n, line, 1n+col))

# b: walk back from one before the cursor; before is the cursor's line
# before the cursor, reversed, after the lines above, last first; skip
# blanks (stop on an empty line), then the run of the class found; stop on
# the run's first character
def Word.b.go(above: List<&2, String>, before: String, +big: Bool, +k: Nat, +l: Nat, +c: Nat) -> T.Pos:
  match above before:
    case Nil{} SNil{}:
      T.Pos{l, c}
    case Con{+pl, pt} SNil{}:
      X.Bool.when(T.Pos, Nat.is_eq(k, 0n), u => T.Pos{l, c}, u => X.Bool.when(T.Pos, String.is_empty(pl), u => Word.b.go(pt, String.reverse(pl), big, 0n, Nat.sub(l, 1n), X.Text.len(pl)), u => T.Pos{Nat.sub(l, 1n), 0n}))
    case +a SCon{+h, t}:
      +cls = X.Char.cls(h, big)
      X.Bool.when(T.Pos, Bool.and(Nat.is_ne(k, 0n), Nat.is_ne(cls, k)), u => Word.b.go(a, t, big, cls, l, Nat.sub(c, 1n)), u => T.Pos{l, c})

# the position after b from p
def Word.b(+ls: List<&2, String>, p: T.Pos, +big: Bool) -> T.Pos:
  match p:
    case T.Pos{+line, +col}:
      +before = String.reverse(X.Text.take(B.Lines.at(ls, line), col))
      +above = List.reverse(&2, String, B.Lines.take(ls, line))
      Move.clamp(ls, Word.b.go(above, before, big, 0n, line, col))

# Paragraphs
# ----------

def Para.down.go(ls: List<&2, String>, +l: Nat, +last: T.Pos) -> T.Pos:
  match ls:
    case Nil{}:
      last
    case Con{+h, t}:
      X.Bool.when(T.Pos, String.is_empty(h), u => Para.down.go(t, 1n+l, last), u => T.Pos{l, 0n})

# }: the next empty line below; the buffer's last character when none
def Para.down(+ls: List<&2, String>, +line: Nat) -> T.Pos:
  +end = Move.last_line(ls)
  Para.down.go(B.Lines.drop(ls, 1n+line), 1n+line, T.Pos{end, Move.last_col(ls, end)})

def Para.up.go(above: List<&2, String>, +l: Nat) -> T.Pos:
  match above:
    case Nil{}:
      T.Pos{0n, 0n}
    case Con{+h, t}:
      X.Bool.when(T.Pos, String.is_empty(h), u => Para.up.go(t, Nat.sub(l, 1n)), u => T.Pos{l, 0n})

# {: the next empty line above; the buffer's first character when none
def Para.up(+ls: List<&2, String>, +line: Nat) -> T.Pos:
  Para.up.go(List.reverse(&2, String, B.Lines.take(ls, line)), Nat.sub(line, 1n))
