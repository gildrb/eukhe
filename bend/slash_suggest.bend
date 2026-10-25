# slash_suggest: the command a mistyped slash command most likely meant
# (Rust: eukhe-types slash_commands.rs `find_slash_command_suggestion`,
# asked by the TUI, the CLI and the Signal gateway when a typed name is no
# command). The closest candidate by Levenshtein distance in chars, the
# first one on a tie, when its distance is within the threshold of the
# typed name's UTF-8 length: 1 up to 3 bytes, else a third of it, at
# least 2. Pure: no IO, no @unsafe.

import Base
import ./skill_load.bend as Sl

# Distance
# --------

def ne.of(b: Bool) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n

# 0 when a and b are the same char, else 1
def ne(a: Char, b: Char) -> Nat:
  ne.of(Char.is_eq(a, b))

def min.of(b: Bool, x: Nat, y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

def min(+x: Nat, +y: Nat) -> Nat:
  min.of(Nat.is_le(x, y), x, y)

def head(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      x

# the lengths of the suffixes of b, longest first
def lens(b: String) -> List<&2, Nat>:
  match b:
    case SNil{}:
      [0n]
    case SCon{x, t}:
      +r = lens(t)
      Nat.add(1n, head(r)) <> r

# the row of c before a: from the row p of a (the distances from a to each
# suffix of b, longest first), the distances from c then a
def step(+c: Char, b: String, p: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case SNil{}:
      [Nat.add(1n, head(p))]
    case SCon{x, t}:
      match p:
        case Nil{}:
          []
        case p0 <> pt:
          +q = pt
          +r = step(c, t, q)
          min(min(Nat.add(1n, p0), Nat.add(1n, head(r))), Nat.add(head(q), ne(c, x))) <> r

# the distances from a to each suffix of b, longest first
def row(a: String, +b: String) -> List<&2, Nat>:
  match a:
    case SNil{}:
      lens(b)
    case SCon{c, t}:
      step(c, b, row(t, b))

# the Levenshtein distance from a to b, in chars
def dist(a: String, b: String) -> Nat:
  head(row(a, b))

# Suggestion
# ----------

# the candidate at index i and its distance
type Near is Data:
  Near{at: Nat, dist: Nat}

def near.keep(b: Bool, +d: Nat, n: Near) -> Near:
  match b:
    case True{}:
      match n:
        case Near{j, e}:
          Near{Nat.add(1n, j), e}
    case False{}:
      Near{0n, d}

def near.of(+d: Nat, m: Maybe<&2, Near>) -> Near:
  match m:
    case None{}:
      Near{0n, d}
    case Some{n}:
      match n:
        case Near{j, +e}:
          near.keep(Nat.is_lt(e, d), d, Near{j, e})

# the first candidate of the fewest edits from w, if any
def nearest(+w: String, cs: List<&2, String>) -> Maybe<&2, Near>:
  match cs:
    case Nil{}:
      None{}
    case x <> t:
      Some{near.of(dist(w, x), nearest(w, t))}

def limit.of(small: Bool, +q: Nat) -> Nat:
  match small:
    case True{}:
      1n
    case False{}:
      min.of(Nat.is_le(2n, q), q, 2n)

# the most edits a suggestion may take from a name of n bytes
def limit(+n: Nat) -> Nat:
  limit.of(Nat.is_le(n, 3n), Nat.div(n, 3n))

def within(b: Bool, j: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{j}
    case False{}:
      None{}

def pick(+w: String, m: Maybe<&2, Near>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      match n:
        case Near{j, e}:
          within(Nat.is_le(e, limit(Sl.bytes(w, 0n))), j)

# the index of the candidate to suggest for the typed name w, if any
def suggest(+w: String, cs: List<&2, String>) -> Maybe<&2, Nat>:
  pick(w, nearest(w, cs))
