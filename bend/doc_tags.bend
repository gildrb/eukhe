# doc_tags: the model of a tagged result of read and grep
# (crates/eukhe-docs/src/read/mod.rs, grep/mod.rs, store.rs).
#
# A text is its lines (each line a Nat). A result shows a tag and rows
# `(n, x)`: line number n has the text x. In the model a tag is the exact
# identity of the text it names (no hash).
#
# Read takes the text from disk, cuts the rows it shows from it, and
# records that same text: its tag names it. Grep searches the bytes it
# read (the buffer); the file may change on disk before grep records the
# result (`later`). Grep records the searched buffer, not the disk, so its
# tag names the text its rows come from.
#
# The bridge (bend/bridge_doc_tags.bend with
# crates/eukhe-docs/src/grep/bridge.rs) runs the real grep with a rewrite
# of the file between the search and the record, and compares.

import Base

# a row: a line number and its text
type Row is Data:
  Row{n: Nat, x: Nat}

# a result: the tag (the text it names) and the rows it shows
type Shown is Data:
  Shown{tag: List<&2, Nat>, rows: List<&2, Row>}

def Shown.tag(s: Shown) -> List<&2, Nat>:
  match s:
    case Shown{t, rs}:
      t

def Shown.rows(s: Shown) -> List<&2, Row>:
  match s:
    case Shown{t, rs}:
      rs

# what made a result: a read, or a grep after which the file holds
# `later`; `sel` says which lines it shows (missing: not shown)
type Op is Data:
  Read{sel: List<&2, Bool>}
  Grep{sel: List<&2, Bool>, later: List<&2, Nat>}

def keep(b: Bool, +r: Row, rs: List<&2, Row>) -> List<&2, Row>:
  match b:
    case True{}:
      r <> rs
    case False{}:
      rs

# the rows of the selected lines of ts; n is the number of the first one
def rows(ts: List<&2, Nat>, sel: List<&2, Bool>, +n: Nat) -> List<&2, Row>:
  match ts:
    case Nil{}:
      Nil{}
    case x <> rest:
      match sel:
        case Nil{}:
          Nil{}
        case s <> more:
          keep(s, Row{n, x}, rows(rest, more, 1n+n))

# the result of op on the text t it read
def show(+t: List<&2, Nat>, op: Op) -> Shown:
  match op:
    case Read{sel}:
      Shown{t, rows(t, sel, 1n)}
    case Grep{sel, later}:
      Shown{t, rows(t, sel, 1n)}

# whether line n of t is x
def is_line(t: List<&2, Nat>, n: Nat, +x: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+m:
      Maybe.default(&2, Bool, Maybe.bind(&2, Nat, Bool, List.get(&2, Nat, t, m), y => Some{Nat.is_eq(y, x)}), False{})

# whether every row (n, x) is line n of t
def from_text(+t: List<&2, Nat>, rs: List<&2, Row>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> more:
      match r:
        case Row{n, x}:
          Bool.and(is_line(t, n, x), from_text(t, more))
