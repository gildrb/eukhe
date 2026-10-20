# doc_seen: the model of the seen lines of one tagged snapshot (F11;
# crates/eukhe-docs/src/hashline/patcher.rs `assert_seen_lines`,
# crates/eukhe-core/src/durable/documents/tool.rs `bounded`).
#
# A snapshot is the text a read (or a mismatch error) tagged. Its seen
# lines are the lines whose rows reached the model: a read marks seen
# only the rows that are outside the cut of the bounded output.
#
# An edit names its anchors (the lines it touches). It applies only when
# every anchor is seen. Else it is rejected, and the rejection shows the
# unseen anchors: when they are at most `cap` lines, they become seen,
# so the same edit applies on a retry; when there are more, the rejection
# shows only a part, nothing becomes seen, and the model must read again.
# Every anchor is a line of the snapshot, of at most 512 columns (a
# longer line is shown cut, and then nothing becomes seen).
#
# The bridge (bend/bridge_doc_seen.bend,
# crates/eukhe-core/src/durable/documents/bridge.rs) runs the real read
# and edit tools on a long file and compares.

import Base

# the most unseen anchors that one rejection shows whole
# (patcher.rs SEEN_LINE_REVEAL_CAP)
def cap() -> Nat:
  40n

def mem(+n: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(Nat.is_eq(x, n), mem(n, rest))

# whether every item of xs is in ys
def subset(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(mem(x, ys), subset(rest, ys))

def unseen.put(+a: Nat, rest: List<&2, Nat>, seen: Bool) -> List<&2, Nat>:
  match seen:
    case True{}:
      rest
    case False{}:
      a <> rest

# the anchors that are not seen, in order
def unseen(+seen: List<&2, Nat>, anchors: List<&2, Nat>) -> List<&2, Nat>:
  match anchors:
    case Nil{}:
      Nil{}
    case +a <> rest:
      unseen.put(a, unseen(seen, rest), mem(a, seen))

# A read: the row of line n reached the model (shown) or the cut removed it
def show(+n: Nat, seen: List<&2, Nat>, shown: Bool) -> List<&2, Nat>:
  match shown:
    case True{}:
      n <> seen
    case False{}:
      seen

# what an edit did: whether it applied, and the seen lines after it
type Step is Data:
  Step{applied: Bool, seen: List<&2, Nat>}

def Step.applied(s: Step) -> Bool:
  match s:
    case Step{a, seen}:
      a

def Step.seen(s: Step) -> List<&2, Nat>:
  match s:
    case Step{a, seen}:
      seen

def reveal(u: List<&2, Nat>, seen: List<&2, Nat>, whole: Bool) -> List<&2, Nat>:
  match whole:
    case True{}:
      List.append(&2, Nat, u, seen)
    case False{}:
      seen

def edit.go(seen: List<&2, Nat>, u: List<&2, Nat>) -> Step:
  match u:
    case Nil{}:
      Step{True{}, seen}
    case +x <> +rest:
      Step{False{}, reveal(x <> rest, seen, Nat.is_le(List.length(&2, Nat, x <> rest), cap))}

# an edit with these anchors on a snapshot with these seen lines
def edit(+seen: List<&2, Nat>, anchors: List<&2, Nat>) -> Step:
  edit.go(seen, unseen(seen, anchors))
