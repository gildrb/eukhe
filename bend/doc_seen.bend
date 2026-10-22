# doc_seen: the seen lines of one tagged snapshot and the guard that an
# edit's anchors meet (F11). It runs as the compiled core
# (bend/ffi_doc_seen.bend, called by crates/eukhe-docs/src/hashline/seen.rs
# from patcher.rs `assert_seen_lines`).
#
# A snapshot is the text a read (or a mismatch error) tagged. Its seen
# lines are the lines whose rows reached the model: a read marks seen
# only the rows that are outside the cut of the bounded output
# (crates/eukhe-core/src/durable/documents/tool.rs `bounded`). The seen
# lines are a list of runs of lines (`Iv`): a read shows runs, so a
# whole file read is one run however long it is.
#
# An edit names its anchors (the lines it touches). Each anchor comes with
# what the snapshot holds there: the width of its line in characters, or
# nothing when the snapshot has no such line (line 0, or past the end).
# `check` is the whole guard: the edit applies only when every anchor is
# seen. Else it is rejected, and the rejection names the unseen anchors
# and shows the first `cap` of them that are lines of the snapshot, each
# cut to `cols` characters when it is longer. The unseen anchors become
# seen (so the same edit applies on a straight retry) only when the
# rejection showed every one of them whole: at most `cap` of them, each
# a line of at most `cols` characters. Else nothing becomes seen and the
# model must read again. `edit` adds what the store keeps after the
# verdict (the laws state the retry over it).
#
# Cost: an anchor's membership walks the runs and stops at the first run
# that holds it, so an edit costs O(anchors x runs); a read-only file
# has a few runs.

import Base

# the most unseen anchors that one rejection shows
# (patcher.rs SEEN_LINE_REVEAL_CAP)
def cap() -> Nat:
  40n

# the most characters of a line that a rejection shows whole
# (patcher.rs SEEN_LINE_REVEAL_MAX_COLUMNS)
def cols() -> Nat:
  512n

# A run of seen lines: the lines lo to hi, both included (none when hi < lo)
type Iv is Data:
  Iv{lo: Nat, hi: Nat}

def inside(+n: Nat, iv: Iv) -> Bool:
  match iv:
    case Iv{lo, hi}:
      Bool.and(Nat.is_le(lo, n), Nat.is_le(n, hi))

# whether line n is in a run of ivs, or hit already holds (a tail loop
# that stops at the first run that holds n)
def mem.go(ivs: List<&2, Iv>, +n: Nat, hit: Bool) -> Bool:
  match ivs:
    case Nil{}:
      hit
    case iv <> rest:
      match hit:
        case True{}:
          True{}
        case False{}:
          mem.go(rest, n, inside(n, iv))

# whether line n is seen
def mem(+n: Nat, ivs: List<&2, Iv>) -> Bool:
  mem.go(ivs, n, False{})

# the runs of single lines
def points(xs: List<&2, Nat>) -> List<&2, Iv>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      Iv{x, x} <> points(rest)

# An anchor: its line number, and the width in characters of that line of
# the snapshot (None: the snapshot has no such line)
type At is Data:
  At{line: Nat, width: Maybe<&2, Nat>}

def At.line(a: At) -> Nat:
  match a:
    case At{n, w}:
      n

# the line numbers of the anchors, in order
def lines(ats: List<&2, At>) -> List<&2, Nat>:
  match ats:
    case Nil{}:
      Nil{}
    case a <> rest:
      At.line(a) <> lines(rest)

def unseen.put(+a: At, rest: List<&2, At>, seen: Bool) -> List<&2, At>:
  match seen:
    case True{}:
      rest
    case False{}:
      a <> rest

# the anchors that are not seen, in order
def unseen(+seen: List<&2, Iv>, ats: List<&2, At>) -> List<&2, At>:
  match ats:
    case Nil{}:
      Nil{}
    case +a <> rest:
      unseen.put(a, unseen(seen, rest), mem(At.line(a), seen))

# whether a line of this width is shown whole
def fits.w(w: Maybe<&2, Nat>) -> Bool:
  match w:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_le(x, cols)

# whether every anchor is a line of at most `cols` characters
def fits(us: List<&2, At>) -> Bool:
  match us:
    case Nil{}:
      True{}
    case a <> rest:
      match a:
        case At{n, w}:
          Bool.and(fits.w(w), fits(rest))

# whether the unseen anchors are shown whole: few is whether they are at
# most `cap` (the widths are read only then)
def whole.go(few: Bool, us: List<&2, At>) -> Bool:
  match few:
    case True{}:
      fits(us)
    case False{}:
      False{}

# A shown line of a rejection: its number, and None when it is shown
# whole, Some{k} when only its first k characters are shown (then `…`)
type Show is Data:
  Show{line: Nat, cut: Maybe<&2, Nat>}

def shows.cut(whole: Bool) -> Maybe<&2, Nat>:
  match whole:
    case True{}:
      None{}
    case False{}:
      Some{cols}

def shows.put(+n: Nat, w: Maybe<&2, Nat>, rest: List<&2, Show>) -> List<&2, Show>:
  match w:
    case None{}:
      rest
    case Some{x}:
      Show{n, shows.cut(Nat.is_le(x, cols))} <> rest

# the anchors that are lines of the snapshot, each cut past `cols`
def shows(us: List<&2, At>) -> List<&2, Show>:
  match us:
    case Nil{}:
      Nil{}
    case a <> rest:
      match a:
        case At{n, w}:
          shows.put(n, w, shows(rest))

# The guard's verdict: the unseen anchors (none: the edit applies), the
# lines the rejection shows, and whether it showed every unseen anchor
# whole (then they become seen)
type Check is Data:
  Check{unseen: List<&2, Nat>, shown: List<&2, Show>, whole: Bool}

def Check.unseen(c: Check) -> List<&2, Nat>:
  match c:
    case Check{u, s, w}:
      u

def Check.shown(c: Check) -> List<&2, Show>:
  match c:
    case Check{u, s, w}:
      s

def Check.whole(c: Check) -> Bool:
  match c:
    case Check{u, s, w}:
      w

def check.go(+u: List<&2, At>) -> Check:
  Check{lines(u), shows(List.take(&2, At, u, cap)), whole.go(Nat.is_le(List.length(&2, At, u), cap), u)}

# the guard: an edit with these anchors on a snapshot with these seen lines
def check(+seen: List<&2, Iv>, ats: List<&2, At>) -> Check:
  check.go(unseen(seen, ats))

# what an edit did: whether it applied, and the seen lines after it
type Step is Data:
  Step{applied: Bool, seen: List<&2, Iv>}

def Step.applied(s: Step) -> Bool:
  match s:
    case Step{a, seen}:
      a

def Step.seen(s: Step) -> List<&2, Iv>:
  match s:
    case Step{a, seen}:
      seen

def reveal(u: List<&2, Nat>, seen: List<&2, Iv>, whole: Bool) -> List<&2, Iv>:
  match whole:
    case True{}:
      List.append(&2, Iv, points(u), seen)
    case False{}:
      seen

def edit.fin(seen: List<&2, Iv>, u: List<&2, Nat>, whole: Bool) -> Step:
  match u:
    case Nil{}:
      Step{True{}, seen}
    case +x <> +rest:
      Step{False{}, reveal(x <> rest, seen, whole)}

def edit.go(seen: List<&2, Iv>, c: Check) -> Step:
  match c:
    case Check{u, s, w}:
      edit.fin(seen, u, w)

# an edit: the guard's verdict, and the seen lines the store keeps after it
# (the unseen anchors join them when the rejection was whole)
def edit(+seen: List<&2, Iv>, ats: List<&2, At>) -> Step:
  edit.go(seen, check(seen, ats))
