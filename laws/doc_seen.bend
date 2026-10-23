# eukhe: the laws of area doc_seen

import Base
import ../bend/doc_seen.bend as Ds
import ../bend/ffi_doc_seen.bend as Fds
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (F11) Seen lines
# ----------------
# bend/doc_seen.bend: every input is free: any seen lines of a snapshot
# tagged by a read or a mismatch error (any runs of lines, so any set of
# lines), any anchors, each with any width of its line in the snapshot
# or no line there (line 0, past the end).

# line n is in the run iv: lo <= n <= hi
def seen.Inside(+n: Nat, iv: Ds.Iv) -> Bool:
  match iv:
    case Ds.Iv{lo, hi}:
      Bool.and(Nat.is_le(lo, n), Nat.is_le(n, hi))

# line n is seen: some run of ivs holds it
def seen.In(+n: Nat, ivs: List<&2, Ds.Iv>) -> Bool:
  match ivs:
    case Nil{}:
      False{}
    case iv <> rest:
      Bool.or(seen.Inside(n, iv), seen.In(n, rest))

# every line of xs is seen
def seen.Sub(xs: List<&2, Nat>, +ivs: List<&2, Ds.Iv>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(seen.In(x, ivs), seen.Sub(rest, ivs))

# each line of xs as a run of one line
def seen.Points(xs: List<&2, Nat>) -> List<&2, Ds.Iv>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      Ds.Iv{x, x} <> seen.Points(rest)

# the anchors of ats whose line is not seen, in order
def seen.Unseen.keep(+a: Ds.At, rest: List<&2, Ds.At>, s: Bool) -> List<&2, Ds.At>:
  match s:
    case True{}:
      rest
    case False{}:
      a <> rest

def seen.Unseen(+seen: List<&2, Ds.Iv>, ats: List<&2, Ds.At>) -> List<&2, Ds.At>:
  match ats:
    case Nil{}:
      Nil{}
    case +a <> rest:
      seen.Unseen.keep(a, seen.Unseen(seen, rest), seen.In(Ds.At.line(a), seen))

# a line of this width is shown whole: the snapshot has the line, and it
# has at most `cols` characters
def seen.Fit(w: Maybe<&2, Nat>) -> Bool:
  match w:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_le(x, Ds.cols)

# every anchor in us is shown whole
def seen.Fits(us: List<&2, Ds.At>) -> Bool:
  match us:
    case Nil{}:
      True{}
    case a <> rest:
      match a:
        case Ds.At{n, w}:
          Bool.and(seen.Fit(w), seen.Fits(rest))

# a rejection shows every anchor in us whole: at most `cap` of them, each
# shown whole
def seen.Whole(+us: List<&2, Ds.At>) -> Bool:
  Bool.and(Nat.is_le(List.length(&2, Ds.At, us), Ds.cap), seen.Fits(us))

# how a line is shown: whole (None), or its first `cols` characters
def seen.Cut(whole: Bool) -> Maybe<&2, Nat>:
  match whole:
    case True{}:
      None{}
    case False{}:
      Some{Ds.cols}

def seen.Shown.at(+n: Nat, w: Maybe<&2, Nat>, rest: List<&2, Ds.Show>) -> List<&2, Ds.Show>:
  match w:
    case None{}:
      rest
    case Some{x}:
      Ds.Show{n, seen.Cut(Nat.is_le(x, Ds.cols))} <> rest

# the lines a rejection shows for the anchors in us: each anchor that is
# a line of the snapshot, in order, cut when it is longer than `cols`
def seen.Shown(us: List<&2, Ds.At>) -> List<&2, Ds.Show>:
  match us:
    case Nil{}:
      Nil{}
    case a <> rest:
      match a:
        case Ds.At{n, w}:
          seen.Shown.at(n, w, seen.Shown(rest))

def seen.After.go(whole: Bool, u: List<&2, Ds.Iv>, seen: List<&2, Ds.Iv>) -> List<&2, Ds.Iv>:
  match whole:
    case True{}:
      List.append(&2, Ds.Iv, u, seen)
    case False{}:
      seen

# the seen lines after an edit whose unseen anchors are us: they join
# the seen lines when the rejection showed them whole, else nothing
# changes (and an edit with no unseen anchor changes nothing)
def seen.After(+seen: List<&2, Ds.Iv>, +us: List<&2, Ds.At>) -> List<&2, Ds.Iv>:
  seen.After.go(seen.Whole(us), seen.Points(Ds.lines(us)), seen)

# LAW edit_only_seen_lines: an edit applies only when every anchor is a seen line: a line
# number the model never saw is never an address
# EXCLUDES: an edit that applies on an unseen anchor (a guard that skips
# anchors, or only checks the first)
law edit_only_seen_lines:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  for ok: {Ds.Step.applied(Ds.edit(seen, ats)) == True{} : Bool}
  {seen.Sub(Ds.lines(ats), seen) == True{} : Bool}

# LAW edit_seen_applies: an edit whose anchors are all seen applies (the guard rejects
# nothing more)
# EXCLUDES: a guard that rejects a seen anchor (always-reject)
law edit_seen_applies:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  for all: {seen.Sub(Ds.lines(ats), seen) == True{} : Bool}
  {Ds.Step.applied(Ds.edit(seen, ats)) == True{} : Bool}

# LAW reveal_then_retry: a rejected edit with at most `cap` anchors applies on a straight
# retry exactly when every unseen anchor is a line of the snapshot of at
# most `cols` characters (the rejection showed it whole); else the retry
# is rejected again and the model must read
# EXCLUDES: a reveal that does not mark its lines seen (a retry loop),
# a retry that applies on a line the rejection never showed whole
law reveal_then_retry:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  for few: {Nat.is_le(List.length(&2, Ds.At, ats), Ds.cap) == True{} : Bool}
  {Ds.Step.applied(Ds.edit(Ds.Step.seen(Ds.edit(seen, ats)), ats)) == seen.Fits(seen.Unseen(seen, ats)) : Bool}

# LAW edit_marks_whole_reveal: after any edit, the unseen anchors join the seen lines exactly
# when the rejection showed them whole (at most `cap`, each a line of at
# most `cols` characters); else the seen lines stay as they were
# EXCLUDES: marking seen a line past the end or a line shown cut, a
# reveal that marks nothing, a reveal past `cap`
law edit_marks_whole_reveal:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  {Ds.Step.seen(Ds.edit(seen, ats)) == seen.After(seen, seen.Unseen(seen, ats)) : List<&2, Ds.Iv>}

# LAW reject_names_unseen: the guard names exactly the anchors that are not seen, in order
# (none: the edit applies)
# EXCLUDES: naming a seen anchor, dropping an unseen one
law reject_names_unseen:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  {Ds.Check.unseen(Ds.check(seen, ats)) == Ds.lines(seen.Unseen(seen, ats)) : List<&2, Nat>}

# LAW reject_shows_lines: a rejection shows, of its first `cap` unseen anchors, each one
# that is a line of the snapshot, in order, cut to `cols` characters
# when it is longer
# EXCLUDES: showing a seen line, a line past the end, more than `cap`
# lines, a long line whole, a short line cut
law reject_shows_lines:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  {Ds.Check.shown(Ds.check(seen, ats)) == seen.Shown(List.take(&2, Ds.At, seen.Unseen(seen, ats), Ds.cap)) : List<&2, Ds.Show>}

# LAW reject_whole_exact: a rejection says it showed its unseen anchors whole exactly when
# they are at most `cap` and each is a line of at most `cols` characters
# EXCLUDES: a reveal called whole with a line missing or cut
law reject_whole_exact:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  {Ds.Check.whole(Ds.check(seen, ats)) == seen.Whole(seen.Unseen(seen, ats)) : Bool}

# LAW reveal_example (anchor): line 1 is seen; line 2 is past the end, line 3 is longer
# than 512 characters, line 4 has exactly 512
# EXCLUDES: a misread of `cols` (512 shown cut, 513 whole) or of "past
# the end"
law reveal_example:
  {Ds.check([Ds.Iv{1n, 1n}], [Ds.At{1n, Some{3n}}, Ds.At{2n, None{}}, Ds.At{3n, Some{513n}}, Ds.At{4n, Some{512n}}]) == Ds.Check{[2n, 3n, 4n], [Ds.Show{3n, Some{512n}}, Ds.Show{4n, None{}}], False{}} : Ds.Check}

# LAW retry_few_witness: witness: an edit with at most `cap` anchors exists, so
# reveal_then_retry is not vacuous
# EXCLUDES: a vacuous reveal_then_retry
law retry_few_witness:
  exs ats: List<&2, Ds.At>
  {Nat.is_le(List.length(&2, Ds.At, ats), Ds.cap) == True{} : Bool}

# LAW retry_applies_example (anchor): a rejection of lines that are shown whole marks them seen,
# and the retry applies
# EXCLUDES: a retry that the whole reveal does not let through
law retry_applies_example:
  {Ds.Step.applied(Ds.edit(Ds.Step.seen(Ds.edit([Ds.Iv{1n, 1n}], [Ds.At{1n, Some{3n}}, Ds.At{2n, Some{512n}}])), [Ds.At{1n, Some{3n}}, Ds.At{2n, Some{512n}}])) == True{} : Bool}

# LAW retry_rejected_example (anchor): a rejection with a line past the end marks nothing seen,
# and the retry is rejected again
# EXCLUDES: marking seen a line the snapshot does not have
law retry_rejected_example:
  {Ds.Step.applied(Ds.edit(Ds.Step.seen(Ds.edit([Ds.Iv{1n, 1n}], [Ds.At{2n, Some{3n}}, Ds.At{9n, None{}}])), [Ds.At{2n, Some{3n}}, Ds.At{9n, None{}}])) == False{} : Bool}

# LAW seen_runs_example (anchor): on the seen runs: the guard finds a line inside a run, at
# either end of it, in any run; and not a line between runs, past the
# last, or in an empty run (hi < lo)
# EXCLUDES: a membership that ignores lo or hi, reads only the first
# run, or counts an empty run
law seen_runs_example:
  {Ds.Check.unseen(Ds.check([Ds.Iv{9n, 2n}, Ds.Iv{1n, 3n}, Ds.Iv{7n, 9n}], [Ds.At{1n, None{}}, Ds.At{2n, None{}}, Ds.At{3n, None{}}, Ds.At{4n, None{}}, Ds.At{6n, None{}}, Ds.At{7n, None{}}, Ds.At{8n, None{}}, Ds.At{9n, None{}}, Ds.At{10n, None{}}])) == [4n, 6n, 10n] : List<&2, Nat>}

# LAW reveal_bounds: a rejection shows at most 40 unseen anchors, and a line of at most
# 512 characters whole (the single source of both numbers: the Rust
# renders what `check` answers)
# EXCLUDES: a changed reveal cap or column limit
law reveal_bounds:
  {Ds.cap == 40n : Nat} & {Ds.cols == 512n : Nat}

# a run fits the wire: both ends do
def seen.IvFit(iv: Ds.Iv) -> Bool:
  match iv:
    case Ds.Iv{lo, hi}:
      Bool.and(LawsBase.wire_fits(lo), LawsBase.wire_fits(hi))

def seen.IvsFit(ivs: List<&2, Ds.Iv>) -> Bool:
  match ivs:
    case Nil{}:
      True{}
    case iv <> rest:
      Bool.and(seen.IvFit(iv), seen.IvsFit(rest))

# an anchor fits the wire: its line, and its width when it has one
def seen.AtFit(a: Ds.At) -> Bool:
  match a:
    case Ds.At{n, w}:
      match w:
        case None{}:
          LawsBase.wire_fits(n)
        case Some{x}:
          Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(x))

def seen.AtsFit(ats: List<&2, Ds.At>) -> Bool:
  match ats:
    case Nil{}:
      True{}
    case a <> rest:
      Bool.and(seen.AtFit(a), seen.AtsFit(rest))

# every number of a request of the guard fits the wire (Rust saturates a
# width at the wire's bound, and a line number is a u32)
def seen.WireFits(+seen: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>) -> Bool:
  Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Ds.Iv, seen)), seen.IvsFit(seen)), Bool.and(LawsBase.wire_fits(List.length(&2, Ds.At, ats)), seen.AtsFit(ats)))

# LAW seen_entry_refines: the guard's entry of the compiled core answers, for every request
# whose numbers fit the wire, the encoding of the model's verdict
# EXCLUDES: a codec that loses, invents, reorders or misreads a seen run
# or an anchor, an entry that answers a default or another rule
law seen_entry_refines:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  for h: {seen.WireFits(seen, ats) == True{} : Bool}
  {Fds.ffi(Fds.put_req(seen, ats, "")) == Fds.put_check(Ds.check(seen, ats), "") : String}

# LAW seen_entry_rejects_example (anchor): a malformed request answers the error form, and a request
# with input left over too
# EXCLUDES: a default verdict for a request the entry could not read
law seen_entry_rejects_example:
  {Fds.ffi("1,1,") == Wr.err("doc_seen: malformed seen runs") : String} & {Fds.ffi("0,0,x") == Wr.err("doc_seen: input left over") : String}

# LAW seen_wire_fits_example (witness): a request of the guard fits the wire (seen_entry_refines
# is not vacuous)
# EXCLUDES: a vacuous seen_entry_refines
law seen_wire_fits_example:
  {seen.WireFits([Ds.Iv{1n, 3n}], [Ds.At{2n, Some{80n}}, Ds.At{9n, None{}}]) == True{} : Bool}
