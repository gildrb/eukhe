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

# Reload
# ------
# bend/doc_seen.bend `reload` and `restored`: every input is free: any
# log of one file (any records, each of any version with any runs), any
# version the file holds when a later process of the session edits it.

def seen.Live.keep(+r: Ds.Rec, rest: List<&2, Ds.Rec>, same: Bool) -> List<&2, Ds.Rec>:
  match same:
    case True{}:
      r <> rest
    case False{}:
      rest

# the records of log whose version is live, in order
def seen.Live(+live: Nat, log: List<&2, Ds.Rec>) -> List<&2, Ds.Rec>:
  match log:
    case Nil{}:
      Nil{}
    case +r <> rest:
      match r:
        case Ds.Rec{t, s}:
          seen.Live.keep(Ds.Rec{t, s}, seen.Live(live, rest), Nat.is_eq(t, live))

# line n is held by a record of log whose version is live
def seen.HeldLive(+n: Nat, +live: Nat, log: List<&2, Ds.Rec>) -> Bool:
  match log:
    case Nil{}:
      False{}
    case r <> rest:
      match r:
        case Ds.Rec{t, s}:
          Bool.or(Bool.and(Nat.is_eq(t, live), seen.In(n, s)), seen.HeldLive(n, live, rest))

# LAW reload_keeps_exactly_the_live_version: a reload keeps exactly the records of the
# version the file holds, in order: none of another version (the file
# changed since, or changed back and forth: those lines were not seen of
# this text) and every one of this version
# EXCLUDES: restoring by path alone, keeping only the last record or the
# first, dropping a record of the live version, keeping a stale one
law reload_keeps_exactly_the_live_version:
  for +live: Nat
  for +log: List<&2, Ds.Rec>
  {Ds.reload(live, log) == seen.Live(live, log) : List<&2, Ds.Rec>}

# LAW reload_sees_exactly_the_live_records: after a reload, a line is seen exactly when a
# record of the version the file holds names it: the guard then lets an
# edit through exactly on the lines an earlier process saw of this text
# EXCLUDES: a line seen from a stale record, a line of a kept record lost
# (only the first record's runs restored, the last record's runs alone)
law reload_sees_exactly_the_live_records:
  for +n: Nat
  for +live: Nat
  for +log: List<&2, Ds.Rec>
  {seen.In(n, Ds.restored(Ds.reload(live, log))) == seen.HeldLive(n, live, log) : Bool}

# LAW reload_example (anchor): of a log of versions 5, 7, 5, the file holding 5 keeps
# the first and the third record, and their runs are the seen lines; the
# file holding 9 keeps nothing
# EXCLUDES: a reload that matches every version, or none
law reload_example:
  {Ds.restored(Ds.reload(5n, [Ds.Rec{5n, [Ds.Iv{1n, 3n}]}, Ds.Rec{7n, [Ds.Iv{4n, 4n}]}, Ds.Rec{5n, [Ds.Iv{9n, 9n}]}])) == [Ds.Iv{1n, 3n}, Ds.Iv{9n, 9n}] : List<&2, Ds.Iv>} & {Ds.reload(9n, [Ds.Rec{5n, [Ds.Iv{1n, 3n}]}, Ds.Rec{7n, [Ds.Iv{4n, 4n}]}]) == [] : List<&2, Ds.Rec>}

# The entry from the requirement
# ------------------------------
# The spec of the whole entry, written from the requirement (F11, the
# rules above) and the wire's primitives only: no function of
# bend/doc_seen.bend or bend/ffi_doc_seen.bend (their types only; `cap`
# and `cols` through seen.Shown and seen.Whole, which reveal_bounds pins to
# 40 and 512).

# the anchors of ats whose line is not seen, in order
def seen.sp_unseen(+seen: List<&2, Ds.Iv>, ats: List<&2, Ds.At>) -> List<&2, Ds.At>:
  match ats:
    case Nil{}:
      Nil{}
    case a <> rest:
      match a:
        case Ds.At{+n, +w}:
          seen.Unseen.keep(Ds.At{n, w}, seen.sp_unseen(seen, rest), seen.In(n, seen))

# the line numbers of the anchors us, in order
def seen.sp_lines(us: List<&2, Ds.At>) -> List<&2, Nat>:
  match us:
    case Nil{}:
      Nil{}
    case a <> rest:
      match a:
        case Ds.At{n, w}:
          n <> seen.sp_lines(rest)

# a Maybe<Nat> on the wire: 0, or 1 then the Nat
def seen.sp_put_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_nat(x, rest))

def seen.sp_put_show(x: Ds.Show, rest: String) -> String:
  match x:
    case Ds.Show{n, c}:
      Wr.put_nat(n, seen.sp_put_mnat(c, rest))

# the verdict on the unseen anchors us: their lines, the lines a
# rejection shows, whether it showed them whole
def seen.sp_verdict(+us: List<&2, Ds.At>) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, seen.sp_lines(us), Wr.put_list(~Ds.Show, ~seen.sp_put_show, seen.Shown(List.take(&2, Ds.At, us, 40n)), Wr.put_bool(seen.Whole(us), "")))

def seen.sp_mnat.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Some{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def seen.sp_mnat.tag(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{None{}, s}
        case 1n:
          seen.sp_mnat.some(Wr.get_nat(s))
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# a Maybe<Nat>: the tag 0 (none) or 1 then the Nat
def seen.sp_mnat(s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  seen.sp_mnat.tag(Wr.get_nat(s))

def seen.sp_iv.hi(lo: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Ds.Iv>:
  match r:
    case Wr.Got{hi, s}:
      Wr.Got{Ds.Iv{lo, hi}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def seen.sp_iv.lo(r: Wr.Dec<Nat>) -> Wr.Dec<Ds.Iv>:
  match r:
    case Wr.Got{lo, s}:
      seen.sp_iv.hi(lo, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a run of seen lines: lo, then hi
def seen.sp_iv(s: String) -> Wr.Dec<Ds.Iv>:
  seen.sp_iv.lo(Wr.get_nat(s))

def seen.sp_at.w(n: Nat, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Ds.At>:
  match r:
    case Wr.Got{w, s}:
      Wr.Got{Ds.At{n, w}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def seen.sp_at.n(r: Wr.Dec<Nat>) -> Wr.Dec<Ds.At>:
  match r:
    case Wr.Got{n, s}:
      seen.sp_at.w(n, seen.sp_mnat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# an anchor: its line, then its width (a Maybe<Nat>)
def seen.sp_at(s: String) -> Wr.Dec<Ds.At>:
  seen.sp_at.n(Wr.get_nat(s))

def seen.sp_done(+seen: List<&2, Ds.Iv>, ats: List<&2, Ds.At>, whole: Bool) -> String:
  match whole:
    case True{}:
      seen.sp_verdict(seen.sp_unseen(seen, ats))
    case False{}:
      Wr.err("doc_seen: input left over")

def seen.sp_ats(+seen: List<&2, Ds.Iv>, r: Wr.Dec<List<&2, Ds.At>>) -> String:
  match r:
    case Wr.Got{ats, s}:
      seen.sp_done(seen, ats, Wr.end(s))
    case Wr.Bad{}:
      Wr.err("doc_seen: malformed anchors")

def seen.sp_seen(r: Wr.Dec<List<&2, Ds.Iv>>) -> String:
  match r:
    case Wr.Got{seen, s}:
      seen.sp_ats(seen, Wr.get_list(~Ds.At, ~seen.sp_at, s))
    case Wr.Bad{}:
      Wr.err("doc_seen: malformed seen runs")

# the entry's answer to the input s: the seen runs, then the anchors
def seen.sp_entry(s: String) -> String:
  seen.sp_seen(Wr.get_list(~Ds.Iv, ~seen.sp_iv, s))

# LAW doc_seen_ffi_exact (compiled core): on every input the guard's entry answers the
# spec's verdict on the seen runs and the anchors the input is exactly
# (the unseen anchors' lines in order; the first 40 of them that are
# lines of the snapshot, each cut to 512 characters when longer; whether
# they are at most 40 and each a line of at most 512 characters), and
# exactly the error form for malformed seen runs, malformed anchors, or
# input left over
# EXCLUDES: a seen anchor named or an unseen one dropped, a line shown cut
#   or whole by another rule, a whole reveal with a line missing or cut, a
#   run or an anchor misread, a reply spelled otherwise, a default for
#   malformed input, input left over ignored, another error text
law doc_seen_ffi_exact:
  for +s: String
  {Fds.ffi(s) == seen.sp_entry(s) : String}
