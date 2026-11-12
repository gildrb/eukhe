# eukhe: the laws of area doc_publish

import Base
import ../bend/doc_publish.bend as Dp
import ../bend/ffi_doc_publish.bend as FDp
import ../bend/wire.bend as Wr
import ../spec/harness/doc_publish.bend as S
import ./base.bend as LawsBase

# (H10) An edit never overwrites bytes it did not read
# ----------------------------------------------------
# spec/README.md H10. bend/doc_publish.bend: a publish of an edited file
# (eukhe-docs write.rs: every file of an edit, and the write tool) writes
# and syncs its new bytes to a temporary file, then re-reads the target
# just before the rename. Another program (no path lock: a formatter, a
# stamper) may have changed it since the edit read its base. The step the
# core answers decides: rename over the base; rebase the edit onto other
# bytes (they become its base) and re-read; or refuse the file, leaving the
# target as it is. It runs as the compiled core by
# bend/ffi_doc_publish.bend (eukhe-bend rules/doc_publish.rs).
# spec/harness/doc_publish.bend restates the rule (S1-S3) and the facts of
# a run: what each re-read met and what the rebase onto it answered.
# Every input is free: every number of rebases, base, change, version and
# list of re-reads, every input string.
#
# R1: a run of a publish, stepped by the code, renames only over its base:
#     never over bytes it did not read, nor over no file (S1).
# R2: a target that holds the base takes the change (S1).
# R3: a target that holds other bytes is rebased onto, while rebases are
#     left (S2); once they ran out it is refused (S3).
# R4: a target that is gone is refused (S3).
# R5: the code's step is the one S1-S3 state, for every number of rebases
#     and every re-read: the run laws (R1-R4) pin each step a run takes,
#     and the entry's answer (R6, doc_publish_entry_is_spec) pins every
#     step on the wire.
# R6: the entry answers each request Rust writes with the spec's step,
#     reads exactly the request and nothing after it, and answers any other
#     input with the exact error form `E doc_publish: malformed request`.
#
# Not pinned here: that Rust's re-read compares the target's bytes with the
# base, renames only on Place, and rebases with the rebase entry (area
# rebase); the Rust tests (write/tests.rs) cover it.

# Spec helpers
# ------------

# a run of a publish that rebased n times, where it stands: still based on
# a version with a change, or ended
type At is Data:
  Going{base: Nat, with: Nat}
  Ended{run: S.Run}

# where a run is after the step p, at base b with change c, having met d
# and the rebase answer r
def sp_next(p: Dp.Step, +b: Nat, +c: Nat, d: Maybe<&2, Nat>, r: Maybe<&2, Nat>) -> At:
  match p:
    case Dp.Place{}:
      Ended{S.Wrote{d, b, c}}
    case Dp.Rebase{}:
      match d:
        case None{}:
          Ended{S.Refused{}}
        case Some{v}:
          match r:
            case None{}:
              Ended{S.Refused{}}
            case Some{x}:
              Going{v, x}
    case Dp.Refuse{}:
      Ended{S.Refused{}}

# R1: the run over the re-reads ls, after n rebases, stepped by the code;
# a run with no re-read left writes nothing
def sp_run(ls: List<&2, S.Reread>, +n: Nat, a: At) -> S.Run:
  match ls:
    case Nil{}:
      match a:
        case Going{b, c}:
          S.Refused{}
        case Ended{r}:
          r
    case l <> rest:
      match l:
        case S.Reread{+d, r}:
          match a:
            case Going{+b, +c}:
              sp_run(rest, 1n+n, sp_next(Dp.step(n, S.seen(b, d)), b, c, d, r))
            case Ended{e}:
              e

# the tag of what a re-read met on the wire: 0 the base, 1 no file, 2
# other bytes
def sp_tag(s: Dp.Seen) -> Nat:
  match s:
    case Dp.Same{}:
      0n
    case Dp.Gone{}:
      1n
    case Dp.Moved{}:
      2n

# R6: the spelling of a request: the rebases done, then the tag
def sp_w_req(+n: Nat, s: Dp.Seen, rest: String) -> String:
  Wr.put_nat(n, Wr.put_nat(sp_tag(s), rest))

# R6: the spelling of a reply: 0 place, 1 rebase, 2 refuse
def sp_w_reply(p: Dp.Step) -> String:
  match p:
    case Dp.Place{}:
      Wr.put_nat(0n, "")
    case Dp.Rebase{}:
      Wr.put_nat(1n, "")
    case Dp.Refuse{}:
      Wr.put_nat(2n, "")

# Laws: the publish (R1-R4)
# -------------------------

# LAW doc_publish_never_overwrites_unread (R1): an edit never overwrites
# bytes it did not read: every run of a publish, stepped by the code, ends
# refused or renamed over the version it was based on, whatever the target
# held at each re-read and whatever each rebase answered
# EXCLUDES: a blind rename over bytes another program wrote between the
#   check and the rename (the lost `# stamp` lines of the bench task
#   stale), a rename over a target that is gone, a rebase that keeps the
#   old base
law doc_publish_never_overwrites_unread:
  for ls: List<&2, S.Reread>
  for +n: Nat
  for +b: Nat
  for +c: Nat
  {S.safe(sp_run(ls, n, Going{b, c})) == True{} : Bool}

# LAW doc_publish_places_over_base (R2): a target that holds the base takes
# the change, after any number of rebases
# EXCLUDES: a publish that refuses or rebases an unchanged file, one that
#   writes another change
law doc_publish_places_over_base:
  for +n: Nat
  for +b: Nat
  for +c: Nat
  for r: Maybe<&2, Nat>
  for ls: List<&2, S.Reread>
  {sp_run(S.Reread{Some{b}, r} <> ls, n, Going{b, c}) == S.Wrote{Some{b}, b, c} : S.Run}

# LAW doc_publish_rebases_onto_other_bytes (R3): while rebases are left, a
# target that holds other bytes is rebased onto: the run goes on based on
# them, with the rebased change
# EXCLUDES: a publish that refuses every change of the target (an edit
#   lost to a stamper that touched other lines), one that keeps the old
#   base or the old change
law doc_publish_rebases_onto_other_bytes:
  for +n: Nat
  for +b: Nat
  for +c: Nat
  for +v: Nat
  for +x: Nat
  for ls: List<&2, S.Reread>
  for left: {Nat.is_lt(n, S.bound()) == True{} : Bool}
  for other: {Nat.is_eq(v, b) == False{} : Bool}
  {sp_run(S.Reread{Some{v}, Some{x}} <> ls, n, Going{b, c}) == sp_run(ls, 1n+n, Going{v, x}) : S.Run}

# LAW doc_publish_rebases_bounded (R3): once the rebases ran out, a target
# that holds other bytes is refused
# EXCLUDES: a publish that rebases forever against a program that writes
#   at every re-read, a bound other than the spec's
law doc_publish_rebases_bounded:
  for +n: Nat
  for +b: Nat
  for +c: Nat
  for +v: Nat
  for r: Maybe<&2, Nat>
  for ls: List<&2, S.Reread>
  for spent: {Nat.is_lt(n, S.bound()) == False{} : Bool}
  for other: {Nat.is_eq(v, b) == False{} : Bool}
  {sp_run(S.Reread{Some{v}, r} <> ls, n, Going{b, c}) == S.Refused{} : S.Run}

# LAW doc_publish_refuses_gone (R4): a target that is gone is refused
# EXCLUDES: a publish that recreates a file another program removed
law doc_publish_refuses_gone:
  for +n: Nat
  for +b: Nat
  for +c: Nat
  for r: Maybe<&2, Nat>
  for ls: List<&2, S.Reread>
  {sp_run(S.Reread{None{}, r} <> ls, n, Going{b, c}) == S.Refused{} : S.Run}

# Laws: the entry (R6)
# --------------------

# LAW doc_publish_entry_is_spec (R6): the entry answers every request Rust
# spells, its count within the wire, with the spec's step, spelled
# EXCLUDES: a tag misread (other bytes read as the base), the count
#   ignored, a default, another reply spelling
law doc_publish_entry_is_spec:
  for +n: Nat
  for +s: Dp.Seen
  for h: {LawsBase.wire_fits(n) == True{} : Bool}
  {FDp.ffi(sp_w_req(n, s, "")) == sp_w_reply(S.step(n, s)) : String}

# LAW doc_publish_entry_reads (R6): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law doc_publish_entry_reads:
  for +n: Nat
  for +s: Dp.Seen
  for +rest: String
  for h: {LawsBase.wire_fits(n) == True{} : Bool}
  {FDp.get_req(sp_w_req(n, s, rest)) == Wr.Got{FDp.Req{n, s}, rest} : Wr.Dec<FDp.Req>}

# LAW doc_publish_entry_exact (R6): every input the entry does not answer
# with the error form is a spelled request whose count fits the wire
# EXCLUDES: an answer for input that is no request (a tag past 2, a
#   malformed count or tag, input left over)
law doc_publish_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FDp.ffi(s)) == False{} : Bool}
  exs n: Nat
  exs seen: Dp.Seen
  {s == sp_w_req(n, seen, "") : String} & {LawsBase.wire_fits(n) == True{} : Bool}

# LAW doc_publish_entry_refuses (R6): every error the entry answers is
# exactly `E doc_publish: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law doc_publish_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FDp.ffi(s)) == True{} : Bool}
  {FDp.ffi(s) == Wr.err("doc_publish: malformed request") : String}

# LAW doc_publish_entry_example (R1-R6): anchor: the wire strings Rust
# sends and the replies it reads; a tag past 2, a missing tag, a leading
# zero, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling, a
#   bound other than 3
law doc_publish_entry_example:
  {[FDp.ffi("0,0,"), FDp.ffi("0,1,"), FDp.ffi("0,2,"), FDp.ffi("2,2,"), FDp.ffi("3,2,"), FDp.ffi("7,0,")] == ["0,", "2,", "1,", "1,", "2,", "0,"] : List<&2, String>} &
  {[FDp.ffi("0,3,"), FDp.ffi("1,"), FDp.ffi("01,0,"), FDp.ffi("0,0,x")] == [Wr.err("doc_publish: malformed request"), Wr.err("doc_publish: malformed request"), Wr.err("doc_publish: malformed request"), Wr.err("doc_publish: malformed request")] : List<&2, String>}
