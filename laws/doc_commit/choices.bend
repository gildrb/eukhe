# eukhe: the laws of area doc_commit, section choices: the writer's
# choices (bend/doc_commit.bend section "The writer's choices", answered
# by the entry bend/ffi_doc_commit.bend, law commit_entry_answers), each
# stated by properties that pin it whole, never by a copy of its code.
#
# R1: an edit writes nothing when a file changed since it was staged or a
#     move's destination exists: the first such file (a change before a
#     taken destination in one file) is the reason; otherwise every file
#     is published.
# R2: a publish lands when its new bytes are in place (with a warning when
#     the directory sync failed, or when a move could not remove its
#     source, the second taking precedence); a delete lands when the file
#     is removed; anything else fails and stops the edit.
# R3: the reply of an edit is an error exactly when a publish failed and
#     none landed; otherwise it lists each staged file (a no-op, written,
#     not written for its own reason, or not tried because the first
#     failed file failed first) and says whether some file was not
#     written.
# R4: the write tool replaces a file based on seen versions only when its
#     bytes are a version the session saw (a missing file is created);
#     based on exact bytes only when the file still holds them.
# R5: after the session sees a version, the seen versions are it, then
#     the earlier ones without it, the last 8.
# R6: the temporary files of a target are named `.eukhe-tmp-<digest>-...`
#     (the xxh64 hex digest of its file name, no `-` in it); a sweep
#     removes exactly the entries with that prefix that no live writer
#     holds, never another target's temporary files or other files.
# Every input is free: any check facts, any publish facts, any fates, any
# base and disk, any digests and seen digests, any directory entries.
# Places in a list are stated by position (pre, the item, post) and read
# with Base's List.get; counts are counts.

import Base
import ../../bend/doc_commit.bend as Cm
import ../base.bend as LawsBase
import ../doc_commit.bend as DocCommit

# Terms
# -----

# R1: n files that neither changed nor have a taken destination
def clears(n: Nat) -> List<&2, Cm.Met>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Cm.Met{False{}, False{}} <> clears(m)

# R2: the new bytes of a publish are in place (an update or a move), or
# the file is removed (a delete)
def placed(x: Cm.Placed) -> Bool:
  match x:
    case Cm.NotPlaced{}:
      False{}
    case Cm.Placed{s}:
      True{}

def in_place(p: Cm.Pub) -> Bool:
  match p:
    case Cm.Updated{x}:
      placed(x)
    case Cm.Deleted{r}:
      r
    case Cm.Moved{x, r}:
      placed(x)

# R2: the warning of a publish whose directory sync succeeded or failed
def sync_warn(s: Bool) -> Cm.Warn:
  match s:
    case True{}:
      Cm.NoWarn{}
    case False{}:
      Cm.SyncWarn{}

# R3: how many publishes landed
def nlanded(fs: List<&2, Cm.Fate>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case f <> rest:
      match f:
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              1n+nlanded(rest)
            case Cm.Fails{}:
              nlanded(rest)
        case Cm.Noop{}:
          nlanded(rest)
        case Cm.Untried{}:
          nlanded(rest)

# R3: how many publishes failed
def nfailed(fs: List<&2, Cm.Fate>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case f <> rest:
      match f:
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              nfailed(rest)
            case Cm.Fails{}:
              1n+nfailed(rest)
        case Cm.Noop{}:
          nfailed(rest)
        case Cm.Untried{}:
          nfailed(rest)

# R3: how many files were not written: a failed publish or an untried
# file
def nunwritten(fs: List<&2, Cm.Fate>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case f <> rest:
      match f:
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              nunwritten(rest)
            case Cm.Fails{}:
              1n+nunwritten(rest)
        case Cm.Noop{}:
          nunwritten(rest)
        case Cm.Untried{}:
          1n+nunwritten(rest)

def is_failure(v: Cm.Verdict) -> Bool:
  match v:
    case Cm.Failure{}:
      True{}
    case Cm.Summary{ns, p}:
      False{}

def notes_of(v: Cm.Verdict) -> List<&2, Cm.Note>:
  match v:
    case Cm.Failure{}:
      Nil{}
    case Cm.Summary{ns, p}:
      ns

def partial_of(v: Cm.Verdict) -> Bool:
  match v:
    case Cm.Failure{}:
      False{}
    case Cm.Summary{ns, p}:
      p

# R3: the note a tried file or a no-op gets for its own fate (an untried
# file's note names another file: none here)
def own_note(f: Cm.Fate) -> Maybe<&2, Cm.Note>:
  match f:
    case Cm.Noop{}:
      Some{Cm.Untouched{}}
    case Cm.Wrote{o}:
      match o:
        case Cm.Lands{w}:
          Some{Cm.Written{}}
        case Cm.Fails{}:
          Some{Cm.Unwritten{}}
    case Cm.Untried{}:
      None{}

# R4: the gate refuses because the bytes are not the expected ones
def stale(g: Cm.Gate) -> Bool:
  match g:
    case Cm.Proceed{}:
      False{}
    case Cm.Unseen{}:
      False{}
    case Cm.Stale{}:
      True{}

# R4: digests in their place: the seen digests before it and after it
type StrAt is Data:
  StrAt{pre: List<&2, String>, post: List<&2, String>}

def str_at(w: StrAt, x: String) -> List<&2, String>:
  match w:
    case StrAt{pre, post}:
      List.append(&2, String, pre, x <> post)

# R5: no seen digest is the text d (texts compared char by char)
def fresh(+d: String, s: List<&2, String>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Bool.not(LawsBase.text_same(x, d)), fresh(d, rest))

# R6: indices moved k places on
def shift(+k: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case i <> rest:
      Nat.add(k, i) <> shift(k, rest)

# R6: a digest with no `-` (an xxh64 hex digest)
def dashless(h: String) -> Bool:
  match h:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Bool.not(Char.is_eq(c, '-')), dashless(t))

# Laws (R1): the check of an edit
# -------------------------------

# LAW commit_check_clear_goes (R1): an edit none of whose files changed or has a taken destination publishes every file
# EXCLUDES: an edit stopped with no reason; a check that stops at the end
law commit_check_clear_goes:
  for +n: Nat
  {Cm.check(clears(n)) == Cm.Go{} : Cm.Check}

# LAW commit_check_stops_at_changed (R1): an edit whose first n files are clear and whose next file changed (its destination taken or not) stops at file n, because it changed
# EXCLUDES: an edit that writes after a conflict; a stop at another file;
#   a taken destination named before a change in the same file
law commit_check_stops_at_changed:
  for +n: Nat
  for +t: Bool
  for +post: List<&2, Cm.Met>
  {Cm.check(List.append(&2, Cm.Met, clears(n), Cm.Met{True{}, t} <> post)) == Cm.Stop{n, Cm.Changed{}} : Cm.Check}

# LAW commit_check_stops_at_taken (R1): an edit whose first n files are clear and whose next file did not change but has a taken destination stops at file n, because the destination is taken
# EXCLUDES: a move over an existing file; a stop at another file or for
#   another reason
law commit_check_stops_at_taken:
  for +n: Nat
  for +post: List<&2, Cm.Met>
  {Cm.check(List.append(&2, Cm.Met, clears(n), Cm.Met{False{}, True{}} <> post)) == Cm.Stop{n, Cm.Taken{}} : Cm.Check}

# Laws (R2): one publish
# ----------------------

# LAW commit_outcome_lands_iff_in_place (R2): a publish lands exactly when its new bytes are in place (an update or a move, whatever the sync and the source removal) or its file is removed (a delete)
# EXCLUDES: a failed publish reported landed, or a landed one reported
#   failed (the edit stopped after its bytes landed)
law commit_outcome_lands_iff_in_place:
  for +p: Cm.Pub
  {DocCommit.sp_landed(Cm.outcome(p)) == in_place(p) : Bool}

# LAW commit_outcome_warns (R2): an update in place warns exactly when the directory sync failed; a move in place that could not remove its source warns of that, whatever the sync; a delete that removed its file does not warn
# EXCLUDES: a lost or invented warning; a sync warning over a source left
#   behind
law commit_outcome_warns:
  for +s: Bool
  {Cm.outcome(Cm.Updated{Cm.Placed{s}}) == Cm.Lands{sync_warn(s)} : Cm.Outcome} & {Cm.outcome(Cm.Moved{Cm.Placed{s}, False{}}) == Cm.Lands{Cm.RemoveWarn{}} : Cm.Outcome} & {Cm.outcome(Cm.Deleted{True{}}) == Cm.Lands{Cm.NoWarn{}} : Cm.Outcome}

# LAW commit_outcome_move_removed_is_update (R2): a move that removed its source did what an update of its destination did
# EXCLUDES: a move whose clean or failed placement reads otherwise than an
#   update's
law commit_outcome_move_removed_is_update:
  for +x: Cm.Placed
  {Cm.outcome(Cm.Moved{x, True{}}) == Cm.outcome(Cm.Updated{x}) : Cm.Outcome}

# Laws (R3): the reply of an edit
# -------------------------------

# LAW commit_answer_failure_by_counts (R3): the reply is an error exactly when at least one publish failed and none landed
# EXCLUDES: an error after a file landed (its new tag lost); an answer
#   after nothing landed; an error with no failure
law commit_answer_failure_by_counts:
  for +fs: List<&2, Cm.Fate>
  {is_failure(Cm.answer(fs)) == Bool.and(Nat.is_gt(nfailed(fs), 0n), Nat.is_eq(nlanded(fs), 0n)) : Bool}

# LAW commit_answer_partial_by_counts (R3): a reply that is not an error says some file was not written exactly when a publish failed or a file was not tried
# EXCLUDES: a lost or invented partial flag
law commit_answer_partial_by_counts:
  for +fs: List<&2, Cm.Fate>
  for ok: {is_failure(Cm.answer(fs)) == False{} : Bool}
  {partial_of(Cm.answer(fs)) == Nat.is_gt(nunwritten(fs), 0n) : Bool}

# LAW commit_answer_one_note_each (R3): a reply that is not an error has one note per staged file
# EXCLUDES: a note dropped or added
law commit_answer_one_note_each:
  for +fs: List<&2, Cm.Fate>
  for ok: {is_failure(Cm.answer(fs)) == False{} : Bool}
  {List.length(&2, Cm.Note, notes_of(Cm.answer(fs))) == List.length(&2, Cm.Fate, fs) : Nat}

# LAW commit_answer_note_in_place (R3): in a reply that is not an error, the note in each staged file's place is the note of its own fate when it was tried or a no-op: untouched, written when its publish landed, not written when it failed
# EXCLUDES: a failed file reported written (or the reverse); a no-op
#   reported written; notes reordered
law commit_answer_note_in_place:
  for +pre: List<&2, Cm.Fate>
  for +f: Cm.Fate
  for +post: List<&2, Cm.Fate>
  for +x: Cm.Note
  for own: {own_note(f) == Some{x} : Maybe<&2, Cm.Note>}
  for ok: {is_failure(Cm.answer(List.append(&2, Cm.Fate, pre, f <> post))) == False{} : Bool}
  {List.get(&2, Cm.Note, notes_of(Cm.answer(List.append(&2, Cm.Fate, pre, f <> post))), List.length(&2, Cm.Fate, pre)) == Some{x} : Maybe<&2, Cm.Note>}

# LAW commit_answer_skip_names_first_failure (R3): in a reply that is not an error, an untried file after the first failed publish (the files before that one did not fail) is noted not tried because of that first failed file
# EXCLUDES: an untried file blamed on a later failure, on another file, or
#   reported written
law commit_answer_skip_names_first_failure:
  for +pre: List<&2, Cm.Fate>
  for +mid: List<&2, Cm.Fate>
  for +post: List<&2, Cm.Fate>
  for clean: {Nat.is_eq(nfailed(pre), 0n) == True{} : Bool}
  for ok: {is_failure(Cm.answer(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), Cm.Untried{} <> post))) == False{} : Bool}
  {List.get(&2, Cm.Note, notes_of(Cm.answer(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), Cm.Untried{} <> post))), List.length(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid))) == Some{Cm.Skipped{List.length(&2, Cm.Fate, pre)}} : Maybe<&2, Cm.Note>}

# LAW commit_answer_skip_without_failure (R3): when no publish failed, the reply is not an error and an untried file is noted not tried because of no file: the index past the last file
# EXCLUDES: an untried file blamed on a file that did not fail
law commit_answer_skip_without_failure:
  for +pre: List<&2, Cm.Fate>
  for +post: List<&2, Cm.Fate>
  for clean: {Nat.is_eq(nfailed(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post)), 0n) == True{} : Bool}
  {is_failure(Cm.answer(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post))) == False{} : Bool} & {List.get(&2, Cm.Note, notes_of(Cm.answer(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post))), List.length(&2, Cm.Fate, pre)) == Some{Cm.Skipped{List.length(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post))}} : Maybe<&2, Cm.Note>}

# Laws (R4): the write tool's gate
# --------------------------------

# LAW commit_gate_creates_on_seen (R4): a write based on seen versions creates a missing file, whatever the session saw
# EXCLUDES: a refused create
law commit_gate_creates_on_seen:
  for +s: List<&2, String>
  {Cm.gate(Cm.OnSeen{s}, Cm.Absent{}) == Cm.Proceed{} : Cm.Gate}

# LAW commit_gate_seen_digest_proceeds (R4): a write based on seen versions goes on when the file's digest is among the seen ones, wherever, whatever the expected-bytes flag
# EXCLUDES: a seen version refused; a gate that reads only the newest seen
#   digest or the expected-bytes flag
law commit_gate_seen_digest_proceeds:
  for +pre: List<&2, String>
  for +g: String
  for +post: List<&2, String>
  for +e: Bool
  {Cm.gate(Cm.OnSeen{List.append(&2, String, pre, g <> post)}, Cm.Present{g, e}) == Cm.Proceed{} : Cm.Gate}

# LAW commit_gate_unseen_refused (R4): a write based on seen versions goes on over a file only when its digest is literally one of the seen digests
# EXCLUDES: a write over bytes the session never saw (a lost change); a
#   digest compared by prefix or length
law commit_gate_unseen_refused:
  for +s: List<&2, String>
  for +g: String
  for +e: Bool
  for go: {DocCommit.proceeds(Cm.gate(Cm.OnSeen{s}, Cm.Present{g, e})) == True{} : Bool}
  exs w: StrAt
  {s == str_at(w, g) : List<&2, String>}

# LAW commit_gate_on_seen_never_stale (R4): a write based on seen versions is never refused as stale: a refusal says the session did not see the bytes
# EXCLUDES: a refusal that names the wrong reason
law commit_gate_on_seen_never_stale:
  for +s: List<&2, String>
  for +d: Cm.Disk
  {stale(Cm.gate(Cm.OnSeen{s}, d)) == False{} : Bool}

# LAW commit_gate_on_bytes (R4): a write based on exact bytes goes on exactly when the file still holds them (whatever its digest), and is refused as stale when the file is gone or changed
# EXCLUDES: a write over bytes other than the expected ones; a write that
#   recreates a file that is gone; a decision read off the digest
law commit_gate_on_bytes:
  for +g: String
  {Cm.gate(Cm.OnBytes{}, Cm.Absent{}) == Cm.Stale{} : Cm.Gate} & {Cm.gate(Cm.OnBytes{}, Cm.Present{g, True{}}) == Cm.Proceed{} : Cm.Gate} & {Cm.gate(Cm.OnBytes{}, Cm.Present{g, False{}}) == Cm.Stale{} : Cm.Gate}

# Laws (R5): the seen versions
# ----------------------------

# LAW commit_seen_ignores_old_copy (R5): an earlier copy of the version the session sees, wherever it is among the seen ones, changes nothing: the version is listed once, newest
# EXCLUDES: a duplicate; an older copy kept in its place
law commit_seen_ignores_old_copy:
  for +d: String
  for +pre: List<&2, String>
  for +post: List<&2, String>
  {Cm.seen(d, List.append(&2, String, pre, d <> post)) == Cm.seen(d, List.append(&2, String, pre, post)) : List<&2, String>}

# LAW commit_seen_fresh (R5): when the session sees a version not among the seen ones, the seen versions are it, then the 7 newest earlier ones in order
# EXCLUDES: the newest lost or not first; more than 8 kept; an older
#   version dropped while room is left; the order changed
law commit_seen_fresh:
  for +d: String
  for +s: List<&2, String>
  for new: {fresh(d, s) == True{} : Bool}
  {Cm.seen(d, s) == d <> List.take(&2, String, s, 7n) : List<&2, String>}

# Laws (R6): the temporary files
# ------------------------------
# gone(h, es): the indices of the entries the sweep of the target with
# digest h removes. Each law splits the entries around one entry: the
# indices from the entries after it move on by the entries before it and
# itself.

# LAW commit_sweep_keeps_held (R6): an empty directory sweeps nothing; an entry a live writer holds, wherever it is, is never removed, and the sweep of the rest is unchanged
# EXCLUDES: a held temporary file removed (a live write's file deleted)
law commit_sweep_keeps_held:
  for +h: String
  for +pre: List<&2, Cm.Ent>
  for +n: String
  for +post: List<&2, Cm.Ent>
  {Cm.gone(h, []) == [] : List<&2, Nat>} & {Cm.gone(h, List.append(&2, Cm.Ent, pre, Cm.Ent{n, True{}} <> post)) == List.append(&2, Nat, Cm.gone(h, pre), shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone(h, post))) : List<&2, Nat>}

# LAW commit_sweep_keeps_unprefixed (R6): an entry whose name does not start with the target's prefix `.eukhe-tmp-<h>-`, wherever it is, held or not, is never removed
# EXCLUDES: another file or another target's temporary file removed
law commit_sweep_keeps_unprefixed:
  for +h: String
  for +pre: List<&2, Cm.Ent>
  for +n: String
  for +held: Bool
  for +post: List<&2, Cm.Ent>
  for other: {String.starts_with(n, DocCommit.tmp_prefix(h)) == False{} : Bool}
  {Cm.gone(h, List.append(&2, Cm.Ent, pre, Cm.Ent{n, held} <> post)) == List.append(&2, Nat, Cm.gone(h, pre), shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone(h, post))) : List<&2, Nat>}

# LAW commit_sweep_removes_free_temp (R6): an entry named with the target's prefix `.eukhe-tmp-<h>-` that no live writer holds, wherever it is, is removed, at its index
# EXCLUDES: a crashed writer's temporary file kept; the wrong index removed
law commit_sweep_removes_free_temp:
  for +h: String
  for +pre: List<&2, Cm.Ent>
  for +rest: String
  for +post: List<&2, Cm.Ent>
  {Cm.gone(h, List.append(&2, Cm.Ent, pre, Cm.Ent{String.append(DocCommit.tmp_prefix(h), rest), False{}} <> post)) == List.append(&2, Nat, Cm.gone(h, pre), List.length(&2, Cm.Ent, pre) <> shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone(h, post))) : List<&2, Nat>}

# LAW commit_sweep_spares_other_targets (R6): for digests without `-` (xxh64 hex), the sweep of target h never removes a temporary file of another target g, wherever it is, held or not
# EXCLUDES: a prefix another target's names share (a digest that is a
#   prefix of another): one write deleting another live target's files
law commit_sweep_spares_other_targets:
  for +h: String
  for +g: String
  for +rest: String
  for +held: Bool
  for +pre: List<&2, Cm.Ent>
  for +post: List<&2, Cm.Ent>
  for hd: {dashless(h) == True{} : Bool}
  for gd: {dashless(g) == True{} : Bool}
  for ne: {LawsBase.text_same(h, g) == False{} : Bool}
  {Cm.gone(h, List.append(&2, Cm.Ent, pre, Cm.Ent{String.append(DocCommit.tmp_prefix(g), rest), held} <> post)) == List.append(&2, Nat, Cm.gone(h, pre), shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone(h, post))) : List<&2, Nat>}
