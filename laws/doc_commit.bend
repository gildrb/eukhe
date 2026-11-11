# eukhe: the laws of area doc_commit: how the documents tools put files on
# disk (bend/doc_commit.bend, entry bend/ffi_doc_commit.bend; Rust
# crates/eukhe-docs write.rs, hashline/mod.rs, store.rs, commit.rs).
# Sections: this file (the models F1-F10, their ties to the writer's
# choices, the entry R7), laws/doc_commit/choices.bend (R1-R6 on the
# writer's choices), laws/doc_commit/exact.bend (the reply of an edit,
# whole). PROOF.bend proves them (as DocCommit.<law>,
# DocCommitChoices.<law>, DocCommitExact.<law>) with the lemmas of
# proof/doc_commit/.
#
# Requirements (bend/doc_commit.bend header, crates/eukhe-docs write.rs
# module docs):
# F1: an edit of many files writes nothing when one file changed since it
#     was staged; otherwise it publishes the files in order and stops at
#     the first publish that fails; the reply calls a file applied exactly
#     when its new content landed.
# F2: the write tool replaces a file only when the bytes on disk are a
#     version the session saw (a missing file is created); a refused write
#     changes nothing; a write puts the new content on disk and the session
#     then has seen it (R5).
# F5: an MV never replaces a file: with its destination taken it is
#     refused and nothing changes; otherwise every file named as the source
#     takes the destination name in place, with its content, and every
#     other file is kept.
# F9: a publish lands, lands with a warning (the directory sync failed, or
#     a move could not remove its source), or fails; the reply keeps that
#     warning.
# F10: a sweep removes the temporary files of the target that no live
#     writer holds and keeps every other entry; the shipped sweep (R6,
#     `gone`, the one Rust calls) is this model's sweep of the entries
#     read as the model's temporary files (temp_sweep_is_shipped).
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
# R7: the entry answers each request Rust writes with the choice of R1-R6,
#     reads exactly the request and nothing after it, and answers any
#     other input with the exact error form.

import Base
import ../bend/doc_commit.bend as Cm
import ../bend/ffi_doc_commit.bend as FCm
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (F1, F9) An edit of many files
# ------------------------------
# bend/doc_commit.bend: every input is free: any files, each an update or
# a move, changed since the edit staged it or not, with any fault (none,
# a failed directory sync, a failed publish, a failed source removal).

# LAW edit_reports_what_landed: the reply calls a file applied exactly when its new content is on
# disk: after a conflict, a publish that fails at any file, or a publish
# that lands with a warning
law edit_reports_what_landed:
  for +fs: List<&2, Cm.Doc>
  {Cm.reported(Cm.reply(fs)) == Cm.landed(fs) : List<&2, Nat>}

# LAW edit_all_or_nothing_on_conflict: when one file changed since the edit staged it, no file lands
law edit_all_or_nothing_on_conflict:
  for +pre: List<&2, Cm.Doc>
  for +k: Cm.Op
  for +x: Cm.Fault
  for +post: List<&2, Cm.Doc>
  {Cm.landed(List.append(&2, Cm.Doc, pre, Cm.Doc{k, True{}, x} <> post)) == Nil{} : List<&2, Nat>}

# LAW edit_lands_every_file: an edit with no changed file and no failed publish lands every
# file
law edit_lands_every_file:
  for +fs: List<&2, Cm.Doc>
  for same: {Cm.conflict(fs) == False{} : Bool}
  for sound: {Cm.failing(fs) == False{} : Bool}
  {Cm.landed(fs) == Cm.ids(fs, 0n) : List<&2, Nat>}

# (F2) The write tool
# -------------------
# bend/doc_commit.bend: every input is free: any disk (a version or no
# file), any versions the session saw, any new content. The model's
# versions are Nats; the shipped choices (R4, R5) read digests (texts):
# dg below names each version by its own text (dg(a) and dg(b) are the
# same text exactly when a = b), so the model answers as the shipped
# gate and seen list do on the digests of its versions.

# F2: a digest of version v: v letters `a`
def dg(v: Nat) -> String:
  match v:
    case 0n:
      ""
    case 1n+m:
      SCon{'a', dg(m)}

def dgs(s: List<&2, Nat>) -> List<&2, String>:
  match s:
    case Nil{}:
      Nil{}
    case v <> rest:
      dg(v) <> dgs(rest)

# what a write did: whether it wrote, the disk after, the seen versions
# after
def wrote(w: Cm.Wt) -> Bool:
  match w:
    case Cm.Wt{ok, d, s}:
      ok

def wt_disk(w: Cm.Wt) -> Maybe<&2, Nat>:
  match w:
    case Cm.Wt{ok, d, s}:
      d

def wt_seen(w: Cm.Wt) -> List<&2, Nat>:
  match w:
    case Cm.Wt{ok, d, s}:
      s

# R4: the gate lets the write go on
def proceeds(g: Cm.Gate) -> Bool:
  match g:
    case Cm.Proceed{}:
      True{}
    case Cm.Unseen{}:
      False{}
    case Cm.Stale{}:
      False{}

# LAW write_refused_keeps_all (F2): a write that does not write leaves the disk and the seen versions as they were
# EXCLUDES: a refused write that clobbers the file, or forgets or adds a
#   seen version
law write_refused_keeps_all:
  for +d: Maybe<&2, Nat>
  for +s: List<&2, Nat>
  for +c: Nat
  for no: {wrote(Cm.write(d, s, c)) == False{} : Bool}
  {Cm.write(d, s, c) == Cm.Wt{False{}, d, s} : Cm.Wt}

# LAW write_accepted_records_it (F2, R5): a write that writes puts the new content on disk, and the session's seen versions after it are, on digests, the shipped seen list after the session sees the new content
# EXCLUDES: a write reported done with other content on disk; the new
#   version not recorded as seen (the next write over it refused); a
#   history kept otherwise than R5
law write_accepted_records_it:
  for +d: Maybe<&2, Nat>
  for +s: List<&2, Nat>
  for +c: Nat
  for yes: {wrote(Cm.write(d, s, c)) == True{} : Bool}
  {wt_disk(Cm.write(d, s, c)) == Some{c} : Maybe<&2, Nat>} & {dgs(wt_seen(Cm.write(d, s, c))) == Cm.seen(dg(c), dgs(s)) : List<&2, String>}

# LAW write_is_gate (F2, R4): on the digests of its versions, the model writes over a version exactly when the shipped gate based on seen versions proceeds for it (whatever the expected-bytes flag), and over no file exactly when that gate proceeds for an absent file
# EXCLUDES: a model whose unseen test drifts from the shipped gate: a write
#   over a version the session never saw, a refused create, a seen version
#   refused
law write_is_gate:
  for +v: Nat
  for +s: List<&2, Nat>
  for +c: Nat
  for e: Bool
  {wrote(Cm.write(Some{v}, s, c)) == proceeds(Cm.gate(Cm.OnSeen{dgs(s)}, Cm.Present{dg(v), e})) : Bool} & {wrote(Cm.write(None{}, s, c)) == proceeds(Cm.gate(Cm.OnSeen{dgs(s)}, Cm.Absent{})) : Bool}

# (F5) A move
# -----------
# bend/doc_commit.bend: every input is free: any files with any names
# and contents, any source and destination names. A file named n is
# stated by its place: the files are pre, then Entry{n, b}, then post.

# F5: a file in its place: the files before it, its content, the files
# after it
type EntAt is Data:
  EntAt{pre: List<&2, Cm.Entry>, body: Nat, post: List<&2, Cm.Entry>}

# the files of a place with the file named n in it
def ent_at(w: EntAt, n: Nat) -> List<&2, Cm.Entry>:
  match w:
    case EntAt{pre, b, post}:
      List.append(&2, Cm.Entry, pre, Cm.Entry{n, b} <> post)

# LAW move_has_named (F5): a file named n wherever it is among the files makes the name n taken
# EXCLUDES: a has that is always False (an MV over an existing file) or
#   reads only the first file
law move_has_named:
  for +pre: List<&2, Cm.Entry>
  for +n: Nat
  for +b: Nat
  for +post: List<&2, Cm.Entry>
  {Cm.has(n, List.append(&2, Cm.Entry, pre, Cm.Entry{n, b} <> post)) == True{} : Bool}

# LAW move_has_only_named (F5): a name is taken only when some file has that name
# EXCLUDES: a has that is always True (every MV refused) or matches another
#   name
law move_has_only_named:
  for +n: Nat
  for +es: List<&2, Cm.Entry>
  for taken: {Cm.has(n, es) == True{} : Bool}
  exs w: EntAt
  {es == ent_at(w, n) : List<&2, Cm.Entry>}

# LAW move_refused_when_taken (F5): an MV to a name a file has, wherever that file is, is refused and leaves every file as it was: an MV never replaces a file
# EXCLUDES: an MV over an existing file; a refused move that changes the
#   files
law move_refused_when_taken:
  for +s: Nat
  for +pre: List<&2, Cm.Entry>
  for +t: Nat
  for +b: Nat
  for +post: List<&2, Cm.Entry>
  {Cm.move(s, t, List.append(&2, Cm.Entry, pre, Cm.Entry{t, b} <> post)) == Cm.Mv{False{}, List.append(&2, Cm.Entry, pre, Cm.Entry{t, b} <> post)} : Cm.Mv}

# LAW move_done_when_free (F5): an MV to a name no file has is done and keeps the number of files
# EXCLUDES: a move to a free name refused; a move that deletes or adds a
#   file
law move_done_when_free:
  for +s: Nat
  for +t: Nat
  for +es: List<&2, Cm.Entry>
  for free: {Cm.has(t, es) == False{} : Bool}
  {Cm.Mv.ok(Cm.move(s, t, es)) == True{} : Bool} & {List.length(&2, Cm.Entry, Cm.Mv.es(Cm.move(s, t, es))) == List.length(&2, Cm.Entry, es) : Nat}

# LAW move_renames_source_in_place (F5): when no file has the destination name, a file named as the source, wherever it is, is in the same place after the MV, named as the destination, with its content
# EXCLUDES: the moved file's content lost or swapped, the file moved to
#   another place, a second file named as the source left behind
law move_renames_source_in_place:
  for +s: Nat
  for +t: Nat
  for +pre: List<&2, Cm.Entry>
  for +b: Nat
  for +post: List<&2, Cm.Entry>
  for free: {Cm.has(t, List.append(&2, Cm.Entry, pre, Cm.Entry{s, b} <> post)) == False{} : Bool}
  {List.get(&2, Cm.Entry, Cm.Mv.es(Cm.move(s, t, List.append(&2, Cm.Entry, pre, Cm.Entry{s, b} <> post))), List.length(&2, Cm.Entry, pre)) == Some{Cm.Entry{t, b}} : Maybe<&2, Cm.Entry>}

# LAW move_keeps_other_files_in_place (F5): when no file has the destination name, a file with another name than the source, wherever it is, is in the same place after the MV, with its name and content
# EXCLUDES: an MV that renames, changes, drops or reorders another file
law move_keeps_other_files_in_place:
  for +s: Nat
  for +t: Nat
  for +pre: List<&2, Cm.Entry>
  for +m: Nat
  for +b: Nat
  for +post: List<&2, Cm.Entry>
  for free: {Cm.has(t, List.append(&2, Cm.Entry, pre, Cm.Entry{m, b} <> post)) == False{} : Bool}
  for other: {Nat.is_eq(m, s) == False{} : Bool}
  {List.get(&2, Cm.Entry, Cm.Mv.es(Cm.move(s, t, List.append(&2, Cm.Entry, pre, Cm.Entry{m, b} <> post))), List.length(&2, Cm.Entry, pre)) == Some{Cm.Entry{m, b}} : Maybe<&2, Cm.Entry>}

# LAW move_moves: a move of a file to a free name moves it: the move is done, the
# source name is gone, and the destination holds the source's content
law move_moves:
  for +s: Nat
  for +t: Nat
  for +es: List<&2, Cm.Entry>
  for free: {Cm.has(t, es) == False{} : Bool}
  for from: {Cm.has(s, es) == True{} : Bool}
  {Cm.Mv.ok(Cm.move(s, t, es)) == True{} : Bool} & {Cm.has(s, Cm.Mv.es(Cm.move(s, t, es))) == False{} : Bool} & {Cm.get(t, Cm.Mv.es(Cm.move(s, t, es))) == Cm.get(s, es) : Maybe<&2, Nat>}

# (F10) Temporary files
# ---------------------
# bend/doc_commit.bend: every input is free: any entries in the target's
# directory (a temporary file of the target, of another target, or
# another file), held by a live writer or not.

# LAW temp_sweep_never_held: a sweep never removes a temporary file that a live writer holds
law temp_sweep_never_held:
  for +pre: List<&2, Cm.Temp>
  for +i: Nat
  for +k: Cm.Sort
  for +post: List<&2, Cm.Temp>
  {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, k, True{}} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}

# LAW temp_sweep_only_own: a sweep never removes a temporary file of another target, or a
# file that is not a temporary file
law temp_sweep_only_own:
  for +pre: List<&2, Cm.Temp>
  for +i: Nat
  for +k: Cm.Sort
  for +h: Bool
  for +post: List<&2, Cm.Temp>
  for other: {Cm.Sort.own(k) == False{} : Bool}
  {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, k, h} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}

# LAW temp_sweep_removes_free: a sweep removes every temporary file of the target that no live
# writer holds
law temp_sweep_removes_free:
  for +pre: List<&2, Cm.Temp>
  for +i: Nat
  for +post: List<&2, Cm.Temp>
  {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, Cm.Own{}, False{}} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.Temp{i, Cm.Own{}, False{}} <> Cm.sweep(post)) : List<&2, Cm.Temp>}

# R6: the name prefix of a target's temporary files (crates/eukhe-docs
# write.rs module docs: `.eukhe-tmp-<xxh64 of the target name>-...`)
def tmp_prefix(h: String) -> String:
  String.append(".eukhe-tmp-", String.append(h, "-"))

# The shipped sweep is the model's
# --------------------------------
# The laws above are about the model's sweep (Cm.sweep); Rust calls the
# shipped one (Cm.gone, R6: the indices of the entries it removes). Read
# the target's directory as the model's temporary files: entry i is file
# i, held as the entry is held, of the target when its name starts with
# the target's prefix `.eukhe-tmp-<h>-` (tmp_prefix, Base's
# String.starts_with), of another target when it starts with
# `.eukhe-tmp-` only, another file otherwise (write.rs module docs). Then
# the shipped sweep removes exactly the files the model's removes, so
# temp_sweep_never_held, temp_sweep_only_own and temp_sweep_removes_free
# hold of what Rust removes.

def sp_sort.pick(own: Bool, temp: Bool) -> Cm.Sort:
  match own:
    case True{}:
      Cm.Own{}
    case False{}:
      match temp:
        case True{}:
          Cm.Foreign{}
        case False{}:
          Cm.Plain{}

# the model's sort of a file named n in the directory of the target with
# digest h
def sp_sort(+h: String, +n: String) -> Cm.Sort:
  sp_sort.pick(String.starts_with(n, tmp_prefix(h)), String.starts_with(n, ".eukhe-tmp-"))

# the entries es, from index i on, as the model's temporary files
def sp_temps(+h: String, es: List<&2, Cm.Ent>, +i: Nat) -> List<&2, Cm.Temp>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Cm.Ent{n, held}:
          Cm.Temp{i, sp_sort(h, n), held} <> sp_temps(h, rest, 1n+i)

# the indices of the files ts
def sp_ids(ts: List<&2, Cm.Temp>) -> List<&2, Nat>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      match t:
        case Cm.Temp{i, k, held}:
          i <> sp_ids(rest)

# LAW temp_sweep_is_shipped (F10, R6): for every target digest and every directory, the entries
# the shipped sweep removes (by index, as Rust reads them) are exactly
# the files the model's sweep removes, in order, the directory read as
# the model's temporary files (sp_temps: of the target by its prefix,
# held as the entry is)
# EXCLUDES: a shipped sweep that removes a held or another target's file,
#   or keeps a free one of the target, while the model's laws hold; the
#   wrong index reported
law temp_sweep_is_shipped:
  for +h: String
  for +es: List<&2, Cm.Ent>
  {Cm.gone(h, es) == sp_ids(Cm.sweep(sp_temps(h, es, 0n))) : List<&2, Nat>}

# (F1, F9) The writer's choices, tied to the models
# -------------------------------------------------
# bend/doc_commit.bend section "The writer's choices", run as the compiled
# core by bend/ffi_doc_commit.bend; R1-R6 (header) are stated on them in
# laws/doc_commit/choices.bend. Here: each choice agrees with the model it
# stands for. Every input is free.

# Spec helpers
# ------------

def sp_go(c: Cm.Check) -> Bool:
  match c:
    case Cm.Go{}:
      True{}
    case Cm.Stop{at, why}:
      False{}

# the check facts of the model's files: changed as staged, no move taken
def sp_mets(fs: List<&2, Cm.Doc>) -> List<&2, Cm.Met>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      match f:
        case Cm.Doc{k, c, x}:
          Cm.Met{c, False{}} <> sp_mets(rest)

# the publish facts a fault of the model stands for
def sp_pub(k: Cm.Op, x: Cm.Fault) -> Cm.Pub:
  match k:
    case Cm.Update{}:
      match x:
        case Cm.Clean{}:
          Cm.Updated{Cm.Placed{True{}}}
        case Cm.Sync{}:
          Cm.Updated{Cm.Placed{False{}}}
        case Cm.Publish{}:
          Cm.Updated{Cm.NotPlaced{}}
        case Cm.Remove{}:
          Cm.Updated{Cm.Placed{True{}}}
    case Cm.Moving{}:
      match x:
        case Cm.Clean{}:
          Cm.Moved{Cm.Placed{True{}}, True{}}
        case Cm.Sync{}:
          Cm.Moved{Cm.Placed{False{}}, True{}}
        case Cm.Publish{}:
          Cm.Moved{Cm.NotPlaced{}, True{}}
        case Cm.Remove{}:
          Cm.Moved{Cm.Placed{True{}}, False{}}

# what the model's publish says of an outcome
def sp_out(o: Cm.Outcome) -> Cm.Out:
  match o:
    case Cm.Lands{w}:
      match w:
        case Cm.NoWarn{}:
          Cm.Landed{False{}}
        case Cm.SyncWarn{}:
          Cm.Landed{True{}}
        case Cm.RemoveWarn{}:
          Cm.Landed{True{}}
    case Cm.Fails{}:
      Cm.Failed{}

# R2: the change of an outcome is on disk
def sp_landed(o: Cm.Outcome) -> Bool:
  match o:
    case Cm.Lands{w}:
      True{}
    case Cm.Fails{}:
      False{}

# the files (by index, from n) a list of notes reports written
def sp_written(ns: List<&2, Cm.Note>, +n: Nat) -> List<&2, Nat>:
  match ns:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case Cm.Written{}:
          n <> sp_written(rest, 1n+n)
        case Cm.Untouched{}:
          sp_written(rest, 1n+n)
        case Cm.Unwritten{}:
          sp_written(rest, 1n+n)
        case Cm.Skipped{k}:
          sp_written(rest, 1n+n)

# the files a verdict reports written
def sp_reported(v: Cm.Verdict) -> List<&2, Nat>:
  match v:
    case Cm.Failure{}:
      Nil{}
    case Cm.Summary{ns, p}:
      sp_written(ns, 0n)

def sp_untried(fs: List<&2, Cm.Doc>) -> List<&2, Cm.Fate>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      Cm.Untried{} <> sp_untried(rest)

def sp_fates.pick(+o: Cm.Outcome, go: List<&2, Cm.Fate>, stop: List<&2, Cm.Fate>) -> List<&2, Cm.Fate>:
  match o:
    case Cm.Lands{w}:
      Cm.Wrote{o} <> go
    case Cm.Fails{}:
      Cm.Wrote{o} <> stop

# the fates of the model's files: each published until the first failure,
# the rest untried; a publish's outcome is the shipped one (R2) of the
# facts its fault stands for
def sp_fates(fs: List<&2, Cm.Doc>) -> List<&2, Cm.Fate>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> +rest:
      match f:
        case Cm.Doc{k, c, x}:
          sp_fates.pick(Cm.outcome(sp_pub(k, x)), sp_fates(rest), sp_untried(rest))

# The spelling of a request and of its reply, from the wire primitives
# (R7). The wire is the contract with its one Rust user,
# crates/eukhe-docs/src/commit.rs: a request is spelled as its writer
# writes it, a reply as its reader reads it. Every row cites the line of
# commit.rs that decides it, so these tables are external (not a copy of
# bend/ffi_doc_commit.bend's encoders and readers): a tag Rust writes or
# reads otherwise breaks the row.

def sp_w_met(m: Cm.Met, rest: String) -> String:
  match m:
    case Cm.Met{c, t}:
      Wr.put_bool(c, Wr.put_bool(t, rest))  # commit.rs:151 .bool(changed).bool(taken)

def sp_w_placed(x: Cm.Placed, rest: String) -> String:
  match x:
    case Cm.NotPlaced{}:
      Wr.put_nat(0n, rest)  # commit.rs:168 Placed::No => tag(0)
    case Cm.Placed{s}:
      Wr.put_nat(1n, Wr.put_bool(s, rest))  # commit.rs:169 Placed::Yes => tag(1).bool(synced)

def sp_w_pub(p: Cm.Pub, rest: String) -> String:
  match p:
    case Cm.Updated{x}:
      Wr.put_nat(0n, sp_w_placed(x, rest))  # commit.rs:178-180 Pub::Updated => tag(0), placed
    case Cm.Deleted{r}:
      Wr.put_nat(1n, Wr.put_bool(r, rest))  # commit.rs:182-183 Pub::Deleted => tag(1).bool(removed)
    case Cm.Moved{x, r}:
      Wr.put_nat(2n, sp_w_placed(x, Wr.put_bool(r, rest)))  # commit.rs:185-188 Pub::Moved => tag(2), placed, bool(removed)

# an outcome, as commit.rs `outcome` reads it (the reply of a publish) and
# `answer` writes it (a fate of a request)
def sp_w_outcome(o: Cm.Outcome, rest: String) -> String:
  match o:
    case Cm.Lands{w}:
      match w:
        case Cm.NoWarn{}:
          Wr.put_nat(0n, Wr.put_nat(0n, rest))  # commit.rs:193-194, 210-211 0 => Lands(Warn::None)
        case Cm.SyncWarn{}:
          Wr.put_nat(0n, Wr.put_nat(1n, rest))  # commit.rs:193,195, 210,212 0 => Lands(Warn::Sync)
        case Cm.RemoveWarn{}:
          Wr.put_nat(0n, Wr.put_nat(2n, rest))  # commit.rs:193,196, 210,213 0 => Lands(Warn::Remove)
    case Cm.Fails{}:
      Wr.put_nat(1n, rest)  # commit.rs:198, 215 1 => Fails

def sp_w_fate(f: Cm.Fate, rest: String) -> String:
  match f:
    case Cm.Noop{}:
      Wr.put_nat(0n, rest)  # commit.rs:209 Fate::Noop => tag(0)
    case Cm.Wrote{o}:
      Wr.put_nat(1n, sp_w_outcome(o, rest))  # commit.rs:210,215 Fate::Wrote => tag(1), outcome
    case Cm.Untried{}:
      Wr.put_nat(2n, rest)  # commit.rs:216 Fate::Untried => tag(2)

def sp_w_base(b: Cm.Base, rest: String) -> String:
  match b:
    case Cm.OnSeen{xs}:
      Wr.put_nat(0n, Wr.put_list(~String, ~Wr.put_str, xs, rest))  # commit.rs:247-251 Base::OnSeen => tag(0), count, strs
    case Cm.OnBytes{}:
      Wr.put_nat(1n, rest)  # commit.rs:253-254 Base::OnBytes => tag(1)

def sp_w_disk(d: Cm.Disk, rest: String) -> String:
  match d:
    case Cm.Absent{}:
      Wr.put_nat(0n, rest)  # commit.rs:258 Disk::Absent => tag(0)
    case Cm.Present{g, e}:
      Wr.put_nat(1n, Wr.put_str(g, Wr.put_bool(e, rest)))  # commit.rs:259 Disk::Present => tag(1).str(digest).bool(expected)

def sp_w_ent(e: Cm.Ent, rest: String) -> String:
  match e:
    case Cm.Ent{n, h}:
      Wr.put_str(n, Wr.put_bool(h, rest))  # commit.rs:302 .str(name).bool(held)

def sp_w_req(q: FCm.Req, rest: String) -> String:
  match q:
    case FCm.QCheck{ms}:
      Wr.put_nat(0n, Wr.put_list(~Cm.Met, ~sp_w_met, ms, rest))  # commit.rs:149 tag(0).count(mets)
    case FCm.QPublish{p}:
      Wr.put_nat(1n, sp_w_pub(p, rest))  # commit.rs:176 tag(1)
    case FCm.QAnswer{fs}:
      Wr.put_nat(2n, Wr.put_list(~Cm.Fate, ~sp_w_fate, fs, rest))  # commit.rs:206 tag(2).count(fates)
    case FCm.QGate{b, d}:
      Wr.put_nat(3n, sp_w_base(b, sp_w_disk(d, rest)))  # commit.rs:245 tag(3), base, disk
    case FCm.QSeen{d, xs}:
      Wr.put_nat(4n, Wr.put_str(d, Wr.put_list(~String, ~Wr.put_str, xs, rest)))  # commit.rs:280-282 tag(4).str(digest).count(seen)
    case FCm.QPrefix{h}:
      Wr.put_nat(5n, Wr.put_str(h, rest))  # commit.rs:291 tag(5).str(name_digest)
    case FCm.QSweep{h, es}:
      Wr.put_nat(6n, Wr.put_str(h, Wr.put_list(~Cm.Ent, ~sp_w_ent, es, rest)))  # commit.rs:300 tag(6).str(name_digest).count(entries)

def sp_w_check(c: Cm.Check) -> String:
  match c:
    case Cm.Go{}:
      Wr.put_nat(0n, "")  # commit.rs:154-155 0 => None (publish every file)
    case Cm.Stop{at, why}:
      match why:
        case Cm.Changed{}:
          Wr.put_nat(1n, Wr.put_nat(at, Wr.put_nat(0n, "")))  # commit.rs:157-159 index, 0 => Why::Changed
        case Cm.Taken{}:
          Wr.put_nat(1n, Wr.put_nat(at, Wr.put_nat(1n, "")))  # commit.rs:157-160 index, 1.. => Why::Taken

def sp_w_note(x: Cm.Note, rest: String) -> String:
  match x:
    case Cm.Untouched{}:
      Wr.put_nat(0n, rest)  # commit.rs:230 0 => Note::Untouched
    case Cm.Written{}:
      Wr.put_nat(1n, rest)  # commit.rs:231 1 => Note::Written
    case Cm.Unwritten{}:
      Wr.put_nat(2n, rest)  # commit.rs:232 2 => Note::Unwritten
    case Cm.Skipped{k}:
      Wr.put_nat(3n, Wr.put_nat(k, rest))  # commit.rs:233 3.. => Note::Skipped(index)

def sp_w_verdict(v: Cm.Verdict) -> String:
  match v:
    case Cm.Failure{}:
      Wr.put_nat(0n, "")  # commit.rs:220-221 0 => Verdict::Failure
    case Cm.Summary{ns, p}:
      Wr.put_nat(1n, Wr.put_list(~Cm.Note, ~sp_w_note, ns, Wr.put_bool(p, "")))  # commit.rs:223-238 count, notes, bool(partial)

def sp_w_gate(g: Cm.Gate) -> String:
  match g:
    case Cm.Proceed{}:
      Wr.put_nat(0n, "")  # commit.rs:263 0 => Gate::Proceed
    case Cm.Unseen{}:
      Wr.put_nat(1n, "")  # commit.rs:264 1 => Gate::Unseen
    case Cm.Stale{}:
      Wr.put_nat(2n, "")  # commit.rs:265 2.. => Gate::Stale

# the reply Rust reads: the spelled choice of the model (pinned by R1-R6
# in laws/doc_commit/choices.bend); the prefix is R6's
def sp_w_reply(q: FCm.Req) -> String:
  match q:
    case FCm.QCheck{ms}:
      sp_w_check(Cm.check(ms))
    case FCm.QPublish{p}:
      sp_w_outcome(Cm.outcome(p), "")
    case FCm.QAnswer{fs}:
      sp_w_verdict(Cm.answer(fs))
    case FCm.QGate{b, d}:
      sp_w_gate(Cm.gate(b, d))
    case FCm.QSeen{d, xs}:
      Wr.put_list(~String, ~Wr.put_str, Cm.seen(d, xs), "")
    case FCm.QPrefix{h}:
      Wr.put_str(tmp_prefix(h), "")
    case FCm.QSweep{h, es}:
      Wr.put_list(~Nat, ~Wr.put_nat, Cm.gone(h, es), "")

def sp_fit_strs(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(LawsBase.wire_fits(String.length(x)), sp_fit_strs(rest))

def sp_fit_ents(es: List<&2, Cm.Ent>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> rest:
      match e:
        case Cm.Ent{n, h}:
          Bool.and(LawsBase.wire_fits(String.length(n)), sp_fit_ents(rest))

def sp_fit_base(b: Cm.Base) -> Bool:
  match b:
    case Cm.OnSeen{+xs}:
      Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), sp_fit_strs(xs))
    case Cm.OnBytes{}:
      True{}

def sp_fit_disk(d: Cm.Disk) -> Bool:
  match d:
    case Cm.Absent{}:
      True{}
    case Cm.Present{g, e}:
      LawsBase.wire_fits(String.length(g))

# every number, length and count of the request fits the wire
def sp_fit_req(q: FCm.Req) -> Bool:
  match q:
    case FCm.QCheck{ms}:
      LawsBase.wire_fits(List.length(&2, Cm.Met, ms))
    case FCm.QPublish{p}:
      True{}
    case FCm.QAnswer{fs}:
      LawsBase.wire_fits(List.length(&2, Cm.Fate, fs))
    case FCm.QGate{b, d}:
      Bool.and(sp_fit_base(b), sp_fit_disk(d))
    case FCm.QSeen{d, +xs}:
      Bool.and(LawsBase.wire_fits(String.length(d)), Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), sp_fit_strs(xs)))
    case FCm.QPrefix{h}:
      LawsBase.wire_fits(String.length(h))
    case FCm.QSweep{h, +es}:
      Bool.and(LawsBase.wire_fits(String.length(h)), Bool.and(LawsBase.wire_fits(List.length(&2, Cm.Ent, es)), sp_fit_ents(es)))

# Laws: the choices and the models
# --------------------------------

# LAW commit_check_is_conflict (R1, F1): on the model's files the check
# goes on exactly when no file changed (edit_all_or_nothing_on_conflict)
# EXCLUDES: a real check that drifts from the model's phase 1
law commit_check_is_conflict:
  for +fs: List<&2, Cm.Doc>
  {sp_go(Cm.check(sp_mets(fs))) == Bool.not(Cm.conflict(fs)) : Bool}

# LAW commit_outcome_is_publish (R2, F9): the outcome of the facts a fault
# stands for is the model's publish of that file
# EXCLUDES: a real publish that drifts from the model's `publish`
law commit_outcome_is_publish:
  for +k: Cm.Op
  for +c: Bool
  for +x: Cm.Fault
  {sp_out(Cm.outcome(sp_pub(k, x))) == Cm.publish(Cm.Doc{k, c, x}) : Cm.Out}

# LAW commit_answer_is_reply (R3, F1): on the model's files with no
# conflict, published until the first failure, the reply reports written
# exactly the files the model's reply reports applied
# EXCLUDES: a real reply that drifts from edit_reports_what_landed
law commit_answer_is_reply:
  for +fs: List<&2, Cm.Doc>
  for clean: {Cm.conflict(fs) == False{} : Bool}
  {sp_reported(Cm.answer(sp_fates(fs))) == Cm.reported(Cm.reply(fs)) : List<&2, Nat>}

# LAW commit_choices_example (R1-R6): anchor: a second file whose
# destination exists stops the edit at it; a move that kept its source
# lands with that warning; an edit whose first publish failed and then
# untried files is an error, one where a publish landed first names the
# failed file; a write over a seen digest goes on, over an unseen one is
# refused; a sweep keeps a held file, another target's and another file
# EXCLUDES: the R1-R6 laws read one way off
law commit_choices_example:
  {Cm.check([Cm.Met{False{}, False{}}, Cm.Met{False{}, True{}}, Cm.Met{True{}, False{}}]) == Cm.Stop{1n, Cm.Taken{}} : Cm.Check} & {Cm.outcome(Cm.Moved{Cm.Placed{False{}}, False{}}) == Cm.Lands{Cm.RemoveWarn{}} : Cm.Outcome} & {[Cm.answer([Cm.Wrote{Cm.Fails{}}, Cm.Untried{}]), Cm.answer([Cm.Noop{}, Cm.Wrote{Cm.Lands{Cm.NoWarn{}}}, Cm.Wrote{Cm.Fails{}}, Cm.Untried{}])] == [Cm.Failure{}, Cm.Summary{[Cm.Untouched{}, Cm.Written{}, Cm.Unwritten{}, Cm.Skipped{2n}], True{}}] : List<&2, Cm.Verdict>} & {[Cm.gate(Cm.OnSeen{["ab", "cd"]}, Cm.Present{"cd", False{}}), Cm.gate(Cm.OnSeen{["ab"]}, Cm.Present{"a", False{}})] == [Cm.Proceed{}, Cm.Unseen{}] : List<&2, Cm.Gate>} & {Cm.gone("beef", [Cm.Ent{".eukhe-tmp-beef-12-0", False{}}, Cm.Ent{".eukhe-tmp-beef-13-0", True{}}, Cm.Ent{"o", False{}}, Cm.Ent{".eukhe-tmp-dead-1-0", False{}}]) == [0n] : List<&2, Nat>}

# Laws: the entry (R7)
# --------------------

# LAW commit_entry_answers (R7): the doc_commit entry answers every
# request Rust spells, every length and count within the wire, with the
# model's choice (check, outcome, answer, gate, seen, gone: pinned by the
# R1-R6 laws of laws/doc_commit/choices.bend) or, for a prefix question,
# R6's `.eukhe-tmp-<h>-`, spelled as WIRE.md
# EXCLUDES: a field misread, swapped or dropped; a request answered with
#   another request's choice, a default, or a reply spelled otherwise
law commit_entry_answers:
  for +q: FCm.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FCm.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW commit_entry_reads (R7): the entry's decoder reads a spelled request
# back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law commit_entry_reads:
  for +q: FCm.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FCm.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FCm.Req>}

# LAW commit_entry_exact (R7): every input the entry does not answer with
# the error form is a spelled request that fits the wire
# EXCLUDES: a choice made on input that is no request (an unknown tag, a
#   malformed field, input left over)
law commit_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FCm.ffi(s)) == False{} : Bool}
  exs r: FCm.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW commit_entry_refuses (R7): every error the entry answers is exactly
# `E doc_commit: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law commit_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FCm.ffi(s)) == True{} : Bool}
  {FCm.ffi(s) == Wr.err("doc_commit: malformed request") : String}

# LAW commit_entry_example (R7): anchor: the wire strings Rust sends and
# the replies it reads; an unknown tag and input left over
# EXCLUDES: tags in another order, a field order other than Rust's
law commit_entry_example:
  {[FCm.ffi("0,3,FFFTTF"), FCm.ffi("1,2,1,TF"), FCm.ffi("2,4,0,1,0,0,1,1,2,"), FCm.ffi("3,0,2,2,ab2,cd1,2,cdF"), FCm.ffi("3,1,0,"), FCm.ffi("4,1,b3,1,a1,b1,c"), FCm.ffi("5,4,beef"), FCm.ffi("6,4,beef4,20,.eukhe-tmp-beef-12-0F20,.eukhe-tmp-beef-13-0T1,oF19,.eukhe-tmp-dead-1-0F"), FCm.ffi("7,"), FCm.ffi("5,1,ax")] == ["1,1,1,", "0,2,", "1,4,0,1,2,3,2,T", "0,", "2,", "3,1,b1,a1,c", "16,.eukhe-tmp-beef-", "1,0,", Wr.err("doc_commit: malformed request"), Wr.err("doc_commit: malformed request")] : List<&2, String>}

