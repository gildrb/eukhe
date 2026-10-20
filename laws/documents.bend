# LAWS: the documents tools (crates/eukhe-docs and the documents tools of
# crates/eukhe-core): edits, writes, moves, temporary files, line endings,
# tags, seen lines, grep and glob. Each law is an open claim about a model
# in bend/doc_*.bend; PROOF.bend proves them (as Docs.<law>) with the
# lemmas of bend/proof_documents.bend and, for lines and their endings,
# bend/proof_doc_lines.bend. A Rust bridge test runs the real
# code and the model on the same generated scenarios and requires the same
# transcript.

import Base
import ../bend/doc_seen.bend as Ds
import ../bend/doc_commit.bend as Cm
import ../bend/doc_search.bend as Sr
import ../bend/doc_lines.bend as Dl
import ../bend/doc_tags.bend as Dt

# (F1, F9) An edit of many files
# ------------------------------
# bend/doc_commit.bend: every input is free: any files, each an update or
# a move, changed since the edit staged it or not, with any fault (none,
# a failed directory sync, a failed publish, a failed source removal).

# LAW: the reply calls a file applied exactly when its new content is on
# disk: after a conflict, a publish that fails at any file, or a publish
# that lands with a warning
law edit_reports_what_landed:
  for +fs: List<&2, Cm.Doc>
  {Cm.reported(Cm.reply(fs)) == Cm.landed(fs) : List<&2, Nat>}

# LAW: when one file changed since the edit staged it, no file lands
law edit_all_or_nothing_on_conflict:
  for +pre: List<&2, Cm.Doc>
  for +k: Cm.Op
  for +x: Cm.Fault
  for +post: List<&2, Cm.Doc>
  {Cm.landed(List.append(&2, Cm.Doc, pre, Cm.Doc{k, True{}, x} <> post)) == Nil{} : List<&2, Nat>}

# LAW: an edit with no changed file and no failed publish lands every
# file
law edit_lands_every_file:
  for +fs: List<&2, Cm.Doc>
  for same: {Cm.conflict(fs) == False{} : Bool}
  for sound: {Cm.failing(fs) == False{} : Bool}
  {Cm.landed(fs) == Cm.ids(fs, 0n) : List<&2, Nat>}

# (F2) The write tool
# -------------------
# bend/doc_commit.bend: every input is free: any disk (a version or no
# file), any versions the session saw, any new content.

# LAW: a write over a version the session did not see is refused and
# changes nothing: a write never loses a change the session did not see
law write_never_loses_unseen:
  for +d: Maybe<&2, Nat>
  for +s: List<&2, Nat>
  for +c: Nat
  for lost: {Cm.unseen(d, s) == True{} : Bool}
  {Cm.write(d, s, c) == Cm.Wt{False{}, d, s} : Cm.Wt}

# LAW: a write over no file or over a version the session saw writes,
# and the session then knows the new version
law write_writes_seen:
  for +d: Maybe<&2, Nat>
  for +s: List<&2, Nat>
  for +c: Nat
  for kept: {Cm.unseen(d, s) == False{} : Bool}
  {Cm.write(d, s, c) == Cm.Wt{True{}, Some{c}, Cm.saw(c, s)} : Cm.Wt}

# (F5) A move
# -----------
# bend/doc_commit.bend: every input is free: any files with any names
# and contents, any source and destination names.

# LAW: a move to a name that a file has is refused and changes nothing:
# an MV never replaces a file
law move_never_overwrites:
  for +s: Nat
  for +t: Nat
  for +es: List<&2, Cm.Entry>
  for taken: {Cm.has(t, es) == True{} : Bool}
  {Cm.move(s, t, es) == Cm.Mv{False{}, es} : Cm.Mv}

# LAW: a move of a file to a free name moves it: the move is done, the
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

# LAW: a sweep never removes a temporary file that a live writer holds
law temp_sweep_never_held:
  for +pre: List<&2, Cm.Temp>
  for +i: Nat
  for +k: Cm.Sort
  for +post: List<&2, Cm.Temp>
  {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, k, True{}} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}

# LAW: a sweep never removes a temporary file of another target, or a
# file that is not a temporary file
law temp_sweep_only_own:
  for +pre: List<&2, Cm.Temp>
  for +i: Nat
  for +k: Cm.Sort
  for +h: Bool
  for +post: List<&2, Cm.Temp>
  for other: {Cm.Sort.own(k) == False{} : Bool}
  {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, k, h} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}

# LAW: a sweep removes every temporary file of the target that no live
# writer holds
law temp_sweep_removes_free:
  for +pre: List<&2, Cm.Temp>
  for +i: Nat
  for +post: List<&2, Cm.Temp>
  {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, Cm.Own{}, False{}} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.Temp{i, Cm.Own{}, False{}} <> Cm.sweep(post)) : List<&2, Cm.Temp>}

# (F4) Lines and their endings
# ----------------------------
# bend/doc_lines.bend: every input is free: any body of bytes (content,
# `\r`, `\n` in any order), with or without a BOM; any edit that replaces
# any run of whole lines with any new lines.

# LAW: a file loaded and persisted with no edit is the same bytes: every
# line keeps its own ending, a lone `\r` stays content, the BOM stays
law load_persist_roundtrip:
  for +f: Dl.Doc
  {Dl.persist(Dl.load(f)) == f : Dl.Doc}

# LAW: an edit of the lines [s, s+k) keeps every byte outside them: the
# bytes of the lines before s, and the bytes after line s+k (its later
# lines with their own endings, and the last piece), are the same in the
# persisted file
law edit_keeps_untouched_bytes:
  for +bom: Bool
  for +bs: List<&2, Dl.B>
  for +s: Nat
  for +k: Nat
  for +xs: List<&2, List<&2, Dl.B>>
  for fits: {Nat.is_le(Nat.add(s, k), Dl.lfs(bs)) == True{} : Bool}
  exs x: List<&2, Dl.B>
  {Dl.persist(Dl.edit(Dl.load(Dl.Doc{bom, bs}), s, k, xs)) == Dl.Doc{bom, List.append(&2, Dl.B, Dl.upto(bs, s), List.append(&2, Dl.B, x, Dl.from(bs, Nat.add(s, k))))} : Dl.Doc}

# LAW: grep and read number the lines of a text the same way and show
# the same text for each line (a text that is not empty: grep shows no
# row of an empty text, read shows one empty row)
law grep_line_is_read_line:
  for +b: Dl.B
  for +bs: List<&2, Dl.B>
  {Dl.grep_rows(b <> bs) == Dl.read_rows(b <> bs) : List<&2, List<&2, Dl.B>>}


# (F3) Tags
# ---------
# bend/doc_tags.bend: every input is free: any text, any lines shown, a
# read or a grep, and any text the file holds when grep records its
# result.

# LAW: the tag of a read or grep result names the text its rows come
# from: the tag is the identity of that text, and every row (n, x) is
# line n of it
law tag_names_shown_text:
  for +t: List<&2, Nat>
  for +op: Dt.Op
  {Dt.Shown.tag(Dt.show(t, op)) == t : List<&2, Nat>} & {Dt.from_text(t, Dt.Shown.rows(Dt.show(t, op))) == True{} : Bool}


# (F11) Seen lines
# ----------------
# bend/doc_seen.bend: every input is free: any seen lines of a snapshot
# tagged by a read or a mismatch error, any anchors.

# LAW: an edit applies only when every anchor is a seen line: a line
# number the model never saw is never an address
law edit_only_seen_lines:
  for +seen: List<&2, Nat>
  for +anchors: List<&2, Nat>
  for ok: {Ds.Step.applied(Ds.edit(seen, anchors)) == True{} : Bool}
  {Ds.subset(anchors, seen) == True{} : Bool}

# LAW: an edit whose anchors are all seen applies (the guard rejects
# nothing more)
law edit_seen_applies:
  for +seen: List<&2, Nat>
  for +anchors: List<&2, Nat>
  for all: {Ds.subset(anchors, seen) == True{} : Bool}
  {Ds.Step.applied(Ds.edit(seen, anchors)) == True{} : Bool}

# LAW: a rejection shows its unseen anchors and marks them seen, so the
# same edit applies on a straight retry (when it has at most `cap`
# anchors)
law reveal_then_retry:
  for +seen: List<&2, Nat>
  for +anchors: List<&2, Nat>
  for few: {Nat.is_le(List.length(&2, Nat, anchors), Ds.cap) == True{} : Bool}
  {Ds.Step.applied(Ds.edit(Ds.Step.seen(Ds.edit(seen, anchors)), anchors)) == True{} : Bool}

# (F6) What grep searched
# -----------------------
# bend/doc_search.bend: every input is free: any walk (text files with
# any number of matches, over the size limit or not; binary files, files
# that do not open, excluded directories, symlinks, walk errors, in any
# order), any match cap of a file, any total match cap, any page.

# LAW: every walked entry is in exactly one class (no match, shown,
# paged out, not searched, or skipped with its reason): the classes add
# up to the walk
law grep_accounts_every_file:
  for +es: List<&2, Sr.Ent>
  for +p: Nat
  for +s: Nat
  for +k: Nat
  for +rem: Nat
  for +n: Nat
  {Sr.Count.total(Sr.account(Sr.run(es, p, s, k, rem, n))) == List.length(&2, Sr.Ent, es) : Nat}

# LAW: a result has the notice of a class of entries it did not search,
# skipped, or searched only in part exactly when that class is not empty
law grep_notes_every_gap:
  for +os: List<&2, Sr.Out>
  for +t: Sr.Note
  {Sr.noted(t, os) == Bool.not(Nat.is_eq(Sr.Note.count(Sr.account(os), t), 0n)) : Bool}

# LAW: a shown file whose matches were cut has its own notice
law grep_notes_every_cut:
  for +pre: List<&2, Sr.Out>
  for +i: Nat
  for +pa: Bool
  for +post: List<&2, Sr.Out>
  {Sr.mem(i, Sr.cuts(List.append(&2, Sr.Out, pre, Sr.Out{i, Sr.Shown{}, True{}, pa} <> post))) == True{} : Bool}

# (F7) Continuations
# ------------------
# bend/doc_search.bend: every input is free: any ordered list (the
# matching files of grep, the ranked paths of glob), any skip, any page
# size, and the continuation the page gives.

# LAW: a continuation gives a page that is not empty
law continuation_progresses:
  for +ps: List<&2, Nat>
  for +s: Nat
  for +k: Nat
  for +c: Nat
  for h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}
  {List.is_empty(&2, Nat, Sr.page(ps, c, k)) == False{} : Bool}

# LAW: a page and the page of its continuation are, together, the start
# of the list after the skip: nothing left out between them, nothing
# twice
law continuation_contiguous:
  for +ps: List<&2, Nat>
  for +s: Nat
  for +k: Nat
  for +c: Nat
  for h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}
  exs rest: List<&2, Nat>
  {List.append(&2, Nat, Sr.page(ps, s, k), List.append(&2, Nat, Sr.page(ps, c, k), rest)) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}

# LAW: in a list with no item twice, a page and the page of its
# continuation have no item in common
law continuation_disjoint:
  for +ps: List<&2, Nat>
  for +s: Nat
  for +k: Nat
  for +c: Nat
  for +x: Nat
  for h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}
  for nd: {Sr.nodup(ps) == True{} : Bool}
  {Bool.and(Sr.mem(x, Sr.page(ps, s, k)), Sr.mem(x, Sr.page(ps, c, k))) == False{} : Bool}
