# eukhe: the laws of area doc_commit

import Base
import ../bend/doc_commit.bend as Cm

# ---- documents ----

# LAWS: the documents tools (crates/eukhe-docs and the documents tools of
# crates/eukhe-core): edits, writes, moves, temporary files, line endings,
# tags, seen lines, grep and glob. Each law is an open claim about a model
# in bend/doc_*.bend; PROOF.bend proves them (as DocCommit.<law>) with the
# lemmas of proof/doc_commit/ and, for lines and their endings,
# proof/doc_lines/. A Rust bridge test runs the real
# code and the model on the same generated scenarios and requires the same
# transcript.

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
