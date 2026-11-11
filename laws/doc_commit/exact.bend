# eukhe: the laws of area doc_commit, section exact: the reply of an edit
# pinned whole (laws/doc_commit.bend states it only through the files
# reported applied)
#
# F1: an edit of many files writes nothing when one file changed since it
#     was staged; otherwise it publishes the files in order and stops at
#     the first publish that fails; the reply calls a file applied exactly
#     when its new content landed.
# F9: a publish lands, lands with a warning (the directory sync failed, or
#     a move could not remove its source), or fails; the reply keeps that
#     warning.
# R3: the reply of an edit is an error exactly when a publish failed and
#     none landed.

import Base
import ../../bend/doc_commit.bend as Cm
import ../doc_commit.bend as DocCommit

# (F1, F9) The reply of an edit, whole
# ------------------------------------
# edit_reports_what_landed and commit_answer_is_reply read the model's
# reply only through the files it reports applied: a reply that dropped a
# landed publish's warning (Applied{False} for Landed{True}) passed. The
# spec reads the reply off the fates of the model's files (sp_fates of
# laws/doc_commit.bend: each published until the first failure, the rest
# untried), as R3 reads the real one off its fates. F1's two cases are two
# laws over the shapes of the input, so no law decides "some file changed"
# with a fold of its own: a changed file anywhere in the edit
# (edit_reply_conflict: pre, the changed file, post, all free), and an
# edit none of whose files changed (edit_reply_exact: the files built from
# any ops and faults, each unchanged, by sp_clean). Together they cover
# every edit. Every other input is free: any files, each an update or a
# move, with any fault.

# a file of an edit that did not change since it was staged: its op and
# its fault
type SpFile is Data:
  SpFile{op: Cm.Op, fault: Cm.Fault}

# the files of an edit none of whose files changed since it was staged:
# one per op and fault, in order
def sp_clean(ds: List<&2, SpFile>) -> List<&2, Cm.Doc>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> rest:
      match d:
        case SpFile{k, x}:
          Cm.Doc{k, False{}, x} <> sp_clean(rest)

# F9: whether a landed publish carries a warning
def sp_warned(w: Cm.Warn) -> Bool:
  match w:
    case Cm.NoWarn{}:
      False{}
    case Cm.SyncWarn{}:
      True{}
    case Cm.RemoveWarn{}:
      True{}

# F1: what the reply says of a file by its fate: applied, with the
# publish's warning, when its publish landed; not written otherwise (the
# model has no no-op file)
def sp_rep(f: Cm.Fate) -> Cm.Report:
  match f:
    case Cm.Noop{}:
      Cm.NotWritten{}
    case Cm.Wrote{o}:
      match o:
        case Cm.Lands{w}:
          Cm.Applied{sp_warned(w)}
        case Cm.Fails{}:
          Cm.NotWritten{}
    case Cm.Untried{}:
      Cm.NotWritten{}

def sp_reps(fs: List<&2, Cm.Fate>) -> List<&2, Cm.Report>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      sp_rep(f) <> sp_reps(rest)

# no publish among fs landed
def sp_quiet(fs: List<&2, Cm.Fate>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case f <> rest:
      match f:
        case Cm.Noop{}:
          sp_quiet(rest)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              False{}
            case Cm.Fails{}:
              sp_quiet(rest)
        case Cm.Untried{}:
          sp_quiet(rest)

# R3: a publish failed and none landed
def sp_rejects(fs: List<&2, Cm.Fate>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case f <> rest:
      match f:
        case Cm.Noop{}:
          sp_rejects(rest)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              False{}
            case Cm.Fails{}:
              sp_quiet(rest)
        case Cm.Untried{}:
          sp_rejects(rest)

def sp_reply.if(b: Bool, fs: List<&2, Cm.Fate>) -> Cm.Reply:
  match b:
    case True{}:
      Cm.Rejected{}
    case False{}:
      Cm.Answered{sp_reps(fs)}

# R3 on the model's reply: an error when a publish failed and none
# landed; otherwise one report a file
def sp_reply.fates(+fs: List<&2, Cm.Fate>) -> Cm.Reply:
  sp_reply.if(sp_rejects(fs), fs)

# LAW edit_reply_conflict (F1): an edit one of whose files changed since the edit staged it, wherever
# that file is among the others and whatever they are, is an error and
# writes nothing
# EXCLUDES: a conflict missed after the first file or before the last; an
#   answer, or a partial write, after a conflict
law edit_reply_conflict:
  for +pre: List<&2, Cm.Doc>
  for +k: Cm.Op
  for +x: Cm.Fault
  for +post: List<&2, Cm.Doc>
  {Cm.reply(List.append(&2, Cm.Doc, pre, Cm.Doc{k, True{}, x} <> post)) == Cm.Rejected{} : Cm.Reply}

# LAW edit_reply_exact (F1, F9): the reply of an edit none of whose files changed since it was
# staged (any ops, any faults, in any order) is an error when the first
# publish failed so none landed; otherwise it reports each file applied,
# with its publish's warning, when its publish landed, and not written
# otherwise (its publish failed, or one before it did). (A changed file:
# edit_reply_conflict.)
# EXCLUDES: a lost warning (Landed{w} reported Applied{False}) or an
#   invented one; an answer after nothing landed; an error after a file
#   landed; a file reported applied that failed or was never tried, or
#   the reverse; a report dropped, added or reordered; an unchanged edit
#   rejected
law edit_reply_exact:
  for +ds: List<&2, SpFile>
  {Cm.reply(sp_clean(ds)) == sp_reply.fates(DocCommit.sp_fates(sp_clean(ds))) : Cm.Reply}

def sp_get.of(b: Bool, g: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{g}
    case False{}:
      rest

# F5: the content of the first file named n (none when no file is)
def sp_get(+n: Nat, es: List<&2, Cm.Entry>) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      None{}
    case e <> rest:
      match e:
        case Cm.Entry{m, g}:
          sp_get.of(Nat.is_eq(m, n), g, sp_get(n, rest))

# F5: some file is named n
def sp_has(+n: Nat, es: List<&2, Cm.Entry>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Cm.Entry{m, g}:
          Bool.or(Nat.is_eq(m, n), sp_has(n, rest))

# LAW move_tests_exact (F5): a file named n is there exactly when some
# file has that name, and the content of n is the content of the first
# file so named (none when no file is)
# EXCLUDES: a has that is always False (move_never_overwrites and
#   move_moves vacuous: an MV over an existing file) or always True; a has
#   or get that reads only one file; a get that answers another file's
#   content, the last match, or a content for a missing name
law move_tests_exact:
  for +n: Nat
  for +es: List<&2, Cm.Entry>
  {Cm.has(n, es) == sp_has(n, es) : Bool} & {Cm.get(n, es) == sp_get(n, es) : Maybe<&2, Nat>}
