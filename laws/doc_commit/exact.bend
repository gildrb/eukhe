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
# untried), as R3 reads the real one off its fates. Every input is free:
# any files, changed or not, each an update or a move, with any fault.

# F1: some file changed since the edit staged it
def sp_changed(fs: List<&2, Cm.Doc>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case f <> rest:
      match f:
        case Cm.Doc{k, c, x}:
          Bool.or(c, sp_changed(rest))

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

def sp_reply.pick(c: Bool, +fs: List<&2, Cm.Doc>) -> Cm.Reply:
  match c:
    case True{}:
      Cm.Rejected{}
    case False{}:
      sp_reply.fates(DocCommit.sp_fates(fs))

# F1, F9: the reply of an edit: an error when a file changed since it was
# staged (nothing was written); otherwise R3 on the files' fates
def sp_reply(+fs: List<&2, Cm.Doc>) -> Cm.Reply:
  sp_reply.pick(sp_changed(fs), fs)

# LAW edit_reply_exact (F1, F9): the reply of an edit is an error when a
# file changed since the edit staged it, or when the first publish failed
# so none landed; otherwise it reports each file applied, with its
# publish's warning, when its publish landed, and not written otherwise
# (its publish failed, or one before it did)
# EXCLUDES: a lost warning (Landed{w} reported Applied{False}) or an
#   invented one; an answer after a conflict or after nothing landed; an
#   error after a file landed; a file reported applied that failed or was
#   never tried, or the reverse; a report dropped, added or reordered
law edit_reply_exact:
  for +fs: List<&2, Cm.Doc>
  {Cm.reply(fs) == sp_reply(fs) : Cm.Reply}
