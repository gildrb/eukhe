# eukhe: the proof of LAW edit_reply_exact
#
# PROOF: the files sp_clean builds hold no conflict (dx.clean), so the
# edit publishes. Then, by cases on
# the first file's op and fault: a first publish that fails is an error,
# and in the spec its untried tail landed nothing (dx.quiet); a first
# publish that lands answers, and the reports of the published files are
# the spec's reports of their fates (dx.reports: Applied with the
# warning up to the first failure, NotWritten from it on, dx.untried).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/exact.bend as DocCommitExact

# the files sp_clean builds hold no conflict
def dx.clean(ds: List<&2, DocCommitExact.SpFile>) -> {Cm.conflict(DocCommitExact.sp_clean(ds)) == False{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      match d:
        case DocCommitExact.SpFile{k, x}:
          dx.clean(rest)

# no publish of an untried tail landed
def dx.quiet(fs: List<&2, Cm.Doc>) -> {DocCommitExact.sp_quiet(DocCommit.sp_untried(fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      dx.quiet(rest)

# a file with no publish is not written, as an untried file is
def dx.untried(fs: List<&2, Cm.Doc>) -> {Cm.report(fs, Nil{}) == DocCommitExact.sp_reps(DocCommit.sp_untried(fs)) : List<&2, Cm.Report>}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      Equal.cong(List<&2, Cm.Report>, List<&2, Cm.Report>, z => Cm.NotWritten{} <> z, Cm.report(rest, Nil{}), DocCommitExact.sp_reps(DocCommit.sp_untried(rest)), dx.untried(rest))

# the reports of the publishes are the spec's reports of the fates
def dx.reports(fs: List<&2, Cm.Doc>) -> {Cm.report(fs, Cm.run(fs)) == DocCommitExact.sp_reps(DocCommit.sp_fates(fs)) : List<&2, Cm.Report>}:
  match fs:
    case Nil{}:
      {==}
    case f <> +rest:
      match f:
        case Cm.Doc{op, c, x}:
          match op x:
            case Cm.Update{} Cm.Clean{}:
              Equal.cong(List<&2, Cm.Report>, List<&2, Cm.Report>, z => Cm.Applied{False{}} <> z, Cm.report(rest, Cm.run(rest)), DocCommitExact.sp_reps(DocCommit.sp_fates(rest)), dx.reports(rest))
            case Cm.Update{} Cm.Sync{}:
              Equal.cong(List<&2, Cm.Report>, List<&2, Cm.Report>, z => Cm.Applied{True{}} <> z, Cm.report(rest, Cm.run(rest)), DocCommitExact.sp_reps(DocCommit.sp_fates(rest)), dx.reports(rest))
            case Cm.Update{} Cm.Remove{}:
              Equal.cong(List<&2, Cm.Report>, List<&2, Cm.Report>, z => Cm.Applied{False{}} <> z, Cm.report(rest, Cm.run(rest)), DocCommitExact.sp_reps(DocCommit.sp_fates(rest)), dx.reports(rest))
            case Cm.Moving{} Cm.Clean{}:
              Equal.cong(List<&2, Cm.Report>, List<&2, Cm.Report>, z => Cm.Applied{False{}} <> z, Cm.report(rest, Cm.run(rest)), DocCommitExact.sp_reps(DocCommit.sp_fates(rest)), dx.reports(rest))
            case Cm.Moving{} Cm.Sync{}:
              Equal.cong(List<&2, Cm.Report>, List<&2, Cm.Report>, z => Cm.Applied{True{}} <> z, Cm.report(rest, Cm.run(rest)), DocCommitExact.sp_reps(DocCommit.sp_fates(rest)), dx.reports(rest))
            case Cm.Moving{} Cm.Remove{}:
              Equal.cong(List<&2, Cm.Report>, List<&2, Cm.Report>, z => Cm.Applied{True{}} <> z, Cm.report(rest, Cm.run(rest)), DocCommitExact.sp_reps(DocCommit.sp_fates(rest)), dx.reports(rest))
            case Cm.Update{} Cm.Publish{}:
              Equal.cong(List<&2, Cm.Report>, List<&2, Cm.Report>, z => Cm.NotWritten{} <> z, Cm.report(rest, Nil{}), DocCommitExact.sp_reps(DocCommit.sp_untried(rest)), dx.untried(rest))
            case Cm.Moving{} Cm.Publish{}:
              Equal.cong(List<&2, Cm.Report>, List<&2, Cm.Report>, z => Cm.NotWritten{} <> z, Cm.report(rest, Nil{}), DocCommitExact.sp_reps(DocCommit.sp_untried(rest)), dx.untried(rest))

# a first publish that lands: the answer reports every file
def dx.lands(-w: Bool, rest: List<&2, Cm.Doc>) -> {Cm.Answered{Cm.Applied{w} <> Cm.report(rest, Cm.run(rest))} == Cm.Answered{Cm.Applied{w} <> DocCommitExact.sp_reps(DocCommit.sp_fates(rest))} : Cm.Reply}:
  %dx.reports(rest) : {Cm.Answered{Cm.Applied{w} <> Cm.report(rest, Cm.run(rest))} == Cm.Answered{Cm.Applied{w} <> _} : Cm.Reply}
  {==}

# a first publish that fails: an error
def dx.fails(rest: List<&2, Cm.Doc>) -> {Cm.Rejected{} == DocCommitExact.sp_reply.if(DocCommitExact.sp_quiet(DocCommit.sp_untried(rest)), Cm.Wrote{Cm.Fails{}} <> DocCommit.sp_untried(rest)) : Cm.Reply}:
  %Equal.sym(Bool, DocCommitExact.sp_quiet(DocCommit.sp_untried(rest)), True{}, dx.quiet(rest)) : {Cm.Rejected{} == DocCommitExact.sp_reply.if(_, Cm.Wrote{Cm.Fails{}} <> DocCommit.sp_untried(rest)) : Cm.Reply}
  {==}

# with no conflict the reply is the spec's reply of the fates
def dx.go(+fs: List<&2, Cm.Doc>) -> {Cm.reply.go(Cm.run(fs), fs) == DocCommitExact.sp_reply.fates(DocCommit.sp_fates(fs)) : Cm.Reply}:
  match fs:
    case Nil{}:
      {==}
    case f <> +rest:
      match f:
        case Cm.Doc{op, c, x}:
          match op x:
            case Cm.Update{} Cm.Clean{}:
              dx.lands(False{}, rest)
            case Cm.Update{} Cm.Sync{}:
              dx.lands(True{}, rest)
            case Cm.Update{} Cm.Remove{}:
              dx.lands(False{}, rest)
            case Cm.Moving{} Cm.Clean{}:
              dx.lands(False{}, rest)
            case Cm.Moving{} Cm.Sync{}:
              dx.lands(True{}, rest)
            case Cm.Moving{} Cm.Remove{}:
              dx.lands(True{}, rest)
            case Cm.Update{} Cm.Publish{}:
              dx.fails(rest)
            case Cm.Moving{} Cm.Publish{}:
              dx.fails(rest)

def DocCommitExact.edit_reply_exact(ds):
  +fs = DocCommitExact.sp_clean(ds)
  %Equal.sym(Bool, Cm.conflict(fs), False{}, dx.clean(ds)) : {Cm.reply.pick(_, fs) == DocCommitExact.sp_reply.fates(DocCommit.sp_fates(fs)) : Cm.Reply}
  dx.go(fs)
