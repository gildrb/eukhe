# eukhe: the proof of LAW commit_answer_is_reply
#
# PROOF: the model's reply reports applied what landed
# (edit_reports_what_landed), which with no conflict is landed.go; the
# notes of the model's fates are Written for each landed publish up to the
# first failure (dcw.written), and an error only when the first publish
# failed, so nothing landed (dcw.failure).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA
import ./edit_reports_what_landed.bend as PEditReportsWhatLanded

# no file of an untried tail is written
def dcw.untried(fs: List<&2, Cm.Doc>, +k: Nat, +n: Nat) -> {DocCommit.sp_written(Cm.reports(DocCommit.sp_untried(fs), k), n) == Nil{} : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      dcw.untried(rest, k, 1n+n)

# the files written are the files that landed
def dcw.written(fs: List<&2, Cm.Doc>, +k: Nat, +n: Nat) -> {DocCommit.sp_written(Cm.reports(DocCommit.sp_fates(fs), k), n) == Cm.landed.go(fs, n) : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case f <> +rest:
      match f:
        case Cm.Doc{op, c, x}:
          match op x:
            case Cm.Update{} Cm.Clean{}:
              Equal.cong(List<&2, Nat>, List<&2, Nat>, z => n <> z, DocCommit.sp_written(Cm.reports(DocCommit.sp_fates(rest), k), 1n+n), Cm.landed.go(rest, 1n+n), dcw.written(rest, k, 1n+n))
            case Cm.Update{} Cm.Sync{}:
              Equal.cong(List<&2, Nat>, List<&2, Nat>, z => n <> z, DocCommit.sp_written(Cm.reports(DocCommit.sp_fates(rest), k), 1n+n), Cm.landed.go(rest, 1n+n), dcw.written(rest, k, 1n+n))
            case Cm.Update{} Cm.Remove{}:
              Equal.cong(List<&2, Nat>, List<&2, Nat>, z => n <> z, DocCommit.sp_written(Cm.reports(DocCommit.sp_fates(rest), k), 1n+n), Cm.landed.go(rest, 1n+n), dcw.written(rest, k, 1n+n))
            case Cm.Moving{} Cm.Clean{}:
              Equal.cong(List<&2, Nat>, List<&2, Nat>, z => n <> z, DocCommit.sp_written(Cm.reports(DocCommit.sp_fates(rest), k), 1n+n), Cm.landed.go(rest, 1n+n), dcw.written(rest, k, 1n+n))
            case Cm.Moving{} Cm.Sync{}:
              Equal.cong(List<&2, Nat>, List<&2, Nat>, z => n <> z, DocCommit.sp_written(Cm.reports(DocCommit.sp_fates(rest), k), 1n+n), Cm.landed.go(rest, 1n+n), dcw.written(rest, k, 1n+n))
            case Cm.Moving{} Cm.Remove{}:
              Equal.cong(List<&2, Nat>, List<&2, Nat>, z => n <> z, DocCommit.sp_written(Cm.reports(DocCommit.sp_fates(rest), k), 1n+n), Cm.landed.go(rest, 1n+n), dcw.written(rest, k, 1n+n))
            case Cm.Update{} Cm.Publish{}:
              dcw.untried(rest, k, 1n+n)
            case Cm.Moving{} Cm.Publish{}:
              dcw.untried(rest, k, 1n+n)

def dcw.lands_first(a: Bool, -G: Type, e: {Bool.and(a, False{}) == True{} : Bool}) -> G:
  match a:
    case True{}:
      LA.dcw.ft(G, e)
    case False{}:
      LA.dcw.ft(G, e)

# an error only when the first publish failed
def dcw.failure(fs: List<&2, Cm.Doc>, e: {Bool.and(Cm.any.failed(DocCommit.sp_fates(fs)), Bool.not(Cm.any.landed(DocCommit.sp_fates(fs)))) == True{} : Bool}) -> {Nil{} == Cm.landed.go(fs, 0n) : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case f <> +rest:
      match f:
        case Cm.Doc{op, c, x}:
          match op x:
            case Cm.Update{} Cm.Clean{}:
              dcw.lands_first(Cm.any.failed(DocCommit.sp_fates(rest)), {Nil{} == Cm.landed.go(Cm.Doc{op, c, x} <> rest, 0n) : List<&2, Nat>}, e)
            case Cm.Update{} Cm.Sync{}:
              dcw.lands_first(Cm.any.failed(DocCommit.sp_fates(rest)), {Nil{} == Cm.landed.go(Cm.Doc{op, c, x} <> rest, 0n) : List<&2, Nat>}, e)
            case Cm.Update{} Cm.Remove{}:
              dcw.lands_first(Cm.any.failed(DocCommit.sp_fates(rest)), {Nil{} == Cm.landed.go(Cm.Doc{op, c, x} <> rest, 0n) : List<&2, Nat>}, e)
            case Cm.Moving{} Cm.Clean{}:
              dcw.lands_first(Cm.any.failed(DocCommit.sp_fates(rest)), {Nil{} == Cm.landed.go(Cm.Doc{op, c, x} <> rest, 0n) : List<&2, Nat>}, e)
            case Cm.Moving{} Cm.Sync{}:
              dcw.lands_first(Cm.any.failed(DocCommit.sp_fates(rest)), {Nil{} == Cm.landed.go(Cm.Doc{op, c, x} <> rest, 0n) : List<&2, Nat>}, e)
            case Cm.Moving{} Cm.Remove{}:
              dcw.lands_first(Cm.any.failed(DocCommit.sp_fates(rest)), {Nil{} == Cm.landed.go(Cm.Doc{op, c, x} <> rest, 0n) : List<&2, Nat>}, e)
            case Cm.Update{} Cm.Publish{}:
              {==}
            case Cm.Moving{} Cm.Publish{}:
              {==}

def dcw.pick(b: Bool, +fs: List<&2, Cm.Doc>, e: {Bool.and(Cm.any.failed(DocCommit.sp_fates(fs)), Bool.not(Cm.any.landed(DocCommit.sp_fates(fs)))) == b : Bool}) -> {DocCommit.sp_reported(Cm.answer.go(b, DocCommit.sp_fates(fs))) == Cm.landed.go(fs, 0n) : List<&2, Nat>}:
  match b:
    case True{}:
      dcw.failure(fs, e)
    case False{}:
      dcw.written(fs, Cm.first.failed(DocCommit.sp_fates(fs), 0n), 0n)

def DocCommit.commit_answer_is_reply(fs, clean):
  %Equal.sym(List<&2, Nat>, Cm.reported(Cm.reply(fs)), Cm.landed(fs), DocCommit.edit_reports_what_landed(fs)) : {DocCommit.sp_reported(Cm.answer(DocCommit.sp_fates(fs))) == _ : List<&2, Nat>}
  %Equal.sym(Bool, Cm.conflict(fs), False{}, clean) : {DocCommit.sp_reported(Cm.answer(DocCommit.sp_fates(fs))) == Cm.landed.pick(_, fs) : List<&2, Nat>}
  dcw.pick(Bool.and(Cm.any.failed(DocCommit.sp_fates(fs)), Bool.not(Cm.any.landed(DocCommit.sp_fates(fs)))), fs, {==})
