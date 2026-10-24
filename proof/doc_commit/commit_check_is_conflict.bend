# eukhe: the proof of LAW commit_check_is_conflict
#
# PROOF: by induction on the files: a changed file stops the check and
# makes the edit conflict; an unchanged one is skipped by both.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit

def dcw.go(fs: List<&2, Cm.Doc>, +n: Nat) -> {DocCommit.sp_go(Cm.check.go(DocCommit.sp_mets(fs), n)) == Bool.not(Cm.conflict(fs)) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      match f:
        case Cm.Doc{k, c, x}:
          match c:
            case True{}:
              {==}
            case False{}:
              dcw.go(rest, 1n+n)

def DocCommit.commit_check_is_conflict(fs):
  dcw.go(fs, 0n)
