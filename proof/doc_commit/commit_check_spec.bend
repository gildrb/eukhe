# eukhe: the proof of LAW commit_check_spec
#
# PROOF: file by file, the code's check from index n is the spec's.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit

def dcw.check(ms: List<&2, Cm.Met>, +n: Nat) -> {Cm.check.go(ms, n) == DocCommit.sp_check(ms, n) : Cm.Check}:
  match ms:
    case Nil{}:
      {==}
    case m <> rest:
      match m:
        case Cm.Met{c, t}:
          match c:
            case True{}:
              {==}
            case False{}:
              match t:
                case True{}:
                  {==}
                case False{}:
                  dcw.check(rest, 1n+n)

def DocCommit.commit_check_spec(ms):
  dcw.check(ms, 0n)
