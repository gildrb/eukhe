# eukhe: the proof of LAW commit_outcome_spec
#
# PROOF: every publish fact computes.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit

def dcw.outcome(p: Cm.Pub) -> {Cm.outcome(p) == DocCommit.sp_outcome(p) : Cm.Outcome}:
  match p:
    case Cm.Updated{x}:
      match x:
        case Cm.NotPlaced{}:
          {==}
        case Cm.Placed{s}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case Cm.Deleted{r}:
      match r:
        case True{}:
          {==}
        case False{}:
          {==}
    case Cm.Moved{x, r}:
      match x:
        case Cm.NotPlaced{}:
          match r:
            case True{}:
              {==}
            case False{}:
              {==}
        case Cm.Placed{s}:
          match s:
            case True{}:
              match r:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match r:
                case True{}:
                  {==}
                case False{}:
                  {==}

def DocCommit.commit_outcome_spec(p):
  dcw.outcome(p)
