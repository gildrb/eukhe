# eukhe: the proof of LAW commit_outcome_lands_iff_in_place
#
# PROOF: every publish fact computes.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_outcome_lands_iff_in_place(p):
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
