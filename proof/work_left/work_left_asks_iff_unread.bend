# eukhe: the proof of LAW work_left_asks_iff_unread
#
# PROOF: case analysis on each fact in the order the rule reads it: the first one that keeps the run computes both sides to False; with none, the loop step and the reading compute both sides.

import Base
import ../../bend/progress.bend as Pg
import ../../bend/work_left.bend as Wl
import ../../spec/agents/work_left.bend as SpL
import ../../laws/work_left.bend as WorkLeft

def WorkLeft.work_left_asks_iff_unread(f):
  match f:
    case Wl.Facts{d, q, a, b, s, n, r}:
      match d:
        case True{}:
          {==}
        case False{}:
          match q:
            case True{}:
              {==}
            case False{}:
              match a:
                case False{}:
                  {==}
                case True{}:
                  match b:
                    case False{}:
                      {==}
                    case True{}:
                      match s:
                        case Pg.Stop{k}:
                          {==}
                        case Pg.Go{k}:
                          match n:
                            case 0n:
                              {==}
                            case 1n+m:
                              match r:
                                case Wl.Unread{}:
                                  {==}
                                case Wl.Finished{}:
                                  {==}
                                case Wl.Left{}:
                                  {==}
                                case Wl.Unjudged{}:
                                  {==}
