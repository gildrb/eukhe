# eukhe: the proof of LAW child_abort_rule

import Base
import ../../bend/child.bend as Ch
import ../../laws/child.bend as Child

def Child.child_abort_rule(ph, del):
  match ph:
    case Ch.Watching{w}:
      match del:
        case True{}:
          {==}
        case False{}:
          {==}
    case Ch.Owing{k, n}:
      {==}
    case Ch.Ended{}:
      {==}
