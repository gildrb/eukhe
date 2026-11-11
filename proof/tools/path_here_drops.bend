# eukhe: the proof of LAW path_here_drops
#
# PROOF: by induction on the segments before the `.`, from any names at:
# `.` keeps at.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

def phd.walk(pre: List<&2, Tl.Seg>, +post: List<&2, Tl.Seg>, at: List<&2, Nat>) -> {Tl.walk(List.append(&2, Tl.Seg, pre, Tl.Here{} <> post), at) == Tl.walk(List.append(&2, Tl.Seg, pre, post), at) : Maybe<&2, List<&2, Nat>>}:
  match pre:
    case Nil{}:
      {==}
    case g <> rest:
      match g:
        case Tl.Name{m}:
          phd.walk(rest, post, m <> at)
        case Tl.Here{}:
          phd.walk(rest, post, at)
        case Tl.Up{}:
          match at:
            case Nil{}:
              {==}
            case a <> above:
              phd.walk(rest, post, above)

def Tools.path_here_drops(pre, post):
  phd.walk(pre, post, Nil{})
