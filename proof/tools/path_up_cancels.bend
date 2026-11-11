# eukhe: the proof of LAW path_up_cancels
#
# PROOF: by induction on the segments before the name, from any names at:
# the name goes one below and `..` comes back to at.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

def puc.walk(pre: List<&2, Tl.Seg>, +n: Nat, +post: List<&2, Tl.Seg>, at: List<&2, Nat>) -> {Tl.walk(List.append(&2, Tl.Seg, pre, Tl.Name{n} <> Tl.Up{} <> post), at) == Tl.walk(List.append(&2, Tl.Seg, pre, post), at) : Maybe<&2, List<&2, Nat>>}:
  match pre:
    case Nil{}:
      {==}
    case g <> rest:
      match g:
        case Tl.Name{m}:
          puc.walk(rest, n, post, m <> at)
        case Tl.Here{}:
          puc.walk(rest, n, post, at)
        case Tl.Up{}:
          match at:
            case Nil{}:
              {==}
            case a <> above:
              puc.walk(rest, n, post, above)

def Tools.path_up_cancels(pre, n, post):
  puc.walk(pre, n, post, Nil{})
