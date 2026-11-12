# eukhe: the proof of LAW path_up_at_root
#
# PROOF: by induction on the segments before the `..`, from any names at
# from which they reach the root: at the end of them at is the root (any
# other names contradict the premise), and `..` there is None.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

# G at the root, Unit at any other walk
def pua.Root(m: Maybe<&2, List<&2, Nat>>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{xs}:
      match xs:
        case Nil{}:
          G
        case x <> rest:
          Unit

def pua.walk(pre: List<&2, Tl.Seg>, +post: List<&2, Tl.Seg>, at: List<&2, Nat>, h: {Tl.walk(pre, at) == Some{Nil{}} : Maybe<&2, List<&2, Nat>>}) -> {Tl.walk(List.append(&2, Tl.Seg, pre, Tl.Up{} <> post), at) == None{} : Maybe<&2, List<&2, Nat>>}:
  match pre:
    case Nil{}:
      match at:
        case Nil{}:
          {==}
        case a <> above:
          %h : pua.Root(_, {Tl.walk(post, above) == None{} : Maybe<&2, List<&2, Nat>>})
          Unit{}
    case g <> rest:
      match g:
        case Tl.Name{n}:
          pua.walk(rest, post, n <> at, h)
        case Tl.Here{}:
          pua.walk(rest, post, at, h)
        case Tl.Up{}:
          match at:
            case Nil{}:
              {==}
            case a <> above:
              pua.walk(rest, post, above, h)

def Tools.path_up_at_root(pre, post, root):
  pua.walk(pre, post, Nil{}, root)
