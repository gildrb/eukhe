# eukhe: the proof of LAW path_rejects_escape

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

# a walk that goes above its root, from the names at, is None
def pl.esc(segs: List<&2, Tl.Seg>, at: List<&2, Nat>, h: {Tl.stays(segs, LA.pl.len(at)) == False{} : Bool}) -> {Tl.walk(segs, at) == None{} : Maybe<&2, List<&2, Nat>>}:
  match segs:
    case Nil{}:
      LA.tools.pl.absurd({Tl.walk(Nil{}, at) == None{} : Maybe<&2, List<&2, Nat>>}, h)
    case s <> rest:
      match s:
        case Tl.Name{n}:
          pl.esc(rest, n <> at, h)
        case Tl.Here{}:
          pl.esc(rest, at, h)
        case Tl.Up{}:
          match at:
            case Nil{}:
              {==}
            case a <> above:
              pl.esc(rest, above, h)

def pl.path_rejects_escape(+segs: List<&2, Tl.Seg>, out: {Tl.stays(segs, 0n) == False{} : Bool}) -> {Tl.resolve(segs) == None{} : Maybe<&2, List<&2, Nat>>}:
  pl.esc(segs, Nil{}, out)

def Tools.path_rejects_escape(segs, out):
  pl.path_rejects_escape(segs, out)
