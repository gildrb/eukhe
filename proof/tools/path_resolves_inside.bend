# eukhe: the proof of LAW path_resolves_inside

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ../base/bool/misc.bend as LBoolMisc
import ./base.bend as LA

# a walk that stays under its root, from the names at, is Some
def pl.ins(segs: List<&2, Tl.Seg>, at: List<&2, Nat>, h: {Tl.stays(segs, LA.pl.len(at)) == True{} : Bool}) -> {Maybe.is_some(&2, List<&2, Nat>, Tl.walk(segs, at)) == True{} : Bool}:
  match segs:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Tl.Name{n}:
          pl.ins(rest, n <> at, h)
        case Tl.Here{}:
          pl.ins(rest, at, h)
        case Tl.Up{}:
          match at:
            case Nil{}:
              LBoolMisc.tools.pl.absurdF({Maybe.is_some(&2, List<&2, Nat>, Tl.walk(Tl.Up{} <> rest, Nil{})) == True{} : Bool}, h)
            case a <> above:
              pl.ins(rest, above, h)

def pl.path_resolves_inside(+segs: List<&2, Tl.Seg>, inside: {Tl.stays(segs, 0n) == True{} : Bool}) -> {Maybe.is_some(&2, List<&2, Nat>, Tl.resolve(segs)) == True{} : Bool}:
  pl.ins(segs, Nil{}, inside)

def Tools.path_resolves_inside(segs, inside):
  pl.path_resolves_inside(segs, inside)
