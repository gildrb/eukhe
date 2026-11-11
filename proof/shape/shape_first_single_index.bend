# eukhe: the proof of LAW shape_first_single_index
#
# PROOF: a list of one shape answers none (no Some to match the premise) or
# that shape's fit at index 0 (the premise's index, read off by
# LE.sfe.found_i).

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ../../laws/shape/search.bend as ShapeSearch
import ./base/earliest.bend as LE

def ssi.at(x: Maybe<&2, S.Hit>, +i: Nat, +f: S.Fit, h: {S.first.hit(x, 0n, k => None{}) == Some{S.Found{i, f}} : Maybe<&2, S.Found>}) -> {i == 0n : Nat}:
  match x:
    case None{}:
      LE.sfe.none_some({i == 0n : Nat}, S.Found{i, f}, h)
    case Some{y}:
      match y:
        case S.Hit{+r, +p}:
          Equal.sym(Nat, 0n, i, Equal.cong(Maybe<&2, S.Found>, Nat, m => LE.sfe.found_i(m), Some{S.Found{0n, S.fit(p, r)}}, Some{S.Found{i, f}}, h))

def ShapeSearch.shape_first_single_index(sh, text, i, f, h):
  ssi.at(S.first.shape(sh, text, String.length(text)), i, f, h)
