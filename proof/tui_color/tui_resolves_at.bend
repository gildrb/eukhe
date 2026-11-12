# eukhe: the proof of LAW tui_resolves_at
# Induction on p: each entry of p in front shifts the role's index by one;
# with p empty the role is the entry x itself.

import Base
import ../../bend/theme/file.bend as TFile
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor

def rsa.at(+p: List<&2, Maybe<&2, TFile.Val>>, +x: Maybe<&2, TFile.Val>, +q: List<&2, Maybe<&2, TFile.Val>>) -> {TC.resolves(TuiColor.cat(Maybe<&2, TFile.Val>, p, x <> q), [List.length(&2, Maybe<&2, TFile.Val>, p)]) == Maybe.is_some(&2, TFile.Val, x) : Bool}:
  match p:
    case Nil{}:
      match x:
        case None{}:
          {==}
        case Some{v}:
          {==}
    case Con{y, rest}:
      rsa.at(rest, x, q)

def TuiColor.tui_resolves_at(p, x, q):
  rsa.at(p, x, q)
