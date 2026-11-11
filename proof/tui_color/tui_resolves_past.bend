# eukhe: the proof of LAW tui_resolves_past
# Induction on the palette and the role together: an empty palette has no
# entry; a role 0 is never past a palette that has an entry.

import Base
import ../../bend/theme/file.bend as TFile
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor
import ../base/logic/logic.bend as LLogicLogic

def rpa.past(+p: List<&2, Maybe<&2, TFile.Val>>, +r: Nat, +past: {Nat.is_le(List.length(&2, Maybe<&2, TFile.Val>, p), r) == True{} : Bool}) -> {TC.resolves(p, [r]) == False{} : Bool}:
  match p r:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{y, rest} 0n:
      LLogicLogic.pu.absurd_ft({TC.resolves(y <> rest, [0n]) == False{} : Bool}, past)
    case Con{y, rest} 1n+j:
      rpa.past(rest, j, past)

def TuiColor.tui_resolves_past(p, r, past):
  rpa.past(p, r, past)
