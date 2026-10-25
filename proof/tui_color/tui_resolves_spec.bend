# eukhe: the proof of LAW tui_resolves_spec: per role, the model's lookup
# is the spec's (tr.found, induction on the palette); then induction on
# the roles

import Base
import ../../bend/theme/file.bend as TFile
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor

def tr.head(m: Maybe<&2, TFile.Val>) -> {TC.found(TFile.Val, Some{m}) == TuiColor.tc_is_set(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def tr.found(p: List<&2, Maybe<&2, TFile.Val>>, r: Nat) -> {TC.found(TFile.Val, List.get(&2, Maybe<&2, TFile.Val>, p, r)) == TuiColor.tc_set(p, r) : Bool}:
  match p r:
    case Nil{} _:
      {==}
    case Con{m, t} 0n:
      tr.head(m)
    case Con{m, t} 1n+k:
      tr.found(t, k)

def TuiColor.tui_resolves_spec(p, rs):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, rest}:
      %TuiColor.tui_resolves_spec(p, rest) : {Bool.and(TC.found(TFile.Val, List.get(&2, Maybe<&2, TFile.Val>, p, r)), TC.resolves(p, rest)) == Bool.and(TuiColor.tc_set(p, r), _) : Bool}
      %tr.found(p, r) : {Bool.and(TC.found(TFile.Val, List.get(&2, Maybe<&2, TFile.Val>, p, r)), TC.resolves(p, rest)) == Bool.and(_, TC.resolves(p, rest)) : Bool}
      {==}
