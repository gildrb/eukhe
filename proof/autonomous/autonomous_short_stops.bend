# eukhe: the proof of LAW autonomous_short_stops
#
# PROOF: by cases on the checks: without a claim that ended, a short budget stops the run; an ended claim contradicts the premise.

import Base
import ../../bend/verify.bend as V
import ../../bend/autonomous.bend as Au
import ../../bend/ffi_autonomous.bend as FAu
import ../../bend/wire.bend as Wr
import ../../spec/autonomous/autonomous.bend as SpA
import ../../laws/autonomous.bend as Autonomous
import ./base.bend as LAAutonomous

def au.BI(x: Bool, G: Type) -> Type:
  match x:
    case True{}:
      Unit
    case False{}:
      G

def au.ended_false(-l: V.Label, -G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : au.BI(_, G)
  Unit{}

def Autonomous.autonomous_short_stops(c, h):
  match c:
    case Au.Unchecked{}:
      {==}
    case Au.Returned{}:
      {==}
    case Au.Ended{l}:
      au.ended_false(l, {Au.Stop{Au.ByChecks{l}} == Au.Stop{Au.ByBudget{}} : Au.Step}, h)
