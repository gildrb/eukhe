# eukhe: the proof of LAW adopt_same_build

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ../base/logic/nat.bend as LLogicNat

# (D1) adopt_same_build
# ---------------------

def ps.AD(x: La.Adoption, A: Type) -> Type:
  match x:
    case La.Adopt{}:
      A
    case La.Replace{}:
      Unit

def ps.not_adopted(-A: Type, e: {La.Replace{} == La.Adopt{} : La.Adoption}) -> A:
  %e : ps.AD(_, A)
  Unit{}

def ps.adopt_put(same: Bool, +b: Nat, +sup: Nat, e: {Nat.is_eq(b, sup) == same : Bool}, adopted: {La.adopt.put(same) == La.Adopt{} : La.Adoption}) -> {Some{b} == Some{sup} : Maybe<&2, Nat>}:
  match same:
    case True{}:
      Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, b, sup, LLogicNat.supervisor.ps.eq_of_is_eq(b, sup, e))
    case False{}:
      ps.not_adopted({Some{b} == Some{sup} : Maybe<&2, Nat>}, adopted)

def ps.adopt_same_build(+sup: Nat, w: Maybe<&2, Nat>, adopted: {La.adoption(sup, w) == La.Adopt{} : La.Adoption}) -> {w == Some{sup} : Maybe<&2, Nat>}:
  match w:
    case None{}:
      ps.not_adopted({None{} == Some{sup} : Maybe<&2, Nat>}, adopted)
    case Some{+b}:
      ps.adopt_put(Nat.is_eq(b, sup), b, sup, {==}, adopted)

def Launcher.adopt_same_build(sup, w, adopted):
  ps.adopt_same_build(sup, w, adopted)
