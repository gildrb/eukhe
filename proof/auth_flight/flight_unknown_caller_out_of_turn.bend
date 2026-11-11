# eukhe: the proof of LAW flight_unknown_caller_out_of_turn
# No live caller is numbered k, so the desk finds none (FR.fr.find_none):
# a found and an unwind are out of turn, the desk kept.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/desk.bend as AuthFlightDesk
import ../../laws/auth_flight/safety.bend as SS
import ./base/frame.bend as FR

def puo.found(+cs: List<&2, F.Cl>, +n: Nat, +k: Nat, +fd: F.Fd, g: {SS.af_live(k, cs) == False{} : Bool}) -> {F.desk.step(F.Desk{cs, n}, F.Found{k, fd}) == F.DRes{F.Desk{cs, n}, F.Off{}} : F.DRes}:
  %Equal.sym(Maybe<&2, F.Cl>, F.find(k, cs), None{}, FR.fr.find_none(k, cs, g)) : {F.found(_, fd, k, cs, n) == F.DRes{F.Desk{cs, n}, F.Off{}} : F.DRes}
  {==}

def puo.unwind(+cs: List<&2, F.Cl>, +n: Nat, +k: Nat, g: {SS.af_live(k, cs) == False{} : Bool}) -> {F.desk.step(F.Desk{cs, n}, F.Unwinds{k}) == F.DRes{F.Desk{cs, n}, F.Off{}} : F.DRes}:
  %Equal.sym(Maybe<&2, F.Cl>, F.find(k, cs), None{}, FR.fr.find_none(k, cs, g)) : {F.unwind(_, k, cs, n) == F.DRes{F.Desk{cs, n}, F.Off{}} : F.DRes}
  {==}

def AuthFlightDesk.flight_unknown_caller_out_of_turn(cs, n, k, gone, fd):
  +g = gone
  (puo.found(cs, n, k, fd, g), puo.unwind(cs, n, k, g))
