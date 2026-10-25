# eukhe: the proof of LAW flight_done_once
# Every run from the open's empty desk keeps each caller number held once
# and below the next one's (PDS.pid); so an event that ends caller k's
# refresh names k once and leaves k not live, numbered below the next
# caller (PDS.pen); from then on no event names k, and k stays not live
# (PDS.pq, by induction over the later events).

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/entry.bend as S
import ../../laws/auth_flight/safety.bend as SS
import ../../laws/auth_flight/safety.bend as AuthFlightSafety
import ./base/entry.bend as LAE
import ./base/moves.bend as MV
import ./flight_done_once/steps.bend as PDS

def pdo.ids_code(+d: F.Desk, +e: F.DEv, h: {MV.mv.ids(d) == True{} : Bool}) -> {MV.mv.ids(SS.af_after(F.desk.step(d, e))) == True{} : Bool}:
  %Equal.sym(F.DRes, F.desk.step(d, e), S.af_desk(d, e), LAE.ae.desk(d, e)) : {MV.mv.ids(SS.af_after(_)) == True{} : Bool}
  PDS.pid.step(d, e, h)

# every run keeps each number held once and below the next one's
def pdo.ids_run(evs: List<&2, F.DEv>, +d: F.Desk, h: {MV.mv.ids(d) == True{} : Bool}) -> {MV.mv.ids(SS.af_go(evs, d)) == True{} : Bool}:
  match evs:
    case Nil{}:
      h
    case +e <> rest:
      pdo.ids_run(rest, SS.af_after(F.desk.step(d, e)), pdo.ids_code(d, e, h))

def pdo.end_code(+d: F.Desk, +e: F.DEv, +i: Nat, hi: {MV.mv.ids(d) == True{} : Bool}, en: {SS.af_ends(i, SS.af_out(F.desk.step(d, e))) == True{} : Bool}) -> MV.mv.EndGoal(i, F.desk.step(d, e)):
  +eq = LAE.ae.desk(d, e)
  %Equal.sym(F.DRes, F.desk.step(d, e), S.af_desk(d, e), eq) : MV.mv.EndGoal(i, _)
  PDS.pen.step(d, e, i, hi, Equal.trans(Bool, SS.af_ends(i, SS.af_out(S.af_desk(d, e))), SS.af_ends(i, SS.af_out(F.desk.step(d, e))), True{}, Equal.cong(F.DRes, Bool, r => SS.af_ends(i, SS.af_out(r)), S.af_desk(d, e), F.desk.step(d, e), Equal.sym(F.DRes, F.desk.step(d, e), S.af_desk(d, e), eq)), en))

def pdo.quiet_code(+d: F.Desk, +e: F.DEv, +i: Nat, q: ({SS.af_live(i, S.af_cs(d)) == False{} : Bool} & {Nat.is_lt(i, MV.mv.m_of(d)) == True{} : Bool})) -> MV.mv.QGoal(i, F.desk.step(d, e)):
  %Equal.sym(F.DRes, F.desk.step(d, e), S.af_desk(d, e), LAE.ae.desk(d, e)) : MV.mv.QGoal(i, _)
  PDS.pq.step(d, e, i, q)

def pdo.quiet_at(+i: Nat, +o: F.DOut, rest: List<&2, F.DEv>, +d1: F.Desk, t: ({SS.af_names(i, o) == 0n : Nat} & {SS.af_live(i, S.af_cs(d1)) == False{} : Bool} & {Nat.is_lt(i, MV.mv.m_of(d1)) == True{} : Bool}), ih: ({SS.af_live(i, S.af_cs(d1)) == False{} : Bool} & {Nat.is_lt(i, MV.mv.m_of(d1)) == True{} : Bool}) -> ({SS.af_named(i, rest, d1) == False{} : Bool} & {SS.af_live(i, S.af_cs(SS.af_go(rest, d1))) == False{} : Bool})) -> ({Bool.or(Nat.is_lt(0n, SS.af_names(i, o)), SS.af_named(i, rest, d1)) == False{} : Bool} & {SS.af_live(i, S.af_cs(SS.af_go(rest, d1))) == False{} : Bool}):
  (z, dk, lt) = t
  %Equal.sym(Nat, SS.af_names(i, o), 0n, z) : ({Bool.or(Nat.is_lt(0n, _), SS.af_named(i, rest, d1)) == False{} : Bool} & {SS.af_live(i, S.af_cs(SS.af_go(rest, d1))) == False{} : Bool})
  ih((dk, lt))

# from a desk where i is not live and numbered below the next caller, no
# answer names i and i stays not live
def pdo.quiet_run(evs: List<&2, F.DEv>, +d: F.Desk, +i: Nat, q: ({SS.af_live(i, S.af_cs(d)) == False{} : Bool} & {Nat.is_lt(i, MV.mv.m_of(d)) == True{} : Bool})) -> ({SS.af_named(i, evs, d) == False{} : Bool} & {SS.af_live(i, S.af_cs(SS.af_go(evs, d))) == False{} : Bool}):
  match evs:
    case Nil{}:
      (dk, lt) = q
      ({==}, dk)
    case +e <> +rest:
      pdo.quiet_at(i, SS.af_out(F.desk.step(d, e)), rest, SS.af_after(F.desk.step(d, e)), pdo.quiet_code(d, e, i, q), g => pdo.quiet_run(rest, SS.af_after(F.desk.step(d, e)), i, g))

def pdo.fin(+k: Nat, post: List<&2, F.DEv>, +d1: F.Desk, +o: F.DOut, eg: ({SS.af_names(k, o) == 1n : Nat} & {SS.af_live(k, S.af_cs(d1)) == False{} : Bool} & {Nat.is_lt(k, MV.mv.m_of(d1)) == True{} : Bool})) -> ({SS.af_names(k, o) == 1n : Nat} & {SS.af_named(k, post, d1) == False{} : Bool} & {SS.af_live(k, S.af_cs(SS.af_go(post, d1))) == False{} : Bool}):
  (n1, dk, lt) = eg
  (n1, pdo.quiet_run(post, d1, k, (dk, lt)))

def AuthFlightSafety.flight_done_once(pre, e, post, k, ends):
  pdo.fin(k, post, SS.af_after(F.desk.step(SS.af_run(pre), e)), SS.af_out(F.desk.step(SS.af_run(pre), e)), pdo.end_code(SS.af_run(pre), e, k, pdo.ids_run(pre, F.Desk{Nil{}, 0n}, {==}), ends))
