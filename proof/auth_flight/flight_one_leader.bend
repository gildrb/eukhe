# eukhe: the proof of LAW flight_one_leader
# The open's empty desk has no leader; every event keeps at most one
# leader per provider: an arrival, a waiting caller and a found that moves
# a leader on add none; a loading caller leads only a provider with no
# flight in flight; a cut, a land and an unwind only remove leaders.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/entry.bend as S
import ../../laws/auth_flight/safety.bend as SS
import ./base/entry.bend as LAE
import ./base/logic.bend as AL
import ./base/callers.bend as AC
import ./base/flights.bend as AF
import ./base/moves.bend as MV

import ../../laws/auth_flight/safety.bend as AuthFlightSafety

def pol.board(w: Bool, +k: Nat, -j: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +ew: {S.af_inflight(p, cs) == w : Bool}, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, F.Loads{}}} : Maybe<&2, F.Cl>}, h: MV.mv.Lead(F.Desk{cs, n})) -> MV.mv.Lead(SS.af_after(S.af_board(w, k, cs, n))):
  match w:
    case True{}:
      +q => MV.mv.le1_eq(SS.af_leaders(q, S.af_set(k, F.Waits{}, cs)), SS.af_leaders(q, cs), AF.ad.lead_set_same(q, k, F.Waits{}, cs, j, p, F.Loads{}, at, {==}), h(q))
    case False{}:
      +q => MV.mv.lead_gain(q, k, cs, j, p, at, ew, h(q))

def pol.fit(a: F.At, fd: F.Fd, +k: Nat, -j: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}, h: MV.mv.Lead(F.Desk{cs, n})) -> MV.mv.Lead(SS.af_after(S.af_found_fit(S.af_takes(a, fd), fd, k, p, cs, n))):
  match a:
    case F.Loads{}:
      match fd:
        case F.LoadFresh{}:
          +q => AL.ad.le_trans(SS.af_leaders(q, S.af_cut(k, cs)), SS.af_leaders(q, cs), 1n, AF.ad.lead_cut_le(q, k, cs), h(q))
        case F.LoadExpired{}:
          pol.board(S.af_inflight(p, cs), k, j, p, cs, n, {==}, at, h)
        case F.LoadFailed{}:
          +q => AL.ad.le_trans(SS.af_leaders(q, S.af_cut(k, cs)), SS.af_leaders(q, cs), 1n, AF.ad.lead_cut_le(q, k, cs), h(q))
        case F.CheckFresh{}:
          h
        case F.CheckExpired{}:
          h
        case F.FetchOk{}:
          h
        case F.FetchFailed{}:
          h
        case F.Stored{}:
          h
    case F.Checks{}:
      match fd:
        case F.LoadFresh{}:
          h
        case F.LoadExpired{}:
          h
        case F.LoadFailed{}:
          h
        case F.CheckFresh{}:
          +q => AL.ad.le_trans(SS.af_leaders(q, S.af_unwait(p, S.af_cut(k, cs))), SS.af_leaders(q, S.af_cut(k, cs)), 1n, AF.ad.lead_unwait_le(q, p, S.af_cut(k, cs)), AL.ad.le_trans(SS.af_leaders(q, S.af_cut(k, cs)), SS.af_leaders(q, cs), 1n, AF.ad.lead_cut_le(q, k, cs), h(q)))
        case F.CheckExpired{}:
          +q => MV.mv.le1_eq(SS.af_leaders(q, S.af_set(k, F.Fetches{}, cs)), SS.af_leaders(q, cs), AF.ad.lead_set_same(q, k, F.Fetches{}, cs, j, p, F.Checks{}, at, {==}), h(q))
        case F.FetchOk{}:
          h
        case F.FetchFailed{}:
          h
        case F.Stored{}:
          h
    case F.Fetches{}:
      match fd:
        case F.LoadFresh{}:
          h
        case F.LoadExpired{}:
          h
        case F.LoadFailed{}:
          h
        case F.CheckFresh{}:
          h
        case F.CheckExpired{}:
          h
        case F.FetchOk{}:
          +q => MV.mv.le1_eq(SS.af_leaders(q, S.af_set(k, F.Stores{}, cs)), SS.af_leaders(q, cs), AF.ad.lead_set_same(q, k, F.Stores{}, cs, j, p, F.Fetches{}, at, {==}), h(q))
        case F.FetchFailed{}:
          +q => AL.ad.le_trans(SS.af_leaders(q, S.af_unwait(p, S.af_cut(k, cs))), SS.af_leaders(q, S.af_cut(k, cs)), 1n, AF.ad.lead_unwait_le(q, p, S.af_cut(k, cs)), AL.ad.le_trans(SS.af_leaders(q, S.af_cut(k, cs)), SS.af_leaders(q, cs), 1n, AF.ad.lead_cut_le(q, k, cs), h(q)))
        case F.Stored{}:
          h
    case F.Stores{}:
      match fd:
        case F.LoadFresh{}:
          h
        case F.LoadExpired{}:
          h
        case F.LoadFailed{}:
          h
        case F.CheckFresh{}:
          h
        case F.CheckExpired{}:
          h
        case F.FetchOk{}:
          h
        case F.FetchFailed{}:
          h
        case F.Stored{}:
          +q => AL.ad.le_trans(SS.af_leaders(q, S.af_unwait(p, S.af_cut(k, cs))), SS.af_leaders(q, S.af_cut(k, cs)), 1n, AF.ad.lead_unwait_le(q, p, S.af_cut(k, cs)), AL.ad.le_trans(SS.af_leaders(q, S.af_cut(k, cs)), SS.af_leaders(q, cs), 1n, AF.ad.lead_cut_le(q, k, cs), h(q)))
    case F.Waits{}:
      match fd:
        case F.LoadFresh{}:
          h
        case F.LoadExpired{}:
          h
        case F.LoadFailed{}:
          h
        case F.CheckFresh{}:
          h
        case F.CheckExpired{}:
          h
        case F.FetchOk{}:
          h
        case F.FetchFailed{}:
          h
        case F.Stored{}:
          h

def pol.found(m: Maybe<&2, F.Cl>, +fd: F.Fd, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == m : Maybe<&2, F.Cl>}, h: MV.mv.Lead(F.Desk{cs, n})) -> MV.mv.Lead(SS.af_after(S.af_found_at(m, fd, k, cs, n))):
  match m:
    case None{}:
      h
    case Some{x}:
      match x:
        case F.Cl{+j, +p, +a}:
          pol.fit(a, fd, k, j, p, cs, n, at, h)

def pol.unwind(m: Maybe<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == m : Maybe<&2, F.Cl>}, h: MV.mv.Lead(F.Desk{cs, n})) -> MV.mv.Lead(SS.af_after(S.af_unwind_at(m, k, cs, n))):
  match m:
    case None{}:
      h
    case Some{x}:
      match x:
        case F.Cl{+j, +p, a}:
          match a:
            case F.Loads{}:
              +q => AL.ad.le_trans(SS.af_leaders(q, S.af_cut(k, cs)), SS.af_leaders(q, cs), 1n, AF.ad.lead_cut_le(q, k, cs), h(q))
            case F.Checks{}:
              +q => AL.ad.le_trans(SS.af_leaders(q, S.af_unwait(p, S.af_cut(k, cs))), SS.af_leaders(q, S.af_cut(k, cs)), 1n, AF.ad.lead_unwait_le(q, p, S.af_cut(k, cs)), AL.ad.le_trans(SS.af_leaders(q, S.af_cut(k, cs)), SS.af_leaders(q, cs), 1n, AF.ad.lead_cut_le(q, k, cs), h(q)))
            case F.Fetches{}:
              +q => AL.ad.le_trans(SS.af_leaders(q, S.af_unwait(p, S.af_cut(k, cs))), SS.af_leaders(q, S.af_cut(k, cs)), 1n, AF.ad.lead_unwait_le(q, p, S.af_cut(k, cs)), AL.ad.le_trans(SS.af_leaders(q, S.af_cut(k, cs)), SS.af_leaders(q, cs), 1n, AF.ad.lead_cut_le(q, k, cs), h(q)))
            case F.Stores{}:
              +q => AL.ad.le_trans(SS.af_leaders(q, S.af_unwait(p, S.af_cut(k, cs))), SS.af_leaders(q, S.af_cut(k, cs)), 1n, AF.ad.lead_unwait_le(q, p, S.af_cut(k, cs)), AL.ad.le_trans(SS.af_leaders(q, S.af_cut(k, cs)), SS.af_leaders(q, cs), 1n, AF.ad.lead_cut_le(q, k, cs), h(q)))
            case F.Waits{}:
              +q => AL.ad.le_trans(SS.af_leaders(q, S.af_cut(k, cs)), SS.af_leaders(q, cs), 1n, AF.ad.lead_cut_le(q, k, cs), h(q))

def pol.step(d: F.Desk, e: F.DEv, h: MV.mv.Lead(d)) -> MV.mv.Lead(SS.af_after(S.af_desk(d, e))):
  match d:
    case F.Desk{+cs, +n}:
      match e:
        case F.Comes{+p}:
          +q => h(q)
        case F.Found{+k, +fd}:
          pol.found(S.af_find(k, cs), fd, k, cs, n, {==}, h)
        case F.Unwinds{+k}:
          pol.unwind(S.af_find(k, cs), k, cs, n, {==}, h)
        case F.Joiners{+p}:
          h

def pol.step_code(+d: F.Desk, +e: F.DEv, h: MV.mv.Lead(d)) -> MV.mv.Lead(SS.af_after(F.desk.step(d, e))):
  %Equal.sym(F.DRes, F.desk.step(d, e), S.af_desk(d, e), LAE.ae.desk(d, e)) : MV.mv.Lead(SS.af_after(_))
  pol.step(d, e, h)

# every run keeps one leader per provider
def pol.run(evs: List<&2, F.DEv>, +d: F.Desk, h: MV.mv.Lead(d)) -> MV.mv.Lead(SS.af_go(evs, d)):
  match evs:
    case Nil{}:
      h
    case +e <> rest:
      pol.run(rest, SS.af_after(F.desk.step(d, e)), pol.step_code(d, e, h))

def AuthFlightSafety.flight_one_leader(evs, p):
  pol.run(evs, F.Desk{Nil{}, 0n}, q => {==})(p)

