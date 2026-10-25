# eukhe: the proof of LAW flight_no_caller_dropped
# Split on the event, the found caller, its place and the found: each
# move keeps every caller other than the one it ends (done: the reply
# says so) or the unwinding one (MV.mv.kept_*).

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

# the claim for the answer r
def pnc.G(+i: Nat, +r: F.DRes) -> Type:
  {Bool.or(SS.af_live(i, S.af_cs(SS.af_after(r))), SS.af_ends(i, SS.af_out(r))) == True{} : Bool}


def pnc.board(w: Bool, +k: Nat, -j: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +ew: {S.af_inflight(p, cs) == w : Bool}, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, F.Loads{}}} : Maybe<&2, F.Cl>}, +i: Nat, live: {SS.af_live(i, cs) == True{} : Bool}) -> pnc.G(i, S.af_board(w, k, cs, n)):
  match w:
    case True{}:
      MV.mv.kept_set(i, k, F.Waits{}, cs, F.Acts{[F.To{k, F.DoWait{}}]}, live)
    case False{}:
      MV.mv.kept_set(i, k, F.Checks{}, cs, F.Acts{[F.To{k, F.DoCheck{}}]}, live)

def pnc.fit(a: F.At, fd: F.Fd, +k: Nat, -j: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}, +i: Nat, live: {SS.af_live(i, cs) == True{} : Bool}) -> pnc.G(i, S.af_found_fit(S.af_takes(a, fd), fd, k, p, cs, n)):
  match a:
    case F.Loads{}:
      match fd:
        case F.LoadFresh{}:
          MV.mv.kept_done(i, k, cs, live)
        case F.LoadExpired{}:
          pnc.board(S.af_inflight(p, cs), k, j, p, cs, n, {==}, at, i, live)
        case F.LoadFailed{}:
          MV.mv.kept_done(i, k, cs, live)
        case F.CheckFresh{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.CheckExpired{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.FetchOk{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.FetchFailed{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.Stored{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
    case F.Checks{}:
      match fd:
        case F.LoadFresh{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.LoadExpired{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.LoadFailed{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.CheckFresh{}:
          MV.mv.kept_land(i, k, p, cs, live)
        case F.CheckExpired{}:
          MV.mv.kept_set(i, k, F.Fetches{}, cs, F.Acts{[F.To{k, F.DoFetch{}}]}, live)
        case F.FetchOk{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.FetchFailed{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.Stored{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
    case F.Fetches{}:
      match fd:
        case F.LoadFresh{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.LoadExpired{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.LoadFailed{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.CheckFresh{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.CheckExpired{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.FetchOk{}:
          MV.mv.kept_set(i, k, F.Stores{}, cs, F.Acts{[F.To{k, F.DoStore{}}]}, live)
        case F.FetchFailed{}:
          MV.mv.kept_land(i, k, p, cs, live)
        case F.Stored{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
    case F.Stores{}:
      match fd:
        case F.LoadFresh{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.LoadExpired{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.LoadFailed{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.CheckFresh{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.CheckExpired{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.FetchOk{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.FetchFailed{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.Stored{}:
          MV.mv.kept_land(i, k, p, cs, live)
    case F.Waits{}:
      match fd:
        case F.LoadFresh{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.LoadExpired{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.LoadFailed{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.CheckFresh{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.CheckExpired{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.FetchOk{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.FetchFailed{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)
        case F.Stored{}:
          MV.mv.kept_live(i, cs, F.Off{}, live)

def pnc.found(m: Maybe<&2, F.Cl>, +fd: F.Fd, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == m : Maybe<&2, F.Cl>}, +i: Nat, live: {SS.af_live(i, cs) == True{} : Bool}) -> pnc.G(i, S.af_found_at(m, fd, k, cs, n)):
  match m:
    case None{}:
      MV.mv.kept_live(i, cs, F.Off{}, live)
    case Some{x}:
      match x:
        case F.Cl{+j, +p, +a}:
          pnc.fit(a, fd, k, j, p, cs, n, at, i, live)

def pnc.unwind(m: Maybe<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == m : Maybe<&2, F.Cl>}, +i: Nat, live: {SS.af_live(i, cs) == True{} : Bool}, +ne: {Nat.is_eq(k, i) == False{} : Bool}) -> pnc.G(i, S.af_unwind_at(m, k, cs, n)):
  match m:
    case None{}:
      MV.mv.kept_live(i, cs, F.Off{}, live)
    case Some{x}:
      match x:
        case F.Cl{+j, +p, a}:
          match a:
            case F.Loads{}:
              MV.mv.kept_unwind_nl(i, k, cs, ne, live)
            case F.Checks{}:
              MV.mv.kept_unwind_lead(i, k, p, cs, ne, live)
            case F.Fetches{}:
              MV.mv.kept_unwind_lead(i, k, p, cs, ne, live)
            case F.Stores{}:
              MV.mv.kept_unwind_lead(i, k, p, cs, ne, live)
            case F.Waits{}:
              MV.mv.kept_unwind_nl(i, k, cs, ne, live)

def pnc.step(d: F.Desk, e: F.DEv, +i: Nat, live: {SS.af_live(i, S.af_cs(d)) == True{} : Bool}, stays: {SS.af_unwinds(e, i) == False{} : Bool}) -> pnc.G(i, S.af_desk(d, e)):
  match d:
    case F.Desk{+cs, +n}:
      match e:
        case F.Comes{+p}:
          MV.mv.kept_live(i, F.Cl{n, p, F.Loads{}} <> cs, F.Acts{[F.To{n, F.DoLoad{}}]}, AL.ad.or_r(Nat.is_eq(n, i), SS.af_live(i, cs), live))
        case F.Found{+k, +fd}:
          pnc.found(S.af_find(k, cs), fd, k, cs, n, {==}, i, live)
        case F.Unwinds{+k}:
          pnc.unwind(S.af_find(k, cs), k, cs, n, {==}, i, live, stays)
        case F.Joiners{+p}:
          MV.mv.kept_live(i, cs, F.Joined{S.af_joiners(S.af_inflight(p, cs), p, cs)}, live)

def AuthFlightSafety.flight_no_caller_dropped(d, e, j, live, stays):
  %Equal.sym(F.DRes, F.desk.step(d, e), S.af_desk(d, e), LAE.ae.desk(d, e)) : pnc.G(j, _)
  pnc.step(d, e, j, live, stays)

