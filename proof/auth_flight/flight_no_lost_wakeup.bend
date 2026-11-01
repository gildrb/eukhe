# eukhe: the proof of LAW flight_no_lost_wakeup
# The open's empty desk has no waiting caller; every event keeps every
# waiting caller's provider in flight: an arrival and a caller that moves
# on keep every flight; a caller joins only a flight in flight; a land or
# an unwind of a leader takes its provider's waiting callers with it, and
# keeps every other provider's flight.

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

def pnl.board(w: Bool, +k: Nat, +j: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +ew: {S.af_inflight(p, cs) == w : Bool}, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, F.Loads{}}} : Maybe<&2, F.Cl>}, h: {MV.mv.led(F.Desk{cs, n}) == True{} : Bool}) -> {MV.mv.led(SS.af_after(S.af_board(w, k, cs, n))) == True{} : Bool}:
  match w:
    case True{}:
      AF.ad.led_setL(k, F.Waits{}, cs, S.af_set(k, F.Waits{}, cs), j, p, F.Loads{}, at, AF.ad.infl_set(p, k, F.Waits{}, cs, j, p, F.Loads{}, at, {==}, ew), AF.ad.led_setC(cs, k, F.Waits{}, cs, j, p, F.Loads{}, at, {==}, h))
    case False{}:
      AF.ad.led_setL(k, F.Checks{}, cs, S.af_set(k, F.Checks{}, cs), j, p, F.Loads{}, at, {==}, AF.ad.led_setC(cs, k, F.Checks{}, cs, j, p, F.Loads{}, at, {==}, h))

def pnl.fit(a: F.At, fd: F.Fd, +k: Nat, +j: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}, h: {MV.mv.led(F.Desk{cs, n}) == True{} : Bool}) -> {MV.mv.led(SS.af_after(S.af_found_fit(S.af_takes(a, fd), fd, k, p, cs, n))) == True{} : Bool}:
  match a:
    case F.Loads{}:
      match fd:
        case F.LoadFresh{}:
          AF.ad.led_cutL(k, cs, S.af_cut(k, cs), AF.ad.led_cutC(cs, k, cs, j, p, F.Loads{}, at, {==}, h))
        case F.LoadExpired{}:
          pnl.board(S.af_inflight(p, cs), k, j, p, cs, n, {==}, at, h)
        case F.LoadFailed{}:
          AF.ad.led_cutL(k, cs, S.af_cut(k, cs), AF.ad.led_cutC(cs, k, cs, j, p, F.Loads{}, at, {==}, h))
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
          AF.ad.led_landC(S.af_cut(k, cs), k, cs, j, p, F.Checks{}, at, {==}, AF.ad.led_cutL(k, cs, cs, h))
        case F.CheckExpired{}:
          AF.ad.led_setL(k, F.Fetches{}, cs, S.af_set(k, F.Fetches{}, cs), j, p, F.Checks{}, at, {==}, AF.ad.led_setC(cs, k, F.Fetches{}, cs, j, p, F.Checks{}, at, {==}, h))
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
          AF.ad.led_setL(k, F.Stores{}, cs, S.af_set(k, F.Stores{}, cs), j, p, F.Fetches{}, at, {==}, AF.ad.led_setC(cs, k, F.Stores{}, cs, j, p, F.Fetches{}, at, {==}, h))
        case F.FetchFailed{}:
          AF.ad.led_landC(S.af_cut(k, cs), k, cs, j, p, F.Fetches{}, at, {==}, AF.ad.led_cutL(k, cs, cs, h))
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
          AF.ad.led_landC(S.af_cut(k, cs), k, cs, j, p, F.Stores{}, at, {==}, AF.ad.led_cutL(k, cs, cs, h))
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

def pnl.found(m: Maybe<&2, F.Cl>, +fd: F.Fd, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == m : Maybe<&2, F.Cl>}, h: {MV.mv.led(F.Desk{cs, n}) == True{} : Bool}) -> {MV.mv.led(SS.af_after(S.af_found_at(m, fd, k, cs, n))) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{x}:
      match x:
        case F.Cl{+j, +p, +a}:
          pnl.fit(a, fd, k, j, p, cs, n, at, h)

def pnl.unwind(m: Maybe<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == m : Maybe<&2, F.Cl>}, h: {MV.mv.led(F.Desk{cs, n}) == True{} : Bool}) -> {MV.mv.led(SS.af_after(S.af_unwind_at(m, k, cs, n))) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{x}:
      match x:
        case F.Cl{+j, +p, a}:
          match a:
            case F.Loads{}:
              AF.ad.led_cutL(k, cs, S.af_cut(k, cs), AF.ad.led_cutC(cs, k, cs, j, p, F.Loads{}, at, {==}, h))
            case F.Checks{}:
              AF.ad.led_landC(S.af_cut(k, cs), k, cs, j, p, F.Checks{}, at, {==}, AF.ad.led_cutL(k, cs, cs, h))
            case F.Fetches{}:
              AF.ad.led_landC(S.af_cut(k, cs), k, cs, j, p, F.Fetches{}, at, {==}, AF.ad.led_cutL(k, cs, cs, h))
            case F.Stores{}:
              AF.ad.led_landC(S.af_cut(k, cs), k, cs, j, p, F.Stores{}, at, {==}, AF.ad.led_cutL(k, cs, cs, h))
            case F.Waits{}:
              AF.ad.led_cutL(k, cs, S.af_cut(k, cs), AF.ad.led_cutC(cs, k, cs, j, p, F.Waits{}, at, {==}, h))

def pnl.step(d: F.Desk, e: F.DEv, h: {MV.mv.led(d) == True{} : Bool}) -> {MV.mv.led(SS.af_after(S.af_desk(d, e))) == True{} : Bool}:
  match d:
    case F.Desk{+cs, +n}:
      match e:
        case F.Comes{+p}:
          AF.ad.led_arrive(cs, n, p, cs, h)
        case F.Found{+k, +fd}:
          pnl.found(S.af_find(k, cs), fd, k, cs, n, {==}, h)
        case F.Unwinds{+k}:
          pnl.unwind(S.af_find(k, cs), k, cs, n, {==}, h)
        case F.Joiners{+p}:
          h

def pnl.step_code(+d: F.Desk, +e: F.DEv, h: {MV.mv.led(d) == True{} : Bool}) -> {MV.mv.led(SS.af_after(F.desk.step(d, e))) == True{} : Bool}:
  %Equal.sym(F.DRes, F.desk.step(d, e), S.af_desk(d, e), LAE.ae.desk(d, e)) : {MV.mv.led(SS.af_after(_)) == True{} : Bool}
  pnl.step(d, e, h)

# every run keeps every waiting caller led
def pnl.run(evs: List<&2, F.DEv>, +d: F.Desk, h: {MV.mv.led(d) == True{} : Bool}) -> {MV.mv.led(SS.af_go(evs, d)) == True{} : Bool}:
  match evs:
    case Nil{}:
      h
    case +e <> rest:
      pnl.run(rest, SS.af_after(F.desk.step(d, e)), pnl.step_code(d, e, h))

def pnl.cs_led(d: F.Desk, h: {MV.mv.led(d) == True{} : Bool}) -> {SS.af_led_all(S.af_cs(d), S.af_cs(d)) == True{} : Bool}:
  match d:
    case F.Desk{cs, m}:
      h

def AuthFlightSafety.flight_no_lost_wakeup(evs):
  pnl.cs_led(SS.af_run(evs), pnl.run(evs, F.Desk{Nil{}, 0n}, {==}))

