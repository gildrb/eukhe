# eukhe: lemmas of the proof of LAW flight_done_once: every event keeps
# each number held once and below the next one's (pid), an event that
# ends caller i's refresh names i once, leaves it not live and numbered
# below the next caller (pen), and an event from a desk where i is not
# live and numbered below the next caller names no i and keeps it so
# (pq).

import Base
import ../../../bend/auth_flight.bend as F
import ../../../laws/auth_flight/entry.bend as S
import ../../../laws/auth_flight/safety.bend as SS
import ../base/entry.bend as LAE
import ../base/logic.bend as AL
import ../base/callers.bend as AC
import ../base/flights.bend as AF
import ../base/moves.bend as MV




def pid.board(w: Bool, +k: Nat, -j: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +ew: {S.af_inflight(p, cs) == w : Bool}, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, F.Loads{}}} : Maybe<&2, F.Cl>}, h: {MV.mv.ids(F.Desk{cs, n}) == True{} : Bool}) -> {MV.mv.ids(SS.af_after(S.af_board(w, k, cs, n))) == True{} : Bool}:
  match w:
    case True{}:
      MV.mv.ids_set(k, F.Waits{}, cs, n, h)
    case False{}:
      MV.mv.ids_set(k, F.Checks{}, cs, n, h)

def pid.fit(a: F.At, fd: F.Fd, +k: Nat, -j: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}, h: {MV.mv.ids(F.Desk{cs, n}) == True{} : Bool}) -> {MV.mv.ids(SS.af_after(S.af_found_fit(S.af_takes(a, fd), fd, k, p, cs, n))) == True{} : Bool}:
  match a:
    case F.Loads{}:
      match fd:
        case F.LoadFresh{}:
          MV.mv.ids_cut(k, cs, n, h)
        case F.LoadExpired{}:
          pid.board(S.af_inflight(p, cs), k, j, p, cs, n, {==}, at, h)
        case F.LoadFailed{}:
          MV.mv.ids_cut(k, cs, n, h)
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
          MV.mv.ids_land(k, p, cs, n, h)
        case F.CheckExpired{}:
          MV.mv.ids_set(k, F.Fetches{}, cs, n, h)
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
          MV.mv.ids_set(k, F.Stores{}, cs, n, h)
        case F.FetchFailed{}:
          MV.mv.ids_land(k, p, cs, n, h)
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
          MV.mv.ids_land(k, p, cs, n, h)
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

def pid.found(m: Maybe<&2, F.Cl>, +fd: F.Fd, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == m : Maybe<&2, F.Cl>}, h: {MV.mv.ids(F.Desk{cs, n}) == True{} : Bool}) -> {MV.mv.ids(SS.af_after(S.af_found_at(m, fd, k, cs, n))) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{x}:
      match x:
        case F.Cl{+j, +p, +a}:
          pid.fit(a, fd, k, j, p, cs, n, at, h)

def pid.unwind(m: Maybe<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == m : Maybe<&2, F.Cl>}, h: {MV.mv.ids(F.Desk{cs, n}) == True{} : Bool}) -> {MV.mv.ids(SS.af_after(S.af_unwind_at(m, k, cs, n))) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{x}:
      match x:
        case F.Cl{+j, +p, a}:
          match a:
            case F.Loads{}:
              MV.mv.ids_cut(k, cs, n, h)
            case F.Checks{}:
              MV.mv.ids_land(k, p, cs, n, h)
            case F.Fetches{}:
              MV.mv.ids_land(k, p, cs, n, h)
            case F.Stores{}:
              MV.mv.ids_land(k, p, cs, n, h)
            case F.Waits{}:
              MV.mv.ids_cut(k, cs, n, h)

def pid.step(d: F.Desk, e: F.DEv, h: {MV.mv.ids(d) == True{} : Bool}) -> {MV.mv.ids(SS.af_after(S.af_desk(d, e))) == True{} : Bool}:
  match d:
    case F.Desk{+cs, +n}:
      match e:
        case F.Comes{+p}:
          MV.mv.ids_arrive(n, p, cs, h)
        case F.Found{+k, +fd}:
          pid.found(S.af_find(k, cs), fd, k, cs, n, {==}, h)
        case F.Unwinds{+k}:
          pid.unwind(S.af_find(k, cs), k, cs, n, {==}, h)
        case F.Joiners{+p}:
          h





def pen.board(w: Bool, +k: Nat, -j: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +ew: {S.af_inflight(p, cs) == w : Bool}, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, F.Loads{}}} : Maybe<&2, F.Cl>}, +i: Nat, hi: {MV.mv.ids(F.Desk{cs, n}) == True{} : Bool}, en: {SS.af_ends(i, SS.af_out(S.af_board(w, k, cs, n))) == True{} : Bool}) -> MV.mv.EndGoal(i, S.af_board(w, k, cs, n)):
  match w:
    case True{}:
      MV.mv.no_end1(MV.mv.EndGoal(i, F.DRes{F.Desk{S.af_set(k, F.Waits{}, cs), n}, F.Acts{[F.To{k, F.DoWait{}}]}}), Nat.is_eq(k, i), en)
    case False{}:
      MV.mv.no_end1(MV.mv.EndGoal(i, F.DRes{F.Desk{S.af_set(k, F.Checks{}, cs), n}, F.Acts{[F.To{k, F.DoCheck{}}]}}), Nat.is_eq(k, i), en)

def pen.fit(a: F.At, fd: F.Fd, +k: Nat, -j: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}, +i: Nat, hi: {MV.mv.ids(F.Desk{cs, n}) == True{} : Bool}, en: {SS.af_ends(i, SS.af_out(S.af_found_fit(S.af_takes(a, fd), fd, k, p, cs, n))) == True{} : Bool}) -> MV.mv.EndGoal(i, S.af_found_fit(S.af_takes(a, fd), fd, k, p, cs, n)):
  match a:
    case F.Loads{}:
      match fd:
        case F.LoadFresh{}:
          MV.mv.end_done(i, k, cs, n, F.Cl{j, p, F.Loads{}}, at, hi, en)
        case F.LoadExpired{}:
          pen.board(S.af_inflight(p, cs), k, j, p, cs, n, {==}, at, i, hi, en)
        case F.LoadFailed{}:
          MV.mv.end_done(i, k, cs, n, F.Cl{j, p, F.Loads{}}, at, hi, en)
        case F.CheckFresh{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.CheckExpired{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.FetchOk{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.FetchFailed{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.Stored{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
    case F.Checks{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.LoadExpired{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.LoadFailed{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.CheckFresh{}:
          MV.mv.end_land(i, k, p, cs, n, F.Cl{j, p, F.Checks{}}, at, hi, en)
        case F.CheckExpired{}:
          MV.mv.no_end1(MV.mv.EndGoal(i, F.DRes{F.Desk{S.af_set(k, F.Fetches{}, cs), n}, F.Acts{[F.To{k, F.DoFetch{}}]}}), Nat.is_eq(k, i), en)
        case F.FetchOk{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.FetchFailed{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.Stored{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
    case F.Fetches{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.LoadExpired{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.LoadFailed{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.CheckFresh{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.CheckExpired{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.FetchOk{}:
          MV.mv.no_end1(MV.mv.EndGoal(i, F.DRes{F.Desk{S.af_set(k, F.Stores{}, cs), n}, F.Acts{[F.To{k, F.DoStore{}}]}}), Nat.is_eq(k, i), en)
        case F.FetchFailed{}:
          MV.mv.end_land(i, k, p, cs, n, F.Cl{j, p, F.Fetches{}}, at, hi, en)
        case F.Stored{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
    case F.Stores{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.LoadExpired{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.LoadFailed{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.CheckFresh{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.CheckExpired{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.FetchOk{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.FetchFailed{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.Stored{}:
          MV.mv.end_land(i, k, p, cs, n, F.Cl{j, p, F.Stores{}}, at, hi, en)
    case F.Waits{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.LoadExpired{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.LoadFailed{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.CheckFresh{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.CheckExpired{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.FetchOk{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.FetchFailed{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
        case F.Stored{}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)

def pen.found(m: Maybe<&2, F.Cl>, +fd: F.Fd, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == m : Maybe<&2, F.Cl>}, +i: Nat, hi: {MV.mv.ids(F.Desk{cs, n}) == True{} : Bool}, en: {SS.af_ends(i, SS.af_out(S.af_found_at(m, fd, k, cs, n))) == True{} : Bool}) -> MV.mv.EndGoal(i, S.af_found_at(m, fd, k, cs, n)):
  match m:
    case None{}:
      LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
    case Some{x}:
      match x:
        case F.Cl{+j, +p, +a}:
          pen.fit(a, fd, k, j, p, cs, n, at, i, hi, en)

def pen.unwind(m: Maybe<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == m : Maybe<&2, F.Cl>}, +i: Nat, hi: {MV.mv.ids(F.Desk{cs, n}) == True{} : Bool}, en: {SS.af_ends(i, SS.af_out(S.af_unwind_at(m, k, cs, n))) == True{} : Bool}) -> MV.mv.EndGoal(i, S.af_unwind_at(m, k, cs, n)):
  match m:
    case None{}:
      LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Off{}}), en)
    case Some{x}:
      match x:
        case F.Cl{+j, +p, a}:
          match a:
            case F.Loads{}:
              LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{S.af_cut(k, cs), n}, F.Acts{Nil{}}}), en)
            case F.Checks{}:
              MV.mv.end_unwind(i, k, p, cs, n, hi, en)
            case F.Fetches{}:
              MV.mv.end_unwind(i, k, p, cs, n, hi, en)
            case F.Stores{}:
              MV.mv.end_unwind(i, k, p, cs, n, hi, en)
            case F.Waits{}:
              LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{S.af_cut(k, cs), n}, F.Acts{Nil{}}}), en)

def pen.step(d: F.Desk, e: F.DEv, +i: Nat, hi: {MV.mv.ids(d) == True{} : Bool}, en: {SS.af_ends(i, SS.af_out(S.af_desk(d, e))) == True{} : Bool}) -> MV.mv.EndGoal(i, S.af_desk(d, e)):
  match d:
    case F.Desk{+cs, +n}:
      match e:
        case F.Comes{+p}:
          MV.mv.no_end1(MV.mv.EndGoal(i, F.DRes{F.Desk{F.Cl{n, p, F.Loads{}} <> cs, 1n+n}, F.Acts{[F.To{n, F.DoLoad{}}]}}), Nat.is_eq(n, i), en)
        case F.Found{+k, +fd}:
          pen.found(S.af_find(k, cs), fd, k, cs, n, {==}, i, hi, en)
        case F.Unwinds{+k}:
          pen.unwind(S.af_find(k, cs), k, cs, n, {==}, i, hi, en)
        case F.Joiners{+p}:
          LAE.ae.ft(MV.mv.EndGoal(i, F.DRes{F.Desk{cs, n}, F.Joined{S.af_joiners(S.af_inflight(p, cs), p, cs)}}), en)





def pq.board(w: Bool, +k: Nat, -j: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +ew: {S.af_inflight(p, cs) == w : Bool}, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, F.Loads{}}} : Maybe<&2, F.Cl>}, +i: Nat, q: ({SS.af_live(i, cs) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})) -> MV.mv.QGoal(i, S.af_board(w, k, cs, n)):
  match w:
    case True{}:
      MV.mv.q_set(i, k, F.Waits{}, F.DoWait{}, cs, n, F.Cl{j, p, F.Loads{}}, at, q)
    case False{}:
      MV.mv.q_set(i, k, F.Checks{}, F.DoCheck{}, cs, n, F.Cl{j, p, F.Loads{}}, at, q)

def pq.fit(a: F.At, fd: F.Fd, +k: Nat, -j: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}, +i: Nat, q: ({SS.af_live(i, cs) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})) -> MV.mv.QGoal(i, S.af_found_fit(S.af_takes(a, fd), fd, k, p, cs, n)):
  match a:
    case F.Loads{}:
      match fd:
        case F.LoadFresh{}:
          MV.mv.q_cut1(i, k, F.DoDone{}, cs, n, F.Cl{j, p, F.Loads{}}, at, q)
        case F.LoadExpired{}:
          pq.board(S.af_inflight(p, cs), k, j, p, cs, n, {==}, at, i, q)
        case F.LoadFailed{}:
          MV.mv.q_cut1(i, k, F.DoDone{}, cs, n, F.Cl{j, p, F.Loads{}}, at, q)
        case F.CheckFresh{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.CheckExpired{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.FetchOk{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.FetchFailed{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.Stored{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
    case F.Checks{}:
      match fd:
        case F.LoadFresh{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.LoadExpired{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.LoadFailed{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.CheckFresh{}:
          MV.mv.q_land(i, k, p, cs, n, F.Cl{j, p, F.Checks{}}, at, q)
        case F.CheckExpired{}:
          MV.mv.q_set(i, k, F.Fetches{}, F.DoFetch{}, cs, n, F.Cl{j, p, F.Checks{}}, at, q)
        case F.FetchOk{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.FetchFailed{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.Stored{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
    case F.Fetches{}:
      match fd:
        case F.LoadFresh{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.LoadExpired{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.LoadFailed{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.CheckFresh{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.CheckExpired{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.FetchOk{}:
          MV.mv.q_set(i, k, F.Stores{}, F.DoStore{}, cs, n, F.Cl{j, p, F.Fetches{}}, at, q)
        case F.FetchFailed{}:
          MV.mv.q_land(i, k, p, cs, n, F.Cl{j, p, F.Fetches{}}, at, q)
        case F.Stored{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
    case F.Stores{}:
      match fd:
        case F.LoadFresh{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.LoadExpired{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.LoadFailed{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.CheckFresh{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.CheckExpired{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.FetchOk{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.FetchFailed{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.Stored{}:
          MV.mv.q_land(i, k, p, cs, n, F.Cl{j, p, F.Stores{}}, at, q)
    case F.Waits{}:
      match fd:
        case F.LoadFresh{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.LoadExpired{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.LoadFailed{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.CheckFresh{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.CheckExpired{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.FetchOk{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.FetchFailed{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
        case F.Stored{}:
          MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)

def pq.found(m: Maybe<&2, F.Cl>, +fd: F.Fd, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == m : Maybe<&2, F.Cl>}, +i: Nat, q: ({SS.af_live(i, cs) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})) -> MV.mv.QGoal(i, S.af_found_at(m, fd, k, cs, n)):
  match m:
    case None{}:
      MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
    case Some{x}:
      match x:
        case F.Cl{+j, +p, +a}:
          pq.fit(a, fd, k, j, p, cs, n, at, i, q)

def pq.unwind(m: Maybe<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, +at: {S.af_find(k, cs) == m : Maybe<&2, F.Cl>}, +i: Nat, q: ({SS.af_live(i, cs) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})) -> MV.mv.QGoal(i, S.af_unwind_at(m, k, cs, n)):
  match m:
    case None{}:
      MV.mv.q_keep(i, cs, n, F.Off{}, {==}, q)
    case Some{x}:
      match x:
        case F.Cl{+j, +p, a}:
          match a:
            case F.Loads{}:
              MV.mv.q_cut0(i, k, cs, n, q)
            case F.Checks{}:
              MV.mv.q_unwind(i, k, p, cs, n, q)
            case F.Fetches{}:
              MV.mv.q_unwind(i, k, p, cs, n, q)
            case F.Stores{}:
              MV.mv.q_unwind(i, k, p, cs, n, q)
            case F.Waits{}:
              MV.mv.q_cut0(i, k, cs, n, q)

def pq.step(d: F.Desk, e: F.DEv, +i: Nat, q: ({SS.af_live(i, S.af_cs(d)) == False{} : Bool} & {Nat.is_lt(i, MV.mv.m_of(d)) == True{} : Bool})) -> MV.mv.QGoal(i, S.af_desk(d, e)):
  match d:
    case F.Desk{+cs, +n}:
      match e:
        case F.Comes{+p}:
          MV.mv.q_arrive(i, n, p, cs, q)
        case F.Found{+k, +fd}:
          pq.found(S.af_find(k, cs), fd, k, cs, n, {==}, i, q)
        case F.Unwinds{+k}:
          pq.unwind(S.af_find(k, cs), k, cs, n, {==}, i, q)
        case F.Joiners{+p}:
          MV.mv.q_keep(i, cs, n, F.Joined{S.af_joiners(S.af_inflight(p, cs), p, cs)}, {==}, q)


