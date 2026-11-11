# eukhe: the proof of LAW flight_found_moves
# The desk finds caller k after pre (FR.fr.find); split on its place and
# the found: where the found answers the place's act and lands nothing,
# the desk tells caller k one act and moves it to that act's place
# (FR.fr.set), or lets it leave on a done (FR.fr.cut); an expired load
# joins (wait) or leads (check) as p has a flight in flight or not. Every
# other pair contradicts a premise.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/entry.bend as S
import ../../laws/auth_flight/desk.bend as AuthFlightDesk
import ../../laws/auth_flight/safety.bend as SS
import ./base/entry.bend as LAE
import ./base/frame.bend as FR

# the claim on a decision r of caller k at a: one act, and the desk it
# leaves
def pfm.H(a: F.At, r: F.DRes, +k: Nat, +p: String, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat) -> Type:
  &act: F.Act -> {r == F.DRes{F.Desk{AuthFlightDesk.af_moved(k, p, act, pre, post), n}, F.Acts{[F.To{k, act}]}} : F.DRes}

def pfm.G(+a: F.At, +fd: F.Fd, +k: Nat, +p: String, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat) -> Type:
  pfm.H(a, F.found.fit(Nat.is_eq(F.At.tag(a), F.Fd.tag(fd)), fd, k, p, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n), k, p, pre, post, n)

# a done: caller k leaves
def pfm.done(+k: Nat, +p: String, +a: F.At, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat, nl: {SS.af_live(k, pre) == False{} : Bool}) -> pfm.H(a, F.DRes{F.Desk{F.cut(k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)), n}, F.Acts{[F.To{k, F.DoDone{}}]}}, k, p, pre, post, n):
  (F.DoDone{}, Equal.cong(List<&2, F.Cl>, F.DRes, r => F.DRes{F.Desk{r, n}, F.Acts{[F.To{k, F.DoDone{}}]}}, F.cut(k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)), List.append(&2, F.Cl, pre, post), FR.fr.cut(k, pre, p, a, post, nl)))

# a move: caller k stands at a2, told act
def pfm.set(+k: Nat, +p: String, +a: F.At, +a2: F.At, +act: F.Act, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat, nl: {SS.af_live(k, pre) == False{} : Bool}, e: {AuthFlightDesk.af_moved(k, p, act, pre, post) == List.append(&2, F.Cl, pre, F.Cl{k, p, a2} <> post) : List<&2, F.Cl>}) -> pfm.H(a, F.DRes{F.Desk{F.set(k, a2, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)), n}, F.Acts{[F.To{k, act}]}}, k, p, pre, post, n):
  (act, Equal.cong(List<&2, F.Cl>, F.DRes, r => F.DRes{F.Desk{r, n}, F.Acts{[F.To{k, act}]}}, F.set(k, a2, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)), AuthFlightDesk.af_moved(k, p, act, pre, post), Equal.trans(List<&2, F.Cl>, F.set(k, a2, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)), List.append(&2, F.Cl, pre, F.Cl{k, p, a2} <> post), AuthFlightDesk.af_moved(k, p, act, pre, post), FR.fr.set(k, a2, pre, p, a, post, nl), Equal.sym(List<&2, F.Cl>, AuthFlightDesk.af_moved(k, p, act, pre, post), List.append(&2, F.Cl, pre, F.Cl{k, p, a2} <> post), e))))

# an expired load: it joins p's flight in flight, or leads a new one
def pfm.board(fl: Bool, +k: Nat, +p: String, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat, nl: {SS.af_live(k, pre) == False{} : Bool}) -> pfm.H(F.Loads{}, F.board(fl, k, List.append(&2, F.Cl, pre, F.Cl{k, p, F.Loads{}} <> post), n), k, p, pre, post, n):
  match fl:
    case True{}:
      pfm.set(k, p, F.Loads{}, F.Waits{}, F.DoWait{}, pre, post, n, nl, {==})
    case False{}:
      pfm.set(k, p, F.Loads{}, F.Checks{}, F.DoCheck{}, pre, post, n, nl, {==})

def pfm.fit(a: F.At, fd: F.Fd, +k: Nat, +p: String, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat, nl: {SS.af_live(k, pre) == False{} : Bool}, answers: {AuthFlightDesk.af_answers(AuthFlightDesk.af_place_act(a), fd) == True{} : Bool}, stays: {S.af_lands(a, fd) == False{} : Bool}) -> pfm.G(a, fd, k, p, pre, post, n):
  match a:
    case F.Loads{}:
      match fd:
        case F.LoadFresh{}:
          pfm.done(k, p, F.Loads{}, pre, post, n, nl)
        case F.LoadExpired{}:
          pfm.board(F.inflight(p, List.append(&2, F.Cl, pre, F.Cl{k, p, F.Loads{}} <> post)), k, p, pre, post, n, nl)
        case F.LoadFailed{}:
          pfm.done(k, p, F.Loads{}, pre, post, n, nl)
        case F.CheckFresh{}:
          LAE.ae.ft(pfm.G(F.Loads{}, F.CheckFresh{}, k, p, pre, post, n), answers)
        case F.CheckExpired{}:
          LAE.ae.ft(pfm.G(F.Loads{}, F.CheckExpired{}, k, p, pre, post, n), answers)
        case F.FetchOk{}:
          LAE.ae.ft(pfm.G(F.Loads{}, F.FetchOk{}, k, p, pre, post, n), answers)
        case F.FetchFailed{}:
          LAE.ae.ft(pfm.G(F.Loads{}, F.FetchFailed{}, k, p, pre, post, n), answers)
        case F.Stored{}:
          LAE.ae.ft(pfm.G(F.Loads{}, F.Stored{}, k, p, pre, post, n), answers)
    case F.Checks{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(pfm.G(F.Checks{}, F.LoadFresh{}, k, p, pre, post, n), answers)
        case F.LoadExpired{}:
          LAE.ae.ft(pfm.G(F.Checks{}, F.LoadExpired{}, k, p, pre, post, n), answers)
        case F.LoadFailed{}:
          LAE.ae.ft(pfm.G(F.Checks{}, F.LoadFailed{}, k, p, pre, post, n), answers)
        case F.CheckFresh{}:
          LAE.ae.tf(pfm.G(F.Checks{}, F.CheckFresh{}, k, p, pre, post, n), stays)
        case F.CheckExpired{}:
          pfm.set(k, p, F.Checks{}, F.Fetches{}, F.DoFetch{}, pre, post, n, nl, {==})
        case F.FetchOk{}:
          LAE.ae.ft(pfm.G(F.Checks{}, F.FetchOk{}, k, p, pre, post, n), answers)
        case F.FetchFailed{}:
          LAE.ae.ft(pfm.G(F.Checks{}, F.FetchFailed{}, k, p, pre, post, n), answers)
        case F.Stored{}:
          LAE.ae.ft(pfm.G(F.Checks{}, F.Stored{}, k, p, pre, post, n), answers)
    case F.Fetches{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(pfm.G(F.Fetches{}, F.LoadFresh{}, k, p, pre, post, n), answers)
        case F.LoadExpired{}:
          LAE.ae.ft(pfm.G(F.Fetches{}, F.LoadExpired{}, k, p, pre, post, n), answers)
        case F.LoadFailed{}:
          LAE.ae.ft(pfm.G(F.Fetches{}, F.LoadFailed{}, k, p, pre, post, n), answers)
        case F.CheckFresh{}:
          LAE.ae.ft(pfm.G(F.Fetches{}, F.CheckFresh{}, k, p, pre, post, n), answers)
        case F.CheckExpired{}:
          LAE.ae.ft(pfm.G(F.Fetches{}, F.CheckExpired{}, k, p, pre, post, n), answers)
        case F.FetchOk{}:
          pfm.set(k, p, F.Fetches{}, F.Stores{}, F.DoStore{}, pre, post, n, nl, {==})
        case F.FetchFailed{}:
          LAE.ae.tf(pfm.G(F.Fetches{}, F.FetchFailed{}, k, p, pre, post, n), stays)
        case F.Stored{}:
          LAE.ae.ft(pfm.G(F.Fetches{}, F.Stored{}, k, p, pre, post, n), answers)
    case F.Stores{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(pfm.G(F.Stores{}, F.LoadFresh{}, k, p, pre, post, n), answers)
        case F.LoadExpired{}:
          LAE.ae.ft(pfm.G(F.Stores{}, F.LoadExpired{}, k, p, pre, post, n), answers)
        case F.LoadFailed{}:
          LAE.ae.ft(pfm.G(F.Stores{}, F.LoadFailed{}, k, p, pre, post, n), answers)
        case F.CheckFresh{}:
          LAE.ae.ft(pfm.G(F.Stores{}, F.CheckFresh{}, k, p, pre, post, n), answers)
        case F.CheckExpired{}:
          LAE.ae.ft(pfm.G(F.Stores{}, F.CheckExpired{}, k, p, pre, post, n), answers)
        case F.FetchOk{}:
          LAE.ae.ft(pfm.G(F.Stores{}, F.FetchOk{}, k, p, pre, post, n), answers)
        case F.FetchFailed{}:
          LAE.ae.ft(pfm.G(F.Stores{}, F.FetchFailed{}, k, p, pre, post, n), answers)
        case F.Stored{}:
          LAE.ae.tf(pfm.G(F.Stores{}, F.Stored{}, k, p, pre, post, n), stays)
    case F.Waits{}:
      match fd:
        case F.LoadFresh{}:
          LAE.ae.ft(pfm.G(F.Waits{}, F.LoadFresh{}, k, p, pre, post, n), answers)
        case F.LoadExpired{}:
          LAE.ae.ft(pfm.G(F.Waits{}, F.LoadExpired{}, k, p, pre, post, n), answers)
        case F.LoadFailed{}:
          LAE.ae.ft(pfm.G(F.Waits{}, F.LoadFailed{}, k, p, pre, post, n), answers)
        case F.CheckFresh{}:
          LAE.ae.ft(pfm.G(F.Waits{}, F.CheckFresh{}, k, p, pre, post, n), answers)
        case F.CheckExpired{}:
          LAE.ae.ft(pfm.G(F.Waits{}, F.CheckExpired{}, k, p, pre, post, n), answers)
        case F.FetchOk{}:
          LAE.ae.ft(pfm.G(F.Waits{}, F.FetchOk{}, k, p, pre, post, n), answers)
        case F.FetchFailed{}:
          LAE.ae.ft(pfm.G(F.Waits{}, F.FetchFailed{}, k, p, pre, post, n), answers)
        case F.Stored{}:
          LAE.ae.ft(pfm.G(F.Waits{}, F.Stored{}, k, p, pre, post, n), answers)

def AuthFlightDesk.flight_found_moves(pre, post, n, k, p, a, first, fd, answers, stays):
  +nl = first
  %Equal.sym(Maybe<&2, F.Cl>, F.find(k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)), Some{F.Cl{k, p, a}}, FR.fr.find(k, pre, p, a, post, nl)) : pfm.H(a, F.found(_, fd, k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n), k, p, pre, post, n)
  pfm.fit(a, fd, k, p, pre, post, n, nl, answers, stays)
