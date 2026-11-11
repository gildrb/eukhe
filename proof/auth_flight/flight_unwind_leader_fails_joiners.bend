# eukhe: the proof of LAW flight_unwind_leader_fails_joiners
# The desk finds caller k after pre (FR.fr.find); it leads (the premise,
# through LAE.ae.leads), so the desk lands its flight with the failure
# gone(p): caller k leaves (FR.fr.cut), the callers waiting on p's flight
# leave (FR.fr.unwait) and are told the failure in order (FR.fr.wake);
# F.gone and the laws' af_gone are the same text.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/entry.bend as S
import ../../laws/auth_flight/safety.bend as SS
import ../../laws/auth_flight/desk.bend as AuthFlightDesk
import ./base/entry.bend as LAE
import ./base/frame.bend as FR

# the desk and the reply the law states
def pul.R(+p: String, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat) -> F.DRes:
  F.DRes{F.Desk{AuthFlightDesk.af_others(p, List.append(&2, F.Cl, pre, post)), n}, F.Acts{AuthFlightDesk.af_tell(F.DoFail{S.af_gone(p)}, AuthFlightDesk.af_waiters(p, List.append(&2, F.Cl, pre, post)))}}

# a failed flight of p on the callers r: its joiners leave and fail
def pul.of(+p: String, +r: List<&2, F.Cl>, +n: Nat) -> {F.DRes{F.Desk{F.unwait(p, r), n}, F.Acts{F.wake(p, F.DoFail{F.gone(p)}, r)}} == F.DRes{F.Desk{AuthFlightDesk.af_others(p, r), n}, F.Acts{AuthFlightDesk.af_tell(F.DoFail{S.af_gone(p)}, AuthFlightDesk.af_waiters(p, r))}} : F.DRes}:
  %Equal.sym(List<&2, F.Cl>, F.unwait(p, r), AuthFlightDesk.af_others(p, r), FR.fr.unwait(p, r)) : {F.DRes{F.Desk{_, n}, F.Acts{F.wake(p, F.DoFail{F.gone(p)}, r)}} == F.DRes{F.Desk{AuthFlightDesk.af_others(p, r), n}, F.Acts{AuthFlightDesk.af_tell(F.DoFail{S.af_gone(p)}, AuthFlightDesk.af_waiters(p, r))}} : F.DRes}
  %Equal.sym(List<&2, F.To>, F.wake(p, F.DoFail{F.gone(p)}, r), AuthFlightDesk.af_tell(F.DoFail{F.gone(p)}, AuthFlightDesk.af_waiters(p, r)), FR.fr.wake(p, F.DoFail{F.gone(p)}, r)) : {F.DRes{F.Desk{AuthFlightDesk.af_others(p, r), n}, F.Acts{_}} == F.DRes{F.Desk{AuthFlightDesk.af_others(p, r), n}, F.Acts{AuthFlightDesk.af_tell(F.DoFail{S.af_gone(p)}, AuthFlightDesk.af_waiters(p, r))}} : F.DRes}
  {==}

# the leader k unwinds, between pre and post
def pul.lead(+k: Nat, +p: String, +a: F.At, +pre: List<&2, F.Cl>, +post: List<&2, F.Cl>, +n: Nat, nl: {SS.af_live(k, pre) == False{} : Bool}) -> {F.unwind.at(True{}, k, p, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n) == pul.R(p, pre, post, n) : F.DRes}:
  Equal.trans(F.DRes, F.unwind.at(True{}, k, p, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n), F.DRes{F.Desk{F.unwait(p, List.append(&2, F.Cl, pre, post)), n}, F.Acts{F.wake(p, F.DoFail{F.gone(p)}, List.append(&2, F.Cl, pre, post))}}, pul.R(p, pre, post, n), Equal.cong(List<&2, F.Cl>, F.DRes, r => F.DRes{F.Desk{F.unwait(p, r), n}, F.Acts{F.wake(p, F.DoFail{F.gone(p)}, r)}}, F.cut(k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)), List.append(&2, F.Cl, pre, post), FR.fr.cut(k, pre, p, a, post, nl)), pul.of(p, List.append(&2, F.Cl, pre, post), n))

def AuthFlightDesk.flight_unwind_leader_fails_joiners(pre, post, n, k, p, a, first, leads):
  +nl = first
  %Equal.sym(Maybe<&2, F.Cl>, F.find(k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)), Some{F.Cl{k, p, a}}, FR.fr.find(k, pre, p, a, post, nl)) : {F.unwind(_, k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n) == pul.R(p, pre, post, n) : F.DRes}
  %Equal.sym(Bool, F.leads(a), True{}, Equal.trans(Bool, F.leads(a), S.af_leads(a), True{}, LAE.ae.leads(a), leads)) : {F.unwind.at(_, k, p, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n) == pul.R(p, pre, post, n) : F.DRes}
  pul.lead(k, p, a, pre, post, n, nl)
