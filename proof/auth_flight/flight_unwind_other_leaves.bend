# eukhe: the proof of LAW flight_unwind_other_leaves
# The desk finds caller k after pre (FR.fr.find); it does not lead (the
# premise, through LAE.ae.leads), so it just leaves (FR.fr.cut) and the
# reply names nobody.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/entry.bend as S
import ../../laws/auth_flight/desk.bend as AuthFlightDesk
import ./base/entry.bend as LAE
import ./base/frame.bend as FR

def AuthFlightDesk.flight_unwind_other_leaves(pre, post, n, k, p, a, first, leads):
  +nl = first
  %Equal.sym(Maybe<&2, F.Cl>, F.find(k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)), Some{F.Cl{k, p, a}}, FR.fr.find(k, pre, p, a, post, nl)) : {F.unwind(_, k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n) == F.DRes{F.Desk{List.append(&2, F.Cl, pre, post), n}, F.Acts{Nil{}}} : F.DRes}
  %Equal.sym(Bool, F.leads(a), False{}, Equal.trans(Bool, F.leads(a), S.af_leads(a), False{}, LAE.ae.leads(a), leads)) : {F.unwind.at(_, k, p, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post), n) == F.DRes{F.Desk{List.append(&2, F.Cl, pre, post), n}, F.Acts{Nil{}}} : F.DRes}
  Equal.cong(List<&2, F.Cl>, F.DRes, r => F.DRes{F.Desk{r, n}, F.Acts{Nil{}}}, F.cut(k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)), List.append(&2, F.Cl, pre, post), FR.fr.cut(k, pre, p, a, post, nl))
