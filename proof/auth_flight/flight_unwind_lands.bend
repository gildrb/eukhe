# eukhe: the proof of LAW flight_unwind_lands
# The entry steps the desk as the laws' desk (LAE.ae.answers); the
# caller is the one found; then split on whether it leads: both sides
# compute.

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_flight.bend as FA
import ../../laws/auth_flight/entry.bend as AuthFlightEntry
import ./base/entry.bend as LAE

def afl.lead(lead: Bool, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat) -> {AuthFlightEntry.af_step_of(AuthFlightEntry.af_unwind_lead(lead, k, p, cs, n)) == AuthFlightEntry.af_unwound(lead, k, p, cs, n) : FA.St & String}:
  match lead:
    case True{}:
      {==}
    case False{}:
      {==}

def AuthFlightEntry.flight_unwind_lands(cs, n, k, fits, j, p, a, at):
  %LAE.ae.answers_r(F.Desk{cs, n}, F.Unwinds{k}, fits) : {_ == AuthFlightEntry.af_unwound(AuthFlightEntry.af_leads(a), k, p, cs, n) : FA.St & String}
  %LAE.ae.at_r(k, cs, F.Cl{j, p, a}, at) : {AuthFlightEntry.af_step_of(AuthFlightEntry.af_unwind_at(_, k, cs, n)) == AuthFlightEntry.af_unwound(AuthFlightEntry.af_leads(a), k, p, cs, n) : FA.St & String}
  afl.lead(AuthFlightEntry.af_leads(a), k, p, cs, n)
