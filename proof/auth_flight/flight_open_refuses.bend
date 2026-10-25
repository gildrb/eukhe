# eukhe: the proof of LAW flight_open_refuses
# A non-empty open reads as not empty (the premise); the refused stepper's
# step computes.

import Base
import ../../bend/ffi_auth_flight.bend as FA
import ../../laws/auth_flight/entry.bend as AuthFlightEntry

def for.open(+s: String, ne: {String.is_empty(s) == False{} : Bool}) -> {FA.open(s) == (FA.Shut{}, SCon{'E', SCon{' ', "auth_flight: malformed open"}}) : FA.St & String}:
  %Equal.sym(Bool, String.is_empty(s), False{}, ne) : {FA.open.fin(_) == (FA.Shut{}, SCon{'E', SCon{' ', "auth_flight: malformed open"}}) : FA.St & String}
  {==}

def AuthFlightEntry.flight_open_refuses(s, ne, e):
  (for.open(s, ne), {==})
