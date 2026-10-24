# eukhe: the proof of LAW flight_next_fetch_is_model
# On every world both sides compute.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight.bend as AuthFlight

def AuthFlight.flight_next_fetch_is_model(f, w):
  match w:
    case F.W{s, fl, ld, n}:
      ({==}, {==})
