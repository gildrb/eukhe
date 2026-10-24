# eukhe: the proof of LAW flight_next_store_is_model
# On every world, a fresh store and an expired one, both sides compute.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight.bend as AuthFlight

def AuthFlight.flight_next_store_is_model(f, c, w):
  match w:
    case F.W{s, fl, ld, n}:
      match s:
        case F.Sto{p, fresh}:
          match fresh:
            case True{}:
              {==}
            case False{}:
              {==}
