# eukhe: the proof of LAW flight_next_load_is_model
# Both sides compute on a fresh and on an expired store.

import Base
import ../../laws/auth_flight.bend as AuthFlight

def AuthFlight.flight_next_load_is_model(c, w):
  ({==}, {==})
