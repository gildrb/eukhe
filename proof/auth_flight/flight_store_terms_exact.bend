# eukhe: the proof of LAW flight_store_terms_exact
# Both accessors compute on a built store.

import Base
import ../../laws/auth_flight.bend as AuthFlight

def AuthFlight.flight_store_terms_exact(c, f):
  ({==}, {==})
