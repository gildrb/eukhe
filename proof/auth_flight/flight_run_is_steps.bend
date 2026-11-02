# eukhe: the proof of LAW flight_run_is_steps
# Induction on the events: each step is am_step (flight_step_exact); a
# run is the fold from the new world.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight.bend as AuthFlight
import ./flight_step_exact.bend as PFlightStepExact

def pfr.go(evs: List<&2, F.Ev>, +s: F.St) -> {F.go(evs, s) == AuthFlight.am_go(evs, s) : F.St}:
  match evs:
    case Nil{}:
      {==}
    case +e <> rest:
      %AuthFlight.flight_step_exact(s, e) : {F.go(rest, F.step(s, e)) == AuthFlight.am_go(rest, _) : F.St}
      pfr.go(rest, F.step(s, e))

def AuthFlight.flight_run_is_steps(evs, s):
  (pfr.go(evs, s), pfr.go(evs, F.St.new()))
