# eukhe: the proof of LAW echo_stepper_refused
#
# PROOF: the premise makes the open refused (state Refused, its error
# reply); a refused state answers the refused error to every event and
# stays refused: er.step, by induction on the events.

import Base
import ../../bend/ffi_echo.bend as FEc
import ../../laws/echo.bend as Echo
import ./base.bend as LA

# from the refused state and the reply x, the reply to the i-th event is the
# refused error; none past the events
def er.step(evs: List<&2, String>, x: String, i: Nat) -> {List.get(&2, String, Echo.ec_feed(evs, (FEc.Refused{}, x)), 1n+i) == Echo.ec_if_event(List.get(&2, String, evs, i), "E echo: the open was refused") : Maybe<&2, String>}:
  match evs:
    case Nil{}:
      {==}
    case e <> +t:
      match i:
        case 0n:
          LA.eb.head(t, FEc.Refused{}, "E echo: the open was refused")
        case 1n+j:
          er.step(t, "E echo: the open was refused", j)

def Echo.echo_stepper_refused(input, no, evs, i):
  %Equal.sym(Maybe<&2, U32>, U32.read(input), None{}, no) : ({List.get(&2, String, Echo.ec_feed(evs, FEc.open.start(_)), 0n) == Some{"E echo: open wants a decimal U32"} : Maybe<&2, String>} & {List.get(&2, String, Echo.ec_feed(evs, FEc.open.start(_)), 1n+i) == Echo.ec_if_event(List.get(&2, String, evs, i), "E echo: the open was refused") : Maybe<&2, String>})
  (LA.eb.head(evs, FEc.Refused{}, "E echo: open wants a decimal U32"), er.step(evs, "E echo: open wants a decimal U32", i))
