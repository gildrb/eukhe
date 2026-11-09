# eukhe: lemmas the proofs of area echo share

import Base
import ../../bend/ffi_echo.bend as FEc
import ../../laws/echo.bend as Echo

# a run of steps from the reply x answers x first
def eb.head(evs: List<&2, String>, st: FEc.St, x: String) -> {List.get(&2, String, Echo.ec_feed(evs, (st, x)), 0n) == Some{x} : Maybe<&2, String>}:
  match evs:
    case Nil{}:
      {==}
    case e <> t:
      {==}
