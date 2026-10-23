# eukhe: the proof of LAW publish_never_overwrites

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging

# Publish
# -------

def pg.publish_taken(+s: Nat, +t: Nat, +es: List<&2, Sg.Entry>, taken: {Sg.has(t, es) == True{} : Bool}) -> {Sg.publish(s, t, es) == Sg.Pub{False{}, es} : Sg.Pub}:
  %Equal.sym(Bool, Sg.has(t, es), True{}, taken) : {Sg.publish.go(s, t, _, es) == Sg.Pub{False{}, es} : Sg.Pub}
  {==}

def Staging.publish_never_overwrites(s, t, es, taken):
  pg.publish_taken(s, t, es, taken)
