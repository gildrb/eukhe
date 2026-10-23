# eukhe: the proof of LAW publish_moves

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging

def pg.publish_free(+s: Nat, +t: Nat, +es: List<&2, Sg.Entry>, free: {Sg.has(t, es) == False{} : Bool}) -> {Sg.Pub.ok(Sg.publish(s, t, es)) == True{} : Bool}:
  %Equal.sym(Bool, Sg.has(t, es), False{}, free) : {Sg.Pub.ok(Sg.publish.go(s, t, _, es)) == True{} : Bool}
  {==}

def Staging.publish_moves(s, t, es, free):
  pg.publish_free(s, t, es, free)
