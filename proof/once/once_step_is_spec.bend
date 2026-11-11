# eukhe: the proof of LAW once_step_is_spec
#
# PROOF: the stepper opens on the life of no record; from the life any
# records tell, every reply is the spec's for the records read so far
# (LE.oe.model, by induction on the events).

import Base
import ../../laws/once.bend as Once
import ./base/entry.bend as LE

def Once.once_step_is_spec(es, fits):
  LE.oe.model(es, Nil{}, fits)
