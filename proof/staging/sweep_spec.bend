# eukhe: the proof of LAW sweep_spec

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def Staging.sweep_spec(ns):
  LA.pg.sweep_spec(ns)
