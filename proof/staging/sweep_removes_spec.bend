# eukhe: the proof of LAW sweep_removes_spec

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def Staging.sweep_removes_spec(n):
  LA.pg.removes_spec(n)
