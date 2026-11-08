# eukhe: the proof of LAW sweep_sort_spec

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def Staging.sweep_sort_spec(k):
  LA.pg.swept_spec(k)
