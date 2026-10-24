# eukhe: the proof of LAW meet_exact

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def Staging.meet_exact(es):
  LA.rr.meet_go(es, es)
