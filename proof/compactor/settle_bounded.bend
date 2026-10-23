# eukhe: the proof of LAW settle_bounded

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.settle_bounded(es, ps):
  LA.pc.settle_bounded(es, ps)
