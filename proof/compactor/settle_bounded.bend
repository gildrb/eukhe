# eukhe: the proof of LAW settle_bounded

import Base
import ../../laws/compactor.bend as Compactor
import ./base.bend as LA

def Compactor.settle_bounded(es, ps):
  LA.pc.settle_bounded(es, ps)
