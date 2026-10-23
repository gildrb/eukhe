# eukhe: the proof of LAW settle_falls

import Base
import ../../laws/compactor.bend as Compactor
import ./base.bend as LA

def Compactor.settle_falls(ps, k, o, due, lands):
  LA.pc.settle_falls(ps, k, o, due, lands)
