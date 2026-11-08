# eukhe: the proof of LAW orphan_work_spec

import Base
import ../../laws/orphan.bend as Orphan
import ./base.bend as LA

def Orphan.orphan_work_spec(w):
  LA.ps.ow_work(w)
