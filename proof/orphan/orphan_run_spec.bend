# eukhe: the proof of LAW orphan_run_spec

import Base
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan
import ./base.bend as LA

def Orphan.orphan_run_spec(window, evs):
  LA.ps.ow_go(window, evs, Or.Live{Or.W{False{}, 0n, False{}, 0n}})
