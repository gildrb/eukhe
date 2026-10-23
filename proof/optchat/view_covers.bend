# eukhe: the proof of LAW view_covers

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

# ---- laws ----

# (a) The view

def Laws.view_covers(cfg, evs):
  LA.view_covers(cfg, evs)
