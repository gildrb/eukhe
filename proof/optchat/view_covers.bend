# eukhe: the proof of LAW view_covers

import Base
import ../../laws/optchat.bend as Optchat
import ./base/step.bend as LA

# ---- laws ----

# (a) The view

def Optchat.view_covers(cfg, evs):
  LA.view_covers(cfg, evs)
