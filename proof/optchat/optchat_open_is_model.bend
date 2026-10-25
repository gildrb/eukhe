# eukhe: the proof of LAW optchat_open_is_model
# The entry reads a spelled open back whole (LAO.oo.spelled) and runs the
# laws' open (LAO.oo.run): LAO.oo.opened.

import Base
import ../../laws/optchat.bend as Optchat
import ./base/open.bend as LAO

def Optchat.optchat_open_is_model(o, fits):
  LAO.oo.opened(o, fits)
