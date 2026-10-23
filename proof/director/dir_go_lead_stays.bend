# eukhe: the proof of LAW dir_go_lead_stays

import Base
import ../../bend/director.bend as Dr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.dir_go_lead_stays(l, rest, vs, room):
  LA.pd.on_top(l, Dr.decide.go(rest, vs, room, True{}))
