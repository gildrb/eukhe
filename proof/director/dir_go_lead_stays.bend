# eukhe: the proof of LAW dir_go_lead_stays

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ./base.bend as LA

def Director.dir_go_lead_stays(l, rest, vs, room):
  LA.pd.on_top(l, Dr.decide.go(rest, vs, room, True{}))
