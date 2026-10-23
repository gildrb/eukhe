# eukhe: the proof of LAW dir_go_unjudged

import Base
import ../../bend/director.bend as Dr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.dir_go_unjudged(l, rest, room, stay):
  LA.pd.on_top(l, Dr.decide.go(rest, Nil{}, room, stay))
