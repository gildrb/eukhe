# eukhe: the proof of LAW dir_go_unjudged

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ./base.bend as LA

def Director.dir_go_unjudged(l, rest, room, stay):
  LA.pd.on_top(l, Dr.decide.go(rest, Nil{}, room, stay))
