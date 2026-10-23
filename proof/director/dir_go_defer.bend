# eukhe: the proof of LAW dir_go_defer

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ./base.bend as LA

def Director.dir_go_defer(l, rest, vs, room, stay):
  LA.pd.on_top(l, Dr.decide.go(rest, vs, room, stay))
