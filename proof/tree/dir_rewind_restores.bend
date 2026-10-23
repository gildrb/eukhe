# eukhe: the proof of LAW dir_rewind_restores

import Base
import ../../bend/tree.bend as Tr
import ../../bend/director.bend as Dr
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def pd.dir_rewind_restores(+a: List<&2, Tr.Ent>, +s: List<&2, Dr.Layer>, good: {Tr.sound(a) == True{} : Bool}) -> {Dr.decode(Tr.apply(a, Tr.Rewind{Tr.diff(a, Dr.encode(s))})) == s : List<&2, Dr.Layer>}:
  %Equal.sym(List<&2, Tr.Ent>, Tr.apply(a, Tr.Rewind{Tr.diff(a, Dr.encode(s))}), Dr.encode(s), LA.rewind_reaches(a, Dr.encode(s), good, LA.pd.dir_encode_sound(s))) : {Dr.decode(_) == s : List<&2, Dr.Layer>}
  L.pd.dir_resume_restores(s)

def Laws.dir_rewind_restores(a, s, L.good):
  pd.dir_rewind_restores(a, s, L.good)
