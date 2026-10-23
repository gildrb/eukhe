# eukhe: the proof of LAW dir_rewind_restores

import Base
import ../../bend/director.bend as Dr
import ../../bend/tree.bend as Tr
import ../../laws/tree.bend as Tree
import ../base/director.bend as LDirector
import ../base/retry.bend as LRetry
import ./base/director.bend as LADirector
import ./base/tree/sorted.bend as LATreeSorted

def pd.dir_rewind_restores(+a: List<&2, Tr.Ent>, +s: List<&2, Dr.Layer>, good: {Tr.sound(a) == True{} : Bool}) -> {Dr.decode(Tr.apply(a, Tr.Rewind{Tr.diff(a, Dr.encode(s))})) == s : List<&2, Dr.Layer>}:
  %Equal.sym(List<&2, Tr.Ent>, Tr.apply(a, Tr.Rewind{Tr.diff(a, Dr.encode(s))}), Dr.encode(s), LATreeSorted.rewind_reaches(a, Dr.encode(s), good, LADirector.pd.dir_encode_sound(s))) : {Dr.decode(_) == s : List<&2, Dr.Layer>}
  LDirector.pd.dir_resume_restores(s)

def Tree.dir_rewind_restores(a, s, LRetry.good):
  pd.dir_rewind_restores(a, s, LRetry.good)
