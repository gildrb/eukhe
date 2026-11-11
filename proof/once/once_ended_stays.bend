# eukhe: the proof of LAW once_ended_stays
#
# PROOF: the fold of j then rest is the fold of rest from the life j
# tells (LA.ob.go_append); that life is an end, which absorbs every
# record (LA.ob.stays).

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ./base.bend as LA

def Once.once_ended_stays(j, rest, ended):
  Equal.trans(O.Life, O.life(List.append(&2, O.Rec, j, rest)), O.life.go(rest, O.life(j)), O.life(j), LA.ob.go_append(j, rest, O.Absent{}), LA.ob.stays(O.life(j), rest, ended))
