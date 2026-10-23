# eukhe: the proof of LAW plan_fits_lists_the_loose

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ./base.bend as LA

def Infer.plan_fits_lists_the_loose(cap, ts, need, ls, f):
  +L = Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict.of(cap, ts))
  %LA.w2.ids(L) : {ls == _ : List<&2, Nat>}
  LA.w2.of_fits(If.needs.go(L, need, If.needs.at(L, need)), L, ls, f)
