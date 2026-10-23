# eukhe: the proof of LAW admission_live_run

import Base
import ../../bend/admission.bend as Ad
import ../../LAWS.bend as Laws
import ./base.bend as LA

def al.run(os: List<&2, Ad.Op>, +t: Ad.St) -> {Ad.Live.run(os, Laws.adl_live(t)) == Laws.adl_live(Ad.run(os, t)) : Ad.Live}:
  match os:
    case Nil{}:
      {==}
    case +o <> r:
      %Equal.sym(Ad.Live, Ad.Live.step(Laws.adl_live(t), o), Laws.adl_live(Ad.step(t, o)), LA.al.step(t, o)) : {Ad.Live.run(r, _) == Laws.adl_live(Ad.run(r, Ad.step(t, o))) : Ad.Live}
      al.run(r, Ad.step(t, o))

def Laws.admission_live_run(l, q, os):
  al.run(os, Ad.St.new(l, q))
