# eukhe: the proof of LAW admission_background_yields

import Base
import ../../bend/admission.bend as Ad
import ../../LAWS.bend as Laws
import ./base.bend as LA

def ad.okS_calm(s: Ad.St, h: {LA.ad.okS(s) == True{} : Bool}) -> {Ad.calm(Ad.St.ts(s)) == True{} : Bool}:
  match s:
    case Ad.St{+l, q, +ts}:
      LA.ad.calm_of(l, ts, h)

def background_yields(+l: Ad.Lim, +q: Nat, +os: List<&2, Ad.Op>) -> {Ad.calm(Ad.St.ts(Ad.run(os, Ad.St.new(l, q)))) == True{} : Bool}:
  ad.okS_calm(Ad.run(os, Ad.St.new(l, q)), LA.ad.run_ok(os, Ad.St.new(l, q), LA.ad.new_ok(l, q)))

def Laws.admission_background_yields(l, q, os):
  background_yields(l, q, os)
