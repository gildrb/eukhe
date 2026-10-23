# eukhe: lemmas the proofs of area admission share: admission/get

import Base
import ../../../../bend/admission.bend as Ad
import ../logic.bend as LALogic

def ad.isg_at(-ts: List<&2, Ad.Tk>, -k: Nat, -mb: Maybe<&2, Ad.Tk>, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, f: {LALogic.ad.isg(mb) == True{} : Bool}) -> {LALogic.ad.isg(Ad.get(ts, k)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Ad.Tk>, Ad.get(ts, k), mb, ej) : {LALogic.ad.isg(_) == True{} : Bool}
  f
