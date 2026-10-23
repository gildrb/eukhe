# eukhe: lemmas the proofs of area admission share: admission/St

import Base
import ../../../../bend/admission.bend as Ad
import ../logic.bend as LALogic

def ad.new_ok(l: Ad.Lim, -q: Nat) -> {LALogic.ad.okS(Ad.St.new(l, q)) == True{} : Bool}:
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{p}:
      {==}
