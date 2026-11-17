# eukhe: the proof of LAW strength_stale_mark_unshown
#
# PROOF: the mark's state is not the state now: the model's first stage answers
# unshown.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_stale_mark_unshown(pct, c, n, p, at, now, other):
  %Equal.sym(Bool, Nat.is_eq(at, now), False{}, other) : {St.strength.on(_, pct, c, n, p) == St.Unshown{} : St.Strength}
  {==}
