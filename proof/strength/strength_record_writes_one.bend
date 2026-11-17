# eukhe: the proof of LAW strength_record_writes_one
#
# PROOF: with a check at the index, the model's put writes the checks with that
# one's mark replaced (LS.sg.put_some), so the record is admitted; read at
# every index j, those checks are the remarked one at the index and the
# old ones elsewhere (LS.sg.nth_set: induction on j, the index and the
# checks).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_record_writes_one(i, m, gs, j, has):
  %LS.sg.put_some(i, m, gs, has) : ({S.admitted(St.record.put(_, gs)) == True{} : Bool} & {S.nth(j, S.after(St.record.put(_, gs))) == S.remark_if(Nat.is_eq(j, i), m, S.nth(j, gs)) : Maybe<&2, St.Gauge>})
  ({==}, LS.sg.nth_set(j, i, m, gs))
