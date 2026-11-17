# eukhe: the proof of LAW strength_record_missing_refused
#
# PROOF: with no check at the index, the model's put finds none (LS.sg.put_none:
# induction on the index and the checks), so the record is refused with
# the checks kept.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_record_missing_refused(i, m, gs, none):
  %LS.sg.put_none(i, m, gs, none) : {St.record.put(_, gs) == (False{}, gs) : Bool & List<&2, St.Gauge>}
  {==}
