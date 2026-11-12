# eukhe: the proof of LAW admission_limits_grant
#
# PROOF: new limits run the model's grant loop under them, which is the
# two passes (pag.grant).

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/grant.bend as PG

def Admission.admission_limits_grant(l, q, ts, l2, q2):
  %PG.pag.grant(l2, ts) : {Ad.step(Ad.St{l, q, ts}, Ad.Limit{l2, q2}) == Ad.St{l2, q2, _} : Ad.St}
  {==}
