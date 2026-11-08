# eukhe: the proof of LAW rlm_query_cut_spec
#
# PROOF: the code's flat loop and the spec's longest prefix are both the reference cut, which keeps a char while its bytes fit the room left (qc.code, qc.spec).

import Base
import ../../bend/rlm_query.bend as Rq
import ../../spec/rlm/query.bend as QSpec
import ../../laws/rlm_query.bend as RlmQuery
import ./base/cut.bend as LC


def RlmQuery.rlm_query_cut_spec(m, t):
  Equal.trans(Rq.Trim, Rq.cut(m, t), LC.qc.R(t, m), QSpec.cut(m, t), LC.qc.code(t, m), Equal.sym(Rq.Trim, QSpec.cut(m, t), LC.qc.R(t, m), LC.qc.spec(t, m)))
