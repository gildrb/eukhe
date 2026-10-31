# eukhe: the proof of LAW rlm_query_cut_append
#
# PROOF: the code's cut is the reference cut (qc.code); by induction on a, the reference cuts a ++ b as a, then b in the room a leaves after a's bytes (qc.app), which is the law's continuation (qc.then_eq).

import Base
import ../../bend/rlm_query.bend as Rq
import ../../spec/rlm/query.bend as QSpec
import ../../laws/rlm_query.bend as RlmQuery
import ./base/cut.bend as LC


def RlmQuery.rlm_query_cut_append(m, a, b):
  Equal.trans(Rq.Trim, Rq.cut(m, String.append(a, b)), LC.qc.R(String.append(a, b), m), RlmQuery.rq_cut_then(Rq.cut(m, a), m, a, b), LC.qc.code(String.append(a, b), m),
    Equal.trans(Rq.Trim, LC.qc.R(String.append(a, b), m), LC.qc.then(LC.qc.R(a, m), m, a, b), RlmQuery.rq_cut_then(Rq.cut(m, a), m, a, b), LC.qc.app(a, m, b),
      Equal.trans(Rq.Trim, LC.qc.then(LC.qc.R(a, m), m, a, b), LC.qc.then(Rq.cut(m, a), m, a, b), RlmQuery.rq_cut_then(Rq.cut(m, a), m, a, b),
        Equal.cong(Rq.Trim, Rq.Trim, z => LC.qc.then(z, m, a, b), LC.qc.R(a, m), Rq.cut(m, a), Equal.sym(Rq.Trim, Rq.cut(m, a), LC.qc.R(a, m), LC.qc.code(a, m))),
        Equal.sym(Rq.Trim, RlmQuery.rq_cut_then(Rq.cut(m, a), m, a, b), LC.qc.then(Rq.cut(m, a), m, a, b), LC.qc.then_eq(Rq.cut(m, a), m, a, b)))))
