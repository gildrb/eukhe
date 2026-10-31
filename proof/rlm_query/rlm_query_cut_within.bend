# eukhe: the proof of LAW rlm_query_cut_within
#
# PROOF: the code's cut is the reference cut (qc.code), whose cut keeps at most the room: a char is kept only within the room, the rest within the room it leaves (qc.within).

import Base
import ../../bend/rlm_query.bend as Rq
import ../../spec/rlm/query.bend as QSpec
import ../../laws/rlm_query.bend as RlmQuery
import ./base/cut.bend as LC


def RlmQuery.rlm_query_cut_within(m, t, k, e):
  %e : LC.qc.W(_, m)
  %Equal.sym(Rq.Trim, Rq.cut(m, t), LC.qc.R(t, m), LC.qc.code(t, m)) : LC.qc.W(_, m)
  LC.qc.within(t, m)
