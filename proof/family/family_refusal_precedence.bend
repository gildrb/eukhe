# eukhe: the proof of LAW family_refusal_precedence
#
# PROOF: each step of the code is the spec's: the first bad why (fp.bad), then the reason, depth and cap steps (fp.why).

import Base
import ../../bend/family.bend as F
import ../../spec/rlm/family.bend as FamSpec
import ../../laws/family.bend as Family
import ./base.bend as LF


def Family.family_refusal_precedence(d, m, r, c, ws):
  %LF.fp.bad(ws, 0n) : {F.decide.why(F.bad(ws, 0n), d, m, r, c, List.length(&2, String, ws)) == FamSpec.verdict.of(_, d, m, r, c, List.length(&2, String, ws)) : F.Verdict}
  LF.fp.why(F.bad(ws, 0n), d, m, r, c, List.length(&2, String, ws))
