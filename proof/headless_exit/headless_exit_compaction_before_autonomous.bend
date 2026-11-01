# eukhe: the proof of LAW headless_exit_compaction_before_autonomous
#
# PROOF: the cause is the spec's (hx.cause_eq); with no earlier failure (ok, clean), the spec's first failure is the compaction's.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless.bend as Sp
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_compaction_before_autonomous(r, p, a, ok, clean):
  -f = {Hx.Facts{False{}, False{}, r, p, True{}, a} : Hx.Facts}
  %Equal.sym(Hx.Cause, Hx.cause(f), Sp.cause_spec(f), LAHeadlessExit.hx.cause_eq(Hx.Facts{False{}, False{}, r, p, True{}, a})) : {_ == Hx.CCompactionFailed{} : Hx.Cause}
  %Equal.sym(Maybe<&2, Hx.Cause>, Sp.run_cause(r), None{}, ok) : {Sp.first([None{}, None{}, _, Sp.primary_cause(p), Sp.when(True{}, Hx.CCompactionFailed{}), Sp.when(a, Hx.CAutonomousFailed{})]) == Hx.CCompactionFailed{} : Hx.Cause}
  %Equal.sym(Maybe<&2, Hx.Cause>, Sp.primary_cause(p), None{}, clean) : {Sp.first([None{}, None{}, None{}, _, Sp.when(True{}, Hx.CCompactionFailed{}), Sp.when(a, Hx.CAutonomousFailed{})]) == Hx.CCompactionFailed{} : Hx.Cause}
  {==}
