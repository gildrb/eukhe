# eukhe: the proof of LAW headless_exit_autonomous_last
#
# PROOF: the cause is the first failure of the list of E1 (hx.cause_eq);
# with no earlier failure (ok, clean, no failed compaction), that first
# failure is the autonomous turn's.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless.bend as Sp
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_autonomous_last(r, p, ok, clean):
  -f = {Hx.Facts{False{}, False{}, r, p, False{}, True{}} : Hx.Facts}
  %Equal.sym(Hx.Cause, Hx.cause(f), LAHeadlessExit.hx.cause_spec(f), LAHeadlessExit.hx.cause_eq(Hx.Facts{False{}, False{}, r, p, False{}, True{}})) : {_ == Hx.CAutonomousFailed{} : Hx.Cause}
  %Equal.sym(Maybe<&2, Hx.Cause>, Sp.run_cause(r), None{}, ok) : {LAHeadlessExit.hx.first([None{}, None{}, _, Sp.primary_cause(p), Sp.when(False{}, Hx.CCompactionFailed{}), Sp.when(True{}, Hx.CAutonomousFailed{})]) == Hx.CAutonomousFailed{} : Hx.Cause}
  %Equal.sym(Maybe<&2, Hx.Cause>, Sp.primary_cause(p), None{}, clean) : {LAHeadlessExit.hx.first([None{}, None{}, None{}, _, Sp.when(False{}, Hx.CCompactionFailed{}), Sp.when(True{}, Hx.CAutonomousFailed{})]) == Hx.CAutonomousFailed{} : Hx.Cause}
  {==}
