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

def HeadlessExit.headless_exit_autonomous_last(r, p, ba, ok, clean):
  -f = {Hx.Facts{False{}, Hx.Quiet{}, r, p, False{}, True{}, ba} : Hx.Facts}
  %Equal.sym(Hx.Cause, Hx.cause(f), Sp.exit_cause(f), LAHeadlessExit.hx.cause_eq(Hx.Facts{False{}, Hx.Quiet{}, r, p, False{}, True{}, ba})) : {_ == Hx.CAutonomousFailed{} : Hx.Cause}
  %Equal.sym(Maybe<&2, Hx.Cause>, Sp.run_cause(r), None{}, ok) : {Sp.first([None{}, None{}, Sp.counts(_, ba), Sp.counts(Sp.primary_cause(p), ba), Sp.when(False{}, Hx.CCompactionFailed{}), Sp.when(True{}, Hx.CAutonomousFailed{})], Sp.unfailed(ba)) == Hx.CAutonomousFailed{} : Hx.Cause}
  %Equal.sym(Maybe<&2, Hx.Cause>, Sp.primary_cause(p), None{}, clean) : {Sp.first([None{}, None{}, None{}, Sp.counts(_, ba), Sp.when(False{}, Hx.CCompactionFailed{}), Sp.when(True{}, Hx.CAutonomousFailed{})], Sp.unfailed(ba)) == Hx.CAutonomousFailed{} : Hx.Cause}
  {==}
