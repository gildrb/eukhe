# eukhe: the proof of LAW headless_exit_compaction_before_autonomous
#
# PROOF: the cause is the first failure of the list of E1 (hx.cause_eq); with no earlier failure (ok, clean), that first failure is the compaction's.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless.bend as Sp
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_compaction_before_autonomous(r, p, a, ba, ok, clean):
  -f = {Hx.Facts{False{}, Hx.Quiet{}, r, p, True{}, a, ba} : Hx.Facts}
  %Equal.sym(Hx.Cause, Hx.cause(f), Sp.exit_cause(f), LAHeadlessExit.hx.cause_eq(Hx.Facts{False{}, Hx.Quiet{}, r, p, True{}, a, ba})) : {_ == Hx.CCompactionFailed{} : Hx.Cause}
  %Equal.sym(Maybe<&2, Hx.Cause>, Sp.run_cause(r), None{}, ok) : {Sp.first([None{}, None{}, Sp.counts(_, ba), Sp.counts(Sp.primary_cause(p), ba), Sp.when(True{}, Hx.CCompactionFailed{}), Sp.when(a, Hx.CAutonomousFailed{})], Sp.unfailed(ba)) == Hx.CCompactionFailed{} : Hx.Cause}
  %Equal.sym(Maybe<&2, Hx.Cause>, Sp.primary_cause(p), None{}, clean) : {Sp.first([None{}, None{}, None{}, Sp.counts(_, ba), Sp.when(True{}, Hx.CCompactionFailed{}), Sp.when(a, Hx.CAutonomousFailed{})], Sp.unfailed(ba)) == Hx.CCompactionFailed{} : Hx.Cause}
  {==}
