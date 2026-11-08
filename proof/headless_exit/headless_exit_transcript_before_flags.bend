# eukhe: the proof of LAW headless_exit_transcript_before_flags
#
# PROOF: the cause is the spec's (hx.cause_eq); with no failed command, no give-up and no run failure (ok), the spec's first failure is the terminal entry's (failed).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless.bend as Sp
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_transcript_before_flags(r, p, c, a, x, ok, failed):
  -f = {Hx.Facts{False{}, False{}, r, p, c, a} : Hx.Facts}
  %Equal.sym(Hx.Cause, Hx.cause(f), Sp.cause_spec(f), LAHeadlessExit.hx.cause_eq(Hx.Facts{False{}, False{}, r, p, c, a})) : {_ == x : Hx.Cause}
  %Equal.sym(Maybe<&2, Hx.Cause>, Sp.run_cause(r), None{}, ok) : {Sp.first([None{}, None{}, _, Sp.primary_cause(p), Sp.when(c, Hx.CCompactionFailed{}), Sp.when(a, Hx.CAutonomousFailed{})]) == x : Hx.Cause}
  %Equal.sym(Maybe<&2, Hx.Cause>, Sp.primary_cause(p), Some{x}, failed) : {Sp.first([None{}, None{}, None{}, _, Sp.when(c, Hx.CCompactionFailed{}), Sp.when(a, Hx.CAutonomousFailed{})]) == x : Hx.Cause}
  {==}
