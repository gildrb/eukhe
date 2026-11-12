# eukhe: the proof of LAW headless_exit_transcript_before_flags
#
# PROOF: the cause is the first failure of the list of E1 (hx.cause_eq); with no failed command, a quiet wait and no run failure (ok), that first failure is the terminal entry's (failed).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless.bend as Sp
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_transcript_before_flags(r, p, c, a, x, ok, failed):
  -f = {Hx.Facts{False{}, Hx.Quiet{}, r, p, c, a, False{}} : Hx.Facts}
  %Equal.sym(Hx.Cause, Hx.cause(f), LAHeadlessExit.hx.cause_spec(f), LAHeadlessExit.hx.cause_eq(Hx.Facts{False{}, Hx.Quiet{}, r, p, c, a, False{}})) : {_ == x : Hx.Cause}
  %Equal.sym(Maybe<&2, Hx.Cause>, Sp.run_cause(r), None{}, ok) : {LAHeadlessExit.hx.first([None{}, None{}, LAHeadlessExit.hx.ex(_, False{}), LAHeadlessExit.hx.ex(Sp.primary_cause(p), False{}), Sp.when(c, Hx.CCompactionFailed{}), Sp.when(a, Hx.CAutonomousFailed{})], Hx.CAnswered{}) == x : Hx.Cause}
  %Equal.sym(Maybe<&2, Hx.Cause>, Sp.primary_cause(p), Some{x}, failed) : {LAHeadlessExit.hx.first([None{}, None{}, None{}, LAHeadlessExit.hx.ex(_, False{}), Sp.when(c, Hx.CCompactionFailed{}), Sp.when(a, Hx.CAutonomousFailed{})], Hx.CAnswered{}) == x : Hx.Cause}
  {==}
