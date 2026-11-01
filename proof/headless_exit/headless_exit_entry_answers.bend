# eukhe: the proof of LAW headless_exit_entry_answers
#
# PROOF: the entry's decoder is the laws' reader (hx.req), which reads
# the spelled request back whole with nothing left (hx.req_rt), so the
# entry answers the model's exit, which is the spec's
# (headless_exit_refines_spec), spelled as the spec spells it (hx.put).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless.bend as Sp
import ../../spec/durable/headless_wire.bend as SpW
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit
import ./headless_exit_refines_spec.bend as PHeadlessExitRefinesSpec

def hx.put_reason(r: Hx.Reason, -rest: String) -> {FHx.put_reason(r, rest) == SpW.w_reason(r, rest) : String}:
  match r:
    case Hx.ModelError{}:
      {==}
    case Hx.RunLimit{}:
      {==}
    case Hx.NoModel{}:
      {==}
    case Hx.ForcedTool{}:
      {==}
    case Hx.Faulted{}:
      {==}
    case Hx.Aborted{}:
      {==}
    case Hx.Reset{}:
      {==}
    case Hx.Stale{}:
      {==}
    case Hx.Withdrawn{}:
      {==}
    case Hx.Other{}:
      {==}

def hx.put_cause(c: Hx.Cause, +rest: String) -> {FHx.put_cause(c, rest) == SpW.w_cause(c, rest) : String}:
  match c:
    case Hx.CAnswered{}:
      {==}
    case Hx.CCommandFailed{}:
      {==}
    case Hx.CGaveUp{}:
      {==}
    case Hx.CRunFailed{+r}:
      %hx.put_reason(r, rest) : {Wr.put_nat(3n, FHx.put_reason(r, rest)) == Wr.put_nat(3n, _) : String}
      {==}
    case Hx.CProviderError{}:
      {==}
    case Hx.CAborted{}:
      {==}
    case Hx.CUnfinished{}:
      {==}
    case Hx.CSlashFailed{}:
      {==}
    case Hx.CCompactionFailed{}:
      {==}
    case Hx.CAutonomousFailed{}:
      {==}

# the entry spells an exit as the spec does
def hx.put(v: Hx.Verdict, +rest: String) -> {FHx.put_verdict(v, rest) == SpW.w_verdict(v, rest) : String}:
  match v:
    case Hx.Verdict{+n, +c}:
      %hx.put_cause(c, rest) : {Wr.put_nat(n, FHx.put_cause(c, rest)) == Wr.put_nat(n, _) : String}
      {==}

def HeadlessExit.headless_exit_entry_answers(f):
  +s = SpW.w_exit_req(f, "")
  %Equal.sym(Wr.Dec<Hx.Facts>, FHx.get_facts(s), SpW.r_exit(s), LAHeadlessExit.hx.req(s)) : {FHx.ffi.got(_) == SpW.w_exit_reply(f) : String}
  %Equal.sym(Wr.Dec<Hx.Facts>, SpW.r_exit(s), Wr.Got{f, ""}, LAHeadlessExit.hx.req_rt(f, "")) : {FHx.ffi.got(_) == SpW.w_exit_reply(f) : String}
  %Equal.sym(Hx.Verdict, Hx.decide(f), Sp.exit_spec(f), HeadlessExit.headless_exit_refines_spec(f)) : {FHx.put_verdict(_, "") == SpW.w_verdict(Sp.exit_spec(f), "") : String}
  hx.put(Sp.exit_spec(f), "")
