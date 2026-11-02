# eukhe: the proof of LAW headless_exit_entry_exact
#
# PROOF: the entry reads every input as the laws' reader does (hx.req); a
# request read whole is answered with the model's exit, which is the
# spec's (headless_exit_refines_spec), spelled as the spec spells it
# (hx.put); any other input gets the error form on both sides.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless.bend as Sp
import ../../spec/durable/headless_wire.bend as SpW
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit
import ./headless_exit_refines_spec.bend as PHeadlessExitRefinesSpec
import ./headless_exit_entry_answers.bend as PHeadlessExitEntryAnswers

def hxe.end(e: Bool, +f: Hx.Facts) -> {FHx.ffi.done(f, e) == HeadlessExit.exit_entry.whole(SpW.r_exit_whole.end(e, f)) : String}:
  match e:
    case True{}:
      %Equal.sym(Hx.Verdict, Hx.decide(f), Sp.exit_spec(f), HeadlessExit.headless_exit_refines_spec(f)) : {FHx.put_verdict(_, "") == SpW.w_verdict(Sp.exit_spec(f), "") : String}
      PHeadlessExitEntryAnswers.hx.put(Sp.exit_spec(f), "")
    case False{}:
      {==}

def hxe.whole(r: Wr.Dec<Hx.Facts>) -> {FHx.ffi.got(r) == HeadlessExit.exit_entry.whole(SpW.r_exit_whole(r)) : String}:
  match r:
    case Wr.Got{f, +s}:
      hxe.end(Wr.end(s), f)
    case Wr.Bad{}:
      {==}

def HeadlessExit.headless_exit_entry_exact(s):
  %Equal.sym(Wr.Dec<Hx.Facts>, FHx.get_facts(s), SpW.r_exit(s), LAHeadlessExit.hx.req(s)) : {FHx.ffi.got(_) == HeadlessExit.exit_entry(s) : String}
  hxe.whole(SpW.r_exit(s))
