# eukhe: lemmas the proofs of the config entry share (bend/ffi_config.bend):
# the entry reads every input as the reader of spec/settings/config.bend
# does (LFR.pfc.ask); a request read whole is answered as the laws spell
# its decision (LFP.pfr.answer); anything else is the error form.

import Base
import ../../../bend/ffi_config.bend as FC
import ../../../bend/wire.bend as Wr
import ../../../spec/settings/config.bend as CS
import ./ffi_read.bend as LFR
import ./ffi_reply.bend as LFP
import ../../../bend/config.bend as Cf
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../base/wire.bend as LWire
import ../../base/logic/string.bend as LLogicString

# the answer to what the reader read: the error form, or the decision
def pto.of(m: Maybe<&2, FC.Ask>) -> String:
  match m:
    case None{}:
      Wr.err("config: malformed request")
    case Some{a}:
      CS.cf_w_reply(a)

def pto.end(b: Bool, a: FC.Ask) -> {FC.run.end(b, a) == pto.of(CS.cf_r_end(b, a)) : String}:
  match b:
    case True{}:
      LFP.pfr.answer(a)
    case False{}:
      {==}

def pto.whole(r: Wr.Dec<FC.Ask>) -> {FC.run(r) == pto.of(CS.cf_r_whole(r)) : String}:
  match r:
    case Wr.Got{a, s}:
      pto.end(Wr.end(s), a)
    case Wr.Bad{}:
      {==}

# the entry answers what the reader reads
def pto.ffi(+s: String) -> {FC.ffi(s) == pto.of(CS.cf_read(s)) : String}:
  %Equal.sym(Wr.Dec<FC.Ask>, FC.get_ask(Wr.get_nat(s)), CS.cf_r_ask(Wr.get_nat(s)), LFR.pfc.ask(Wr.get_nat(s))) : {FC.run(_) == pto.of(CS.cf_read(s)) : String}
  pto.whole(CS.cf_r_ask(Wr.get_nat(s)))

def pto.write_not_err(w: Cf.Write) -> {LawsBase.wire_opens_err(CS.cf_w_write(w)) == False{} : Bool}:
  match w:
    case Cf.Refused{}:
      Wire.wire_nat_not_err(0n, "")
    case Cf.Wrote{+d}:
      Wire.wire_nat_not_err(1n, CS.cf_w_entries(d, ""))

def pto.nats_not_err(+xs: List<&2, Nat>, +rest: String) -> {LawsBase.wire_opens_err(Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)) == False{} : Bool}:
  %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest), Wr.put_nat(List.length(&2, Nat, xs), LLogicString.wr_items(xs, rest)), LWire.wr_put_list(xs, rest)) : {LawsBase.wire_opens_err(_) == False{} : Bool}
  Wire.wire_nat_not_err(List.length(&2, Nat, xs), LLogicString.wr_items(xs, rest))

# a decision never opens with the error form
def pto.reply_not_err(a: FC.Ask) -> {LawsBase.wire_opens_err(CS.cf_w_reply(a)) == False{} : Bool}:
  match a:
    case FC.AskRmw{r, e}:
      pto.write_not_err(Cf.rmw(r, e))
    case FC.AskLeaves{+ls}:
      pto.nats_not_err(Cf.applied(ls), Wr.put_list(~Nat, ~Wr.put_nat, Cf.reported(ls), ""))
    case FC.AskLimits{s, qs}:
      +ls = Cf.limits(s, qs)
      Wire.wire_nat_not_err(List.length(&2, Cf.Lim, ls), CS.cf_w_lims(ls, ""))
    case FC.AskTrust{+t, +ks}:
      +es = Cf.project(t, Nil{}, ks)
      Wire.wire_nat_not_err(List.length(&2, Cf.Entry, es), CS.cf_w_entries.items(es, Wr.put_list(~String, ~Wr.put_str, Cf.withheld(t, ks), "")))
    case FC.AskMerge{g, p, qs}:
      +ms = Cf.finds(Cf.merge(g, p), qs)
      Wire.wire_nat_not_err(List.length(&2, Maybe<&2, List<&2, Cf.Entry>>, ms), CS.cf_w_founds(ms, ""))
