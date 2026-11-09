# eukhe: the entry's encoders write what the laws spell
#
# The entry's put_* (bend/ffi_infer.bend) and the laws' grammar
# (laws/infer.bend core_infer_spell_*) give the same bytes on every value:
# the cap and a tool field by field, a list its count then item by item
# (a list of Nats by wire_nats_spells), a plan by its tag.

import Base
import ../../../bend/ffi_infer.bend as FIn
import ../../../bend/infer.bend as If
import ../../../bend/wire.bend as Wr
import ../../../laws/infer.bend as Infer
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nats_spells.bend as PWireNatsSpells
import ../base.bend as LA

# the cap
def is.mnat(m: Maybe<&2, Nat>, rest: String) -> {FIn.put_mnat(m, rest) == Infer.core_infer_spell_mnat(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

# the items of a list of tools
def is.items(ts: List<&2, If.ToolPrio>, +rest: String) -> {LA.pc.i_tool_items(ts, rest) == Infer.core_infer_spell_tools.items(ts, rest) : String}:
  match ts:
    case Nil{}:
      {==}
    case Con{x, +t}:
      match x:
        case If.ToolPrio{+i, +p}:
          Equal.cong(String, String, z => Wr.put_nat(i, Wr.put_nat(p, z)), LA.pc.i_tool_items(t, rest), Infer.core_infer_spell_tools.items(t, rest), is.items(t, rest))

# a list of tools: its count, then its items
def is.tools(+ts: List<&2, If.ToolPrio>, +rest: String) -> {Wr.put_list(~If.ToolPrio, ~FIn.put_tool, ts, rest) == Infer.core_infer_spell_tools(ts, rest) : String}:
  Equal.trans(String, Wr.put_list(~If.ToolPrio, ~FIn.put_tool, ts, rest), Wr.put_nat(List.length(&2, If.ToolPrio, ts), LA.pc.i_tool_items(ts, rest)), Infer.core_infer_spell_tools(ts, rest), LA.pc.i_tool_put(ts, rest), Equal.cong(String, String, z => Wr.put_nat(List.length(&2, If.ToolPrio, ts), z), LA.pc.i_tool_items(ts, rest), Infer.core_infer_spell_tools.items(ts, rest), is.items(ts, rest)))

# a request
def is.req(q: FIn.Req, +rest: String) -> {FIn.put_req(q, rest) == Infer.core_infer_spell_req(q, rest) : String}:
  match q:
    case FIn.Req{+cap, +ts, +need}:
      +p2 = Wr.put_list(~Nat, ~Wr.put_nat, need, rest)
      +s2 = LawsBase.wire_spell_nats(need, rest)
      +p1 = Wr.put_list(~If.ToolPrio, ~FIn.put_tool, ts, p2)
      +s1 = Infer.core_infer_spell_tools(ts, s2)
      +e1 = Equal.trans(String, p1, Wr.put_list(~If.ToolPrio, ~FIn.put_tool, ts, s2), s1, Equal.cong(String, String, z => Wr.put_list(~If.ToolPrio, ~FIn.put_tool, ts, z), p2, s2, Wire.wire_nats_spells(need, rest)), is.tools(ts, s2))
      Equal.trans(String, FIn.put_mnat(cap, p1), FIn.put_mnat(cap, s1), Infer.core_infer_spell_mnat(cap, s1), Equal.cong(String, String, z => FIn.put_mnat(cap, z), p1, s1, e1), is.mnat(cap, s1))

# a plan
def is.plan(p: If.Plan, +rest: String) -> {FIn.put_plan(p, rest) == Infer.core_infer_spell_plan(p, rest) : String}:
  match p:
    case If.Fits{+ls}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), Wr.put_list(~Nat, ~Wr.put_nat, ls, rest), LawsBase.wire_spell_nats(ls, rest), Wire.wire_nats_spells(ls, rest))
    case If.Over{i}:
      {==}

# the entry's reply to a request is the spelled reply
def is.answer(q: FIn.Req) -> {FIn.answer(q) == Infer.core_infer_spell_answer(q) : String}:
  match q:
    case FIn.Req{cap, +ts, +need}:
      is.plan(If.plan(cap, ts, need), "")

# a spelled request that fits reads back whole, the rest untouched
def is.read(+q: FIn.Req, +rest: String, h: {Infer.core_infer_fits(q) == True{} : Bool}) -> {Wr.Got{q, rest} == FIn.get_req(Infer.core_infer_spell_req(q, rest)) : Wr.Dec<FIn.Req>}:
  %is.req(q, rest) : {Wr.Got{q, rest} == FIn.get_req(_) : Wr.Dec<FIn.Req>}
  LA.pc.i_req(q, rest, h)

# a spelled request that fits, then rest, gets the entry's answer when
# nothing is left, the left-over error otherwise
def is.run(+q: FIn.Req, +rest: String, h: {Infer.core_infer_fits(q) == True{} : Bool}) -> {FIn.ffi(Infer.core_infer_spell_req(q, rest)) == FIn.ffi.done(Wr.end(rest), q) : String}:
  %is.read(q, rest, h) : {FIn.ffi.go(_) == FIn.ffi.done(Wr.end(rest), q) : String}
  {==}
