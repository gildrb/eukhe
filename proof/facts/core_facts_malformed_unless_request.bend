# eukhe: the proof of LAW core_facts_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (fd.req of core_facts_reads_only_requests); when it reads
# none the entry answers the malformed error, which the premise excludes.

import Base
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts/budgets.bend as FactsBudgets
import ../wire/base/spell.bend as LAWireSpell
import ./core_facts_reads_only_requests.bend as PCoreFactsReadsOnlyRequests

def fmu.goal(+s: String) -> Type:
  &q: FFx.Req -> &rest: String -> {(s, FactsBudgets.core_facts_req_fits(q)) == (FactsBudgets.facts_spell_req(q, rest), True{}) : String & Bool}

def fmu.eq(+s: String, +q: FFx.Req, +rest: String, e1: {s == FactsBudgets.facts_spell_req(q, rest) : String}, e2: {FactsBudgets.core_facts_req_fits(q) == True{} : Bool}) -> {(s, FactsBudgets.core_facts_req_fits(q)) == (FactsBudgets.facts_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, FactsBudgets.facts_spell_req(q, rest), e1) : {(_, FactsBudgets.core_facts_req_fits(q)) == (FactsBudgets.facts_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, FactsBudgets.core_facts_req_fits(q), True{}, e2) : {(FactsBudgets.facts_spell_req(q, rest), _) == (FactsBudgets.facts_spell_req(q, rest), True{}) : String & Bool}
  {==}

def fmu.main(+s: String, d: Wr.Dec<FFx.Req>, inv: PCoreFactsReadsOnlyRequests.fd.Req(s, d), other: {String.eq(FFx.ffi.go(d), Wr.err("budget request: malformed")) == False{} : Bool}) -> fmu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, fmu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(fmu.goal(s), other)

def FactsBudgets.core_facts_malformed_unless_request(s, other):
  fmu.main(s, FFx.get_req(s), PCoreFactsReadsOnlyRequests.fd.req(s), other)
