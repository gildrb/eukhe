# eukhe: the proof of LAW model_name_entry_unknown_rule
#
# PROOF: each count and the rule tag read as themselves when they fit and
# as Bad when too long (ws_nat_read); the rule tag 6 + n is Bad both ways,
# a list loop that meets Bad is Bad, so the request is Bad.

import Base
import ../../bend/model_name.bend as M
import ../../bend/ffi_model_name.bend as FM
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/model_name.bend as ModelName
import ../wire/base/spell.bend as LAWireSpell

def mnk.rule_bad(b: Bool, -n: Nat, -rest: String) -> {FM.get_rule.tag(LAWireSpell.ws_nat_answer(b, 6n+n, rest)) == Wr.Bad{} : Wr.Dec<M.Rule>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule at Z is Bad
def mnk.rule(+n: Nat, +rest: String) -> {FM.get_rule(Wr.put_nat(6n+n, rest)) == Wr.Bad{} : Wr.Dec<M.Rule>}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(6n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(6n+n), 6n+n, rest), LAWireSpell.ws_nat_read(6n+n, rest)) : {FM.get_rule.tag(_) == Wr.Bad{} : Wr.Dec<M.Rule>}
  mnk.rule_bad(LawsBase.wire_fits(6n+n), n, rest)

def mnk.rules_go_bad(m: Nat) -> {Wr.get_list.go(~M.Rule, ~FM.get_rule, m, Wr.Bad{}) == Wr.Bad{} : Wr.Dec<List<&2, M.Rule>>}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      {==}

def mnk.sets_go_bad(m: Nat) -> {Wr.get_list.go(~List<&2, M.Rule>, ~FM.get_set, m, Wr.Bad{}) == Wr.Bad{} : Wr.Dec<List<&2, List<&2, M.Rule>>>}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      {==}

def mnk.set_at(b: Bool, +j: Nat, +z: String, hz: {FM.get_rule(z) == Wr.Bad{} : Wr.Dec<M.Rule>}) -> {Wr.get_list.start(~M.Rule, ~FM.get_rule, LAWireSpell.ws_nat_answer(b, 1n+j, z)) == Wr.Bad{} : Wr.Dec<List<&2, M.Rule>>}:
  match b:
    case True{}:
      %Equal.sym(Wr.Dec<M.Rule>, FM.get_rule(z), Wr.Bad{}, hz) : {Wr.get_list.go(~M.Rule, ~FM.get_rule, j, _) == Wr.Bad{} : Wr.Dec<List<&2, M.Rule>>}
      mnk.rules_go_bad(j)
    case False{}:
      {==}

# the set at Y is Bad
def mnk.set(+j: Nat, +z: String, hz: {FM.get_rule(z) == Wr.Bad{} : Wr.Dec<M.Rule>}) -> {FM.get_set(Wr.put_nat(1n+j, z)) == Wr.Bad{} : Wr.Dec<List<&2, M.Rule>>}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n+j, z)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(1n+j), 1n+j, z), LAWireSpell.ws_nat_read(1n+j, z)) : {Wr.get_list.start(~M.Rule, ~FM.get_rule, _) == Wr.Bad{} : Wr.Dec<List<&2, M.Rule>>}
  mnk.set_at(LawsBase.wire_fits(1n+j), j, z, hz)

def mnk.sets_at(b: Bool, +m: Nat, +y: String, hy: {FM.get_set(y) == Wr.Bad{} : Wr.Dec<List<&2, M.Rule>>}) -> {Wr.get_list.start(~List<&2, M.Rule>, ~FM.get_set, LAWireSpell.ws_nat_answer(b, 1n+m, y)) == Wr.Bad{} : Wr.Dec<List<&2, List<&2, M.Rule>>>}:
  match b:
    case True{}:
      %Equal.sym(Wr.Dec<List<&2, M.Rule>>, FM.get_set(y), Wr.Bad{}, hy) : {Wr.get_list.go(~List<&2, M.Rule>, ~FM.get_set, m, _) == Wr.Bad{} : Wr.Dec<List<&2, List<&2, M.Rule>>>}
      mnk.sets_go_bad(m)
    case False{}:
      {==}

def ModelName.model_name_entry_unknown_rule(m, j, n, rest):
  +z = Wr.put_nat(6n+n, rest)
  +y = Wr.put_nat(1n+j, z)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n+m, y)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(1n+m), 1n+m, y), LAWireSpell.ws_nat_read(1n+m, y)) : {FM.ffi.got(FM.get_req.sets(Wr.get_list.start(~List<&2, M.Rule>, ~FM.get_set, _))) == Wr.err("model_name: malformed request") : String}
  %Equal.sym(Wr.Dec<List<&2, List<&2, M.Rule>>>, Wr.get_list.start(~List<&2, M.Rule>, ~FM.get_set, LAWireSpell.ws_nat_answer(LawsBase.wire_fits(1n+m), 1n+m, y)), Wr.Bad{}, mnk.sets_at(LawsBase.wire_fits(1n+m), m, y, mnk.set(j, z, mnk.rule(n, rest)))) : {FM.ffi.got(FM.get_req.sets(_)) == Wr.err("model_name: malformed request") : String}
  {==}
