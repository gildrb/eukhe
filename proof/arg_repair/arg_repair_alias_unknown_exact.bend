# eukhe: the proof of LAW arg_repair_alias_unknown_exact
#
# PROOF: the first argument's key (not decoded) has no refusal, no
# declaration and an alias whose canonical name has no refusal and no
# declaration (arg_repair_spec's lookups), so a closed schema reads it as
# that name unknown (ux2.named), its step refuses with it and the declared
# names, and a refused first step refuses the call.

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./arg_repair_spec.bend as PSpec
import ./arg_repair_refused_exact.bend as PRefusedExact
import ./arg_repair_alias_refused_exact.bend as PAliasRefused

# the key read as its alias's canonical name, unknown
def ux2.named(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +k: String, +c: String, er: {Ar.lookup(k, rs) == None{} : Maybe<&2, String>}, ed: {Ar.found(Ar.prop(k, ps)) == False{} : Bool}, ea: {Ar.lookup(k, als) == Some{c} : Maybe<&2, String>}, ecr: {Ar.lookup(c, rs) == None{} : Maybe<&2, String>}, ecd: {Ar.found(Ar.prop(c, ps)) == False{} : Bool}) -> {Ar.named(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, k) == Ar.NUnknown{c, Ar.names(ps)} : Ar.Named}:
  %Equal.sym(Maybe<&2, String>, Ar.lookup(k, rs), None{}, er) : {Ar.named.hint(_, Ar.Schema{ps, True{}}, als, rs, k) == Ar.NUnknown{c, Ar.names(ps)} : Ar.Named}
  %Equal.sym(Maybe<&2, String>, Ar.lookup(k, als), Some{c}, ea) : {Ar.named.alias(_, Ar.found(Ar.prop(k, ps)), True{}, k, ps, als, rs) == Ar.NUnknown{c, Ar.names(ps)} : Ar.Named}
  %Equal.sym(Bool, Ar.found(Ar.prop(k, ps)), False{}, ed) : {Ar.named.alias(Some{c}, _, True{}, k, ps, als, rs) == Ar.NUnknown{c, Ar.names(ps)} : Ar.Named}
  %Equal.sym(Maybe<&2, String>, Ar.lookup(c, rs), None{}, ecr) : {Ar.named.target(_, Ar.found(Ar.prop(c, ps)), True{}, Ar.lookup(c, als), c, ps) == Ar.NUnknown{c, Ar.names(ps)} : Ar.Named}
  %Equal.sym(Bool, Ar.found(Ar.prop(c, ps)), False{}, ecd) : {Ar.named.target(None{}, _, True{}, Ar.lookup(c, als), c, ps) == Ar.NUnknown{c, Ar.names(ps)} : Ar.Named}
  {==}

def ux2.step(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, -ks: List<&2, String>, +ss: List<&2, Ar.Seen>, +k: String, +c: String, +v: Ar.Val, en: {Ar.named(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, k) == Ar.NUnknown{c, Ar.names(ps)} : Ar.Named}) -> {Ar.step(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{k, None{}, v}) == Ar.StepNo{Ar.Unknown{c, ArgSpec.declared_names(ps)}} : Ar.Step}:
  %Equal.sym(Ar.Named, Ar.named(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, k), Ar.NUnknown{c, Ar.names(ps)}, en) : {Ar.step.named(_, ps, ss, Nil{}, k, v) == Ar.StepNo{Ar.Unknown{c, ArgSpec.declared_names(ps)}} : Ar.Step}
  %PSpec.rs.names(ps) : {Ar.StepNo{Ar.Unknown{c, Ar.names(ps)}} == Ar.StepNo{Ar.Unknown{c, _}} : Ar.Step}
  {==}

def ArgRepair.arg_repair_alias_unknown_exact(ps, als, rs, k, c, v, t, nr, nd, al, cr, cd):
  +ks = Ar.keys(Ar.Arg{k, None{}, v} <> t)
  +st = Ar.step(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, ks, Nil{}, Ar.Arg{k, None{}, v})
  +en = ux2.named(ps, als, rs, k, c, PAliasRefused.ax.look(k, rs, None{}, nr), PAliasRefused.ax.undeclared(k, ps, nd), PAliasRefused.ax.look(k, als, Some{c}, al), PAliasRefused.ax.look(c, rs, None{}, cr), PAliasRefused.ax.undeclared(c, ps, cd))
  PRefusedExact.rx.cons(st, Ar.go(t, Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, ks, Ar.seen.next(st, Nil{})), Ar.Unknown{c, ArgSpec.declared_names(ps)}, ux2.step(ps, als, rs, ks, Nil{}, k, c, v, en))
