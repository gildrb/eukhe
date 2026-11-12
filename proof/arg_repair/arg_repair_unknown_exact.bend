# eukhe: the proof of LAW arg_repair_unknown_exact
#
# PROOF: the first argument's key (not decoded) has no refusal, no alias
# and no declaration (base/look.bend's lookups), so a closed schema's
# step refuses it as unknown with the declared names (ux.step), and a
# refused first step refuses the call.

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./base/look.bend as PSpec
import ./arg_repair_refused_exact.bend as PRefusedExact

def ux.alias(ha: Maybe<&2, String>, hp: Maybe<&2, Ar.Prop>, +ps: List<&2, Ar.Prop>, -als: List<&2, Ar.KV>, -rs: List<&2, Ar.KV>, -ss: List<&2, Ar.Seen>, -k: String, -v: Ar.Val, ea: {ha == None{} : Maybe<&2, String>}, ep: {hp == None{} : Maybe<&2, Ar.Prop>}) -> {Ar.step.named(Ar.named.alias(ha, Ar.found(hp), True{}, k, ps, als, rs), ps, ss, Nil{}, k, v) == Ar.StepNo{Ar.Unknown{k, ArgSpec.declared_names(ps)}} : Ar.Step}:
  %Equal.sym(Maybe<&2, String>, ha, None{}, ea) : {Ar.step.named(Ar.named.alias(_, Ar.found(hp), True{}, k, ps, als, rs), ps, ss, Nil{}, k, v) == Ar.StepNo{Ar.Unknown{k, ArgSpec.declared_names(ps)}} : Ar.Step}
  %Equal.sym(Maybe<&2, Ar.Prop>, hp, None{}, ep) : {Ar.step.named(Ar.named.alias(None{}, Ar.found(_), True{}, k, ps, als, rs), ps, ss, Nil{}, k, v) == Ar.StepNo{Ar.Unknown{k, ArgSpec.declared_names(ps)}} : Ar.Step}
  %PSpec.rs.names(ps) : {Ar.StepNo{Ar.Unknown{k, Ar.names(ps)}} == Ar.StepNo{Ar.Unknown{k, _}} : Ar.Step}
  {==}

def ux.hint(hr: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ss: List<&2, Ar.Seen>, +k: String, +v: Ar.Val, er: {hr == None{} : Maybe<&2, String>}, ea: {Ar.lookup(k, als) == None{} : Maybe<&2, String>}, ep: {Ar.prop(k, ps) == None{} : Maybe<&2, Ar.Prop>}) -> {Ar.step.named(Ar.named.hint(hr, Ar.Schema{ps, True{}}, als, rs, k), ps, ss, Nil{}, k, v) == Ar.StepNo{Ar.Unknown{k, ArgSpec.declared_names(ps)}} : Ar.Step}:
  %Equal.sym(Maybe<&2, String>, hr, None{}, er) : {Ar.step.named(Ar.named.hint(_, Ar.Schema{ps, True{}}, als, rs, k), ps, ss, Nil{}, k, v) == Ar.StepNo{Ar.Unknown{k, ArgSpec.declared_names(ps)}} : Ar.Step}
  ux.alias(Ar.lookup(k, als), Ar.prop(k, ps), ps, als, rs, ss, k, v, ea, ep)

def ux.step(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, -ks: List<&2, String>, +ss: List<&2, Ar.Seen>, +k: String, +v: Ar.Val, nr: {ArgSpec.first_text(k, rs) == None{} : Maybe<&2, String>}, na: {ArgSpec.first_text(k, als) == None{} : Maybe<&2, String>}, nd: {ArgSpec.declared(k, ps) == None{} : Maybe<&2, Ar.Prop>}) -> {Ar.step(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{k, None{}, v}) == Ar.StepNo{Ar.Unknown{k, ArgSpec.declared_names(ps)}} : Ar.Step}:
  ux.hint(Ar.lookup(k, rs), ps, als, rs, ss, k, v, Equal.trans(Maybe<&2, String>, Ar.lookup(k, rs), ArgSpec.first_text(k, rs), None{}, PSpec.rs.lookup(k, rs), nr), Equal.trans(Maybe<&2, String>, Ar.lookup(k, als), ArgSpec.first_text(k, als), None{}, PSpec.rs.lookup(k, als), na), Equal.trans(Maybe<&2, Ar.Prop>, Ar.prop(k, ps), ArgSpec.declared(k, ps), None{}, PSpec.rs.prop(k, ps), nd))

def ArgRepair.arg_repair_unknown_exact(ps, als, rs, k, v, t, nr, na, nd):
  +ks = Ar.keys(Ar.Arg{k, None{}, v} <> t)
  +st = Ar.step(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, ks, Nil{}, Ar.Arg{k, None{}, v})
  PRefusedExact.rx.cons(st, Ar.go(t, Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, ks, Ar.seen.next(st, Nil{})), Ar.Unknown{k, ArgSpec.declared_names(ps)}, ux.step(ps, als, rs, ks, Nil{}, k, v, nr, na, nd))
