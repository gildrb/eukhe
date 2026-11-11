# eukhe: the proof of LAW arg_repair_alias_refused_exact
#
# PROOF: the first argument's key (not decoded) has no refusal, no
# declaration and an alias whose canonical name has the refusal's first
# hint (the lookups of base/look.bend), so it is read as that name refused
# (ax.named), its step refuses with it (ax.step), and a refused first step
# refuses the call.

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./base/look.bend as PSpec
import ./arg_repair_refused_exact.bend as PRefusedExact

# a key's lookups, as the spec's
def ax.look(+k: String, +kvs: List<&2, Ar.KV>, -m: Maybe<&2, String>, e: {ArgSpec.first_text(k, kvs) == m : Maybe<&2, String>}) -> {Ar.lookup(k, kvs) == m : Maybe<&2, String>}:
  Equal.trans(Maybe<&2, String>, Ar.lookup(k, kvs), ArgSpec.first_text(k, kvs), m, PSpec.rs.lookup(k, kvs), e)

# an undeclared key, as the spec's
def ax.undeclared(+k: String, +ps: List<&2, Ar.Prop>, e: {ArgSpec.declared(k, ps) == None{} : Maybe<&2, Ar.Prop>}) -> {Ar.found(Ar.prop(k, ps)) == False{} : Bool}:
  Equal.cong(Maybe<&2, Ar.Prop>, Bool, q => Ar.found(q), Ar.prop(k, ps), None{}, Equal.trans(Maybe<&2, Ar.Prop>, Ar.prop(k, ps), ArgSpec.declared(k, ps), None{}, PSpec.rs.prop(k, ps), e))

# the key read as its alias's canonical name, refused
def ax.named(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +k: String, +c: String, +h: String, er: {Ar.lookup(k, rs) == None{} : Maybe<&2, String>}, ed: {Ar.found(Ar.prop(k, ps)) == False{} : Bool}, ea: {Ar.lookup(k, als) == Some{c} : Maybe<&2, String>}, ec: {Ar.lookup(c, rs) == Some{h} : Maybe<&2, String>}) -> {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k) == Ar.NRefused{c, h} : Ar.Named}:
  %Equal.sym(Maybe<&2, String>, Ar.lookup(k, rs), None{}, er) : {Ar.named.hint(_, Ar.Schema{ps, cl}, als, rs, k) == Ar.NRefused{c, h} : Ar.Named}
  %Equal.sym(Maybe<&2, String>, Ar.lookup(k, als), Some{c}, ea) : {Ar.named.alias(_, Ar.found(Ar.prop(k, ps)), cl, k, ps, als, rs) == Ar.NRefused{c, h} : Ar.Named}
  %Equal.sym(Bool, Ar.found(Ar.prop(k, ps)), False{}, ed) : {Ar.named.alias(Some{c}, _, cl, k, ps, als, rs) == Ar.NRefused{c, h} : Ar.Named}
  %Equal.sym(Maybe<&2, String>, Ar.lookup(c, rs), Some{h}, ec) : {Ar.named.target(_, Ar.found(Ar.prop(c, ps)), cl, Ar.lookup(c, als), c, ps) == Ar.NRefused{c, h} : Ar.Named}
  {==}

def ax.step(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, -ks: List<&2, String>, +ss: List<&2, Ar.Seen>, +k: String, +c: String, +h: String, +v: Ar.Val, en: {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k) == Ar.NRefused{c, h} : Ar.Named}) -> {Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{k, None{}, v}) == Ar.StepNo{Ar.Refused{c, h}} : Ar.Step}:
  %Equal.sym(Ar.Named, Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k), Ar.NRefused{c, h}, en) : {Ar.step.named(_, ps, ss, Nil{}, k, v) == Ar.StepNo{Ar.Refused{c, h}} : Ar.Step}
  {==}

def ArgRepair.arg_repair_alias_refused_exact(ps, cl, als, rs, k, c, h, v, t, nr, nd, al, hit):
  +ks = Ar.keys(Ar.Arg{k, None{}, v} <> t)
  +st = Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, Nil{}, Ar.Arg{k, None{}, v})
  +en = ax.named(ps, cl, als, rs, k, c, h, ax.look(k, rs, None{}, nr), ax.undeclared(k, ps, nd), ax.look(k, als, Some{c}, al), ax.look(c, rs, Some{h}, hit))
  PRefusedExact.rx.cons(st, Ar.go(t, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, Ar.seen.next(st, Nil{})), Ar.Refused{c, h}, ax.step(ps, cl, als, rs, ks, Nil{}, k, c, h, v, en))
