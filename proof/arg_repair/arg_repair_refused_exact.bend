# eukhe: the proof of LAW arg_repair_refused_exact
#
# PROOF: the first argument's key (not decoded) has the refusal's first
# hint (arg_repair_spec's lookup), so its step refuses with it (rx.step),
# and a refused first step refuses the call (rx.cons).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./arg_repair_spec.bend as PSpec

def rx.hint(hr: Maybe<&2, String>, -ps: List<&2, Ar.Prop>, -cl: Bool, -als: List<&2, Ar.KV>, -rs: List<&2, Ar.KV>, -ss: List<&2, Ar.Seen>, -k: String, -h: String, -v: Ar.Val, er: {hr == Some{h} : Maybe<&2, String>}) -> {Ar.step.named(Ar.named.hint(hr, Ar.Schema{ps, cl}, als, rs, k), ps, ss, Nil{}, k, v) == Ar.StepNo{Ar.Refused{k, h}} : Ar.Step}:
  %Equal.sym(Maybe<&2, String>, hr, Some{h}, er) : {Ar.step.named(Ar.named.hint(_, Ar.Schema{ps, cl}, als, rs, k), ps, ss, Nil{}, k, v) == Ar.StepNo{Ar.Refused{k, h}} : Ar.Step}
  {==}

def rx.step(sc: Ar.Schema, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, -ks: List<&2, String>, +ss: List<&2, Ar.Seen>, +k: String, +h: String, +v: Ar.Val, hit: {ArgSpec.first_text(k, rs) == Some{h} : Maybe<&2, String>}) -> {Ar.step(sc, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{k, None{}, v}) == Ar.StepNo{Ar.Refused{k, h}} : Ar.Step}:
  match sc:
    case Ar.Schema{+ps, +cl}:
      rx.hint(Ar.lookup(k, rs), ps, cl, als, rs, ss, k, h, v, Equal.trans(Maybe<&2, String>, Ar.lookup(k, rs), ArgSpec.first_text(k, rs), Some{h}, PSpec.rs.lookup(k, rs), hit))

def rx.cons(st: Ar.Step, -rest: Ar.Verdict, -x: Ar.Refusal, e: {st == Ar.StepNo{x} : Ar.Step}) -> {Ar.go.cons(st, rest) == Ar.Rejected{x} : Ar.Verdict}:
  %Equal.sym(Ar.Step, st, Ar.StepNo{x}, e) : {Ar.go.cons(_, rest) == Ar.Rejected{x} : Ar.Verdict}
  {==}

def ArgRepair.arg_repair_refused_exact(sc, als, rs, k, h, v, t, hit):
  +ks = Ar.keys(Ar.Arg{k, None{}, v} <> t)
  +st = Ar.step(sc, Ar.Dialect{als, rs}, ks, Nil{}, Ar.Arg{k, None{}, v})
  rx.cons(st, Ar.go(t, sc, Ar.Dialect{als, rs}, ks, Ar.seen.next(st, Nil{})), Ar.Refused{k, h}, rx.step(sc, als, rs, ks, Nil{}, k, h, v, hit))
