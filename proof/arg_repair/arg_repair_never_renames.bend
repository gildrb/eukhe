# eukhe: the proof of LAW arg_repair_never_renames
#
# PROOF: by induction over the arguments, the sent keys and the names
# taken generalized (nr.go): a refused step refuses the call; a repaired
# step's name satisfies the naming facts (sv.step): a declared key keeps
# its name, an unaliased key keeps its name (nr.one); a decoded key claims
# nothing.

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./base.bend as AB
import ./base/step.bend as SV
import ./arg_repair_spec.bend as PSpec

# the claim about a verdict, the sent keys ks given
def nr.KO(ps: List<&2, Ar.Prop>, als: List<&2, Ar.KV>, ks: List<&2, String>, args: List<&2, Ar.Arg>, v: Ar.Verdict) -> Bool:
  match v:
    case Ar.Repaired{os, rs}:
      ArgRepair.ar_keys_ok.go(ps, als, ks, args, os)
    case Ar.Rejected{x}:
      True{}

def nr.conv(-ps: List<&2, Ar.Prop>, -cl: Bool, -als: List<&2, Ar.KV>, -rs: List<&2, Ar.KV>, -args: List<&2, Ar.Arg>, v: Ar.Verdict) -> {nr.KO(ps, als, ArgSpec.sent_keys(args), args, v) == ArgRepair.ar_keys_ok(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, args, v) : Bool}:
  match v:
    case Ar.Repaired{os, xs}:
      {==}
    case Ar.Rejected{x}:
      {==}

def nr.alias(ha: Maybe<&2, String>, -dec: Bool, -k: String, -c: String, h: {SV.sv.nalias(ha, dec, k, c) == True{} : Bool}) -> {ArgRepair.ar_implies(ArgRepair.ar_none(ha), String.eq(c, k)) == True{} : Bool}:
  match ha:
    case None{}:
      h
    case Some{a}:
      {==}

# the claim for one argument, from the naming facts of its key read
def nr.one(dm: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +k: String, +c: String, h: {SV.sv.nok2(Ar.lookup(ArgRepair.ar_cur(dm, k), rs), Ar.lookup(ArgRepair.ar_cur(dm, k), als), Ar.found(Ar.prop(ArgRepair.ar_cur(dm, k), ps)), cl, ArgRepair.ar_cur(dm, k), c) == True{} : Bool}) -> {ArgRepair.ar_keys_ok.one(ps, als, dm, k, c) == True{} : Bool}:
  match dm:
    case Some{p}:
      {==}
    case None{}:
      +hh = h
      %PSpec.rs.prop(k, ps) : {Bool.and(ArgRepair.ar_implies(ArgSpec.is_some(_), String.eq(c, k)), ArgRepair.ar_implies(ArgRepair.ar_none(ArgSpec.first_text(k, als)), String.eq(c, k))) == True{} : Bool}
      %PSpec.rs.found(Ar.prop(k, ps)) : {Bool.and(ArgRepair.ar_implies(_, String.eq(c, k)), ArgRepair.ar_implies(ArgRepair.ar_none(ArgSpec.first_text(k, als)), String.eq(c, k))) == True{} : Bool}
      %PSpec.rs.lookup(k, als) : {Bool.and(ArgRepair.ar_implies(Ar.found(Ar.prop(k, ps)), String.eq(c, k)), ArgRepair.ar_implies(ArgRepair.ar_none(_), String.eq(c, k))) == True{} : Bool}
      SV.sv.and2(ArgRepair.ar_implies(Ar.found(Ar.prop(k, ps)), String.eq(c, k)), ArgRepair.ar_implies(ArgRepair.ar_none(Ar.lookup(k, als)), String.eq(c, k)), SV.sv.nok_dec(Ar.lookup(k, rs), Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, k, c, hh), nr.alias(Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), k, c, SV.sv.nok_alias(Ar.lookup(k, rs), Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, k, c, hh)))

def nr.arg(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, ss: List<&2, Ar.Seen>, a: Ar.Arg, o: Ar.Out, r: List<&2, Ar.Record>, s: Ar.Seen, h: SV.sv.SVa(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a, Ar.StepOk{o, r, s})) -> {ArgRepair.ar_keys_ok.arg(ps, als, ks, a, o) == True{} : Bool}:
  match a:
    case Ar.Arg{+k, +m, v}:
      match o:
        case Ar.Out{+c, to}:
          (hn, rest) = h
          %PSpec.rs.decoded(ks, k, m) : {ArgRepair.ar_keys_ok.one(ps, als, _, k, c) == True{} : Bool}
          nr.one(Ar.decoded(ks, k, m), ps, cl, als, rs, k, c, hn)

def nr.cons(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, ss: List<&2, Ar.Seen>, a: Ar.Arg, t: List<&2, Ar.Arg>, st: Ar.Step, h: SV.sv.SVa(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a, st), rest: Ar.Verdict, ih: {nr.KO(ps, als, ks, t, rest) == True{} : Bool}) -> {nr.KO(ps, als, ks, a <> t, Ar.go.cons(st, rest)) == True{} : Bool}:
  match st:
    case Ar.StepNo{x}:
      {==}
    case Ar.StepOk{+o, +r, +s}:
      match rest:
        case Ar.Rejected{x}:
          {==}
        case Ar.Repaired{os, xs}:
          SV.sv.and2(ArgRepair.ar_keys_ok.arg(ps, als, ks, a, o), ArgRepair.ar_keys_ok.go(ps, als, ks, t, os), nr.arg(ps, cl, als, rs, ks, ss, a, o, r, s, h), ih)

def nr.go(args: List<&2, Ar.Arg>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>) -> {nr.KO(ps, als, ks, args, Ar.go(args, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss)) == True{} : Bool}:
  match args:
    case Nil{}:
      {==}
    case +a <> +t:
      +st = Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a)
      nr.cons(ps, cl, als, rs, ks, ss, a, t, st, SV.sv.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a), Ar.go(t, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, Ar.seen.next(st, ss)), nr.go(t, ps, cl, als, rs, ks, Ar.seen.next(st, ss)))

def ArgRepair.arg_repair_never_renames(sc, d, args):
  match sc:
    case Ar.Schema{+ps, +cl}:
      match d:
        case Ar.Dialect{+als, +rs}:
          +v = Ar.go(args, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, Ar.keys(args), Nil{})
          %nr.conv(ps, cl, als, rs, args, v) : {_ == True{} : Bool}
          %PSpec.rs.keys(args) : {nr.KO(ps, als, _, args, v) == True{} : Bool}
          nr.go(args, ps, cl, als, rs, Ar.keys(args), Nil{})
