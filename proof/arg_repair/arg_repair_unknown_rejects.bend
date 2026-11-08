# eukhe: the proof of LAW arg_repair_unknown_rejects
#
# PROOF: by induction over the arguments, the names taken generalized
# (ru.go): a closed schema's repaired step reads a declared key or an
# alias (sv.step, sv.nok_cl), so when the unknown key is this argument's
# the step refuses; else the rest of the call is refused.

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./base.bend as AB
import ./base/step.bend as SV
import ./arg_repair_spec.bend as PSpec

def ru.or_l(b1: Bool, -b2: Bool, e1: {b1 == False{} : Bool}, eb: {Bool.or(b1, b2) == True{} : Bool}) -> {b2 == True{} : Bool}:
  match b1:
    case True{}:
      AB.ab.absurd_tf({b2 == True{} : Bool}, e1)
    case False{}:
      eb

def ru.known(dec: Bool, ha: Maybe<&2, String>, h: {Bool.or(dec, Maybe.is_some(&2, String, ha)) == True{} : Bool}) -> {Bool.and(Bool.not(dec), ArgRepair.ar_none(ha)) == False{} : Bool}:
  match dec:
    case True{}:
      {==}
    case False{}:
      match ha:
        case None{}:
          AB.ab.absurd({Bool.and(Bool.not(False{}), ArgRepair.ar_none(None{})) == False{} : Bool}, h)
        case Some{x}:
          {==}

# a closed schema's repaired step reads a declared key or an alias
def ru.head(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +k: String, +m: Maybe<&2, String>, +c: String, hn: {SV.sv.nok2(Ar.lookup(ArgRepair.ar_cur(Ar.decoded(ks, k, m), k), rs), Ar.lookup(ArgRepair.ar_cur(Ar.decoded(ks, k, m), k), als), Ar.found(Ar.prop(ArgRepair.ar_cur(Ar.decoded(ks, k, m), k), ps)), True{}, ArgRepair.ar_cur(Ar.decoded(ks, k, m), k), c) == True{} : Bool}) -> {Bool.and(Bool.not(ArgSpec.is_some(ArgSpec.declared(ArgRepair.ar_cur(ArgSpec.decoding(ks, k, m), k), ps))), ArgRepair.ar_none(ArgSpec.first_text(ArgRepair.ar_cur(ArgSpec.decoding(ks, k, m), k), als))) == False{} : Bool}:
  +cur = ArgRepair.ar_cur(Ar.decoded(ks, k, m), k)
  %PSpec.rs.decoded(ks, k, m) : {Bool.and(Bool.not(ArgSpec.is_some(ArgSpec.declared(ArgRepair.ar_cur(_, k), ps))), ArgRepair.ar_none(ArgSpec.first_text(ArgRepair.ar_cur(_, k), als))) == False{} : Bool}
  %PSpec.rs.prop(cur, ps) : {Bool.and(Bool.not(ArgSpec.is_some(_)), ArgRepair.ar_none(ArgSpec.first_text(cur, als))) == False{} : Bool}
  %PSpec.rs.found(Ar.prop(cur, ps)) : {Bool.and(Bool.not(_), ArgRepair.ar_none(ArgSpec.first_text(cur, als))) == False{} : Bool}
  %PSpec.rs.lookup(cur, als) : {Bool.and(Bool.not(Ar.found(Ar.prop(cur, ps))), ArgRepair.ar_none(_)) == False{} : Bool}
  ru.known(Ar.found(Ar.prop(cur, ps)), Ar.lookup(cur, als), SV.sv.nok_cl(Ar.lookup(cur, rs), Ar.lookup(cur, als), Ar.found(Ar.prop(cur, ps)), True{}, cur, c, hn))

def ru.end(-c: String, -to: Maybe<&2, Ar.To>, -r: List<&2, Ar.Record>, -s: Ar.Seen, rest: Ar.Verdict, -b2: Bool, ih: {b2 == True{} : Bool} -> {ArgRepair.ar_rejected(rest) == True{} : Bool}, hb: {b2 == True{} : Bool}) -> {ArgRepair.ar_rejected(Ar.go.cons(Ar.StepOk{Ar.Out{c, to}, r, s}, rest)) == True{} : Bool}:
  match rest:
    case Ar.Rejected{x}:
      {==}
    case Ar.Repaired{os, xs}:
      AB.ab.absurd({ArgRepair.ar_rejected(Ar.Repaired{Ar.Out{c, to} <> os, List.append(&2, Ar.Record, r, xs)}) == True{} : Bool}, ih(hb))

def ru.cons(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, ss: List<&2, Ar.Seen>, +k: String, +m: Maybe<&2, String>, v: Ar.Val, st: Ar.Step, h: SV.sv.SVa(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{k, m, v}, st), rest: Ar.Verdict, b2: Bool, eb: {Bool.or(Bool.and(Bool.not(ArgSpec.is_some(ArgSpec.declared(ArgRepair.ar_cur(ArgSpec.decoding(ks, k, m), k), ps))), ArgRepair.ar_none(ArgSpec.first_text(ArgRepair.ar_cur(ArgSpec.decoding(ks, k, m), k), als))), b2) == True{} : Bool}, ih: {b2 == True{} : Bool} -> {ArgRepair.ar_rejected(rest) == True{} : Bool}) -> {ArgRepair.ar_rejected(Ar.go.cons(st, rest)) == True{} : Bool}:
  match st:
    case Ar.StepNo{x}:
      {==}
    case Ar.StepOk{o, r, s}:
      match o:
        case Ar.Out{+c, to}:
          (hn, more) = h
          ru.end(c, to, r, s, rest, b2, ih, ru.or_l(Bool.and(Bool.not(ArgSpec.is_some(ArgSpec.declared(ArgRepair.ar_cur(ArgSpec.decoding(ks, k, m), k), ps))), ArgRepair.ar_none(ArgSpec.first_text(ArgRepair.ar_cur(ArgSpec.decoding(ks, k, m), k), als))), b2, ru.head(ps, als, rs, ks, k, m, c, hn), eb))

def ru.go(args: List<&2, Ar.Arg>, +ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>, bad: {ArgRepair.ar_some_unknown.go(ps, als, ks, args) == True{} : Bool}) -> {ArgRepair.ar_rejected(Ar.go(args, Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, ks, ss)) == True{} : Bool}:
  match args:
    case Nil{}:
      AB.ab.absurd({ArgRepair.ar_rejected(Ar.Repaired{Nil{}, Nil{}}) == True{} : Bool}, bad)
    case +a <> +t:
      match a:
        case Ar.Arg{+k, +m, +v}:
          +st = Ar.step(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{k, m, v})
          ru.cons(ps, als, rs, ks, ss, k, m, v, st, SV.sv.step(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{k, m, v}), Ar.go(t, Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, ks, Ar.seen.next(st, ss)), ArgRepair.ar_some_unknown.go(ps, als, ks, t), bad, e => ru.go(t, ps, als, rs, ks, Ar.seen.next(st, ss), e))

def ru.keys(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +args: List<&2, Ar.Arg>, bad: {ArgRepair.ar_some_unknown.go(ps, als, ArgSpec.sent_keys(args), args) == True{} : Bool}) -> {ArgRepair.ar_some_unknown.go(ps, als, Ar.keys(args), args) == True{} : Bool}:
  %Equal.sym(List<&2, String>, Ar.keys(args), ArgSpec.sent_keys(args), PSpec.rs.keys(args)) : {ArgRepair.ar_some_unknown.go(ps, als, _, args) == True{} : Bool}
  bad

def ArgRepair.arg_repair_unknown_rejects(ps, d, args, bad):
  match d:
    case Ar.Dialect{+als, +rs}:
      ru.go(args, ps, als, rs, Ar.keys(args), Nil{}, ru.keys(ps, als, args, bad))
