# eukhe: the proof of LAW arg_repair_refused_rejects
#
# PROOF: by induction over the arguments, the names taken generalized
# (rr.go): a repaired step's key read is not refused (sv.step, sv.nok_hr),
# so when the refused key is this argument's the step refuses; else the
# rest of the call is refused (the hypothesis), and a refusal of the rest
# refuses the call.

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./base.bend as AB
import ./base/step.bend as SV
import ./base/look.bend as PSpec

def rr.none_some(m: Maybe<&2, String>, e: {ArgRepair.ar_none(m) == True{} : Bool}) -> {Maybe.is_some(&2, String, m) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      AB.ab.absurd({Maybe.is_some(&2, String, Some{x}) == False{} : Bool}, e)

def rr.or_l(b1: Bool, -b2: Bool, e1: {b1 == False{} : Bool}, eb: {Bool.or(b1, b2) == True{} : Bool}) -> {b2 == True{} : Bool}:
  match b1:
    case True{}:
      AB.ab.absurd_tf({b2 == True{} : Bool}, e1)
    case False{}:
      eb

# a repaired step's key read is not refused
def rr.head(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +k: String, +m: Maybe<&2, String>, +c: String, hn: {SV.sv.nok2(Ar.lookup(ArgRepair.ar_cur(Ar.decoded(ks, k, m), k), rs), Ar.lookup(ArgRepair.ar_cur(Ar.decoded(ks, k, m), k), als), Ar.found(Ar.prop(ArgRepair.ar_cur(Ar.decoded(ks, k, m), k), ps)), cl, ArgRepair.ar_cur(Ar.decoded(ks, k, m), k), c) == True{} : Bool}) -> {Maybe.is_some(&2, String, ArgSpec.first_text(ArgRepair.ar_cur(ArgSpec.decoding(ks, k, m), k), rs)) == False{} : Bool}:
  +cur = ArgRepair.ar_cur(Ar.decoded(ks, k, m), k)
  %PSpec.rs.decoded(ks, k, m) : {Maybe.is_some(&2, String, ArgSpec.first_text(ArgRepair.ar_cur(_, k), rs)) == False{} : Bool}
  %PSpec.rs.lookup(cur, rs) : {Maybe.is_some(&2, String, _) == False{} : Bool}
  rr.none_some(Ar.lookup(cur, rs), SV.sv.nok_hr(Ar.lookup(cur, rs), Ar.lookup(cur, als), Ar.found(Ar.prop(cur, ps)), cl, cur, c, hn))

def rr.end(-c: String, -to: Maybe<&2, Ar.To>, -r: List<&2, Ar.Record>, -s: Ar.Seen, rest: Ar.Verdict, -b2: Bool, ih: {b2 == True{} : Bool} -> {ArgRepair.ar_rejected(rest) == True{} : Bool}, hb: {b2 == True{} : Bool}) -> {ArgRepair.ar_rejected(Ar.go.cons(Ar.StepOk{Ar.Out{c, to}, r, s}, rest)) == True{} : Bool}:
  match rest:
    case Ar.Rejected{x}:
      {==}
    case Ar.Repaired{os, xs}:
      AB.ab.absurd({ArgRepair.ar_rejected(Ar.Repaired{Ar.Out{c, to} <> os, List.append(&2, Ar.Record, r, xs)}) == True{} : Bool}, ih(hb))

def rr.cons(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, ss: List<&2, Ar.Seen>, +k: String, +m: Maybe<&2, String>, v: Ar.Val, st: Ar.Step, h: SV.sv.SVa(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{k, m, v}, st), rest: Ar.Verdict, b2: Bool, eb: {Bool.or(Maybe.is_some(&2, String, ArgSpec.first_text(ArgRepair.ar_cur(ArgSpec.decoding(ks, k, m), k), rs)), b2) == True{} : Bool}, ih: {b2 == True{} : Bool} -> {ArgRepair.ar_rejected(rest) == True{} : Bool}) -> {ArgRepair.ar_rejected(Ar.go.cons(st, rest)) == True{} : Bool}:
  match st:
    case Ar.StepNo{x}:
      {==}
    case Ar.StepOk{o, r, s}:
      match o:
        case Ar.Out{+c, to}:
          (hn, more) = h
          rr.end(c, to, r, s, rest, b2, ih, rr.or_l(Maybe.is_some(&2, String, ArgSpec.first_text(ArgRepair.ar_cur(ArgSpec.decoding(ks, k, m), k), rs)), b2, rr.head(ps, cl, als, rs, ks, k, m, c, hn), eb))

def rr.go(args: List<&2, Ar.Arg>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>, bad: {ArgRepair.ar_some_refused.go(rs, ks, args) == True{} : Bool}) -> {ArgRepair.ar_rejected(Ar.go(args, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss)) == True{} : Bool}:
  match args:
    case Nil{}:
      AB.ab.absurd({ArgRepair.ar_rejected(Ar.Repaired{Nil{}, Nil{}}) == True{} : Bool}, bad)
    case +a <> +t:
      match a:
        case Ar.Arg{+k, +m, +v}:
          +st = Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{k, m, v})
          rr.cons(ps, cl, als, rs, ks, ss, k, m, v, st, SV.sv.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{k, m, v}), Ar.go(t, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, Ar.seen.next(st, ss)), ArgRepair.ar_some_refused.go(rs, ks, t), bad, e => rr.go(t, ps, cl, als, rs, ks, Ar.seen.next(st, ss), e))

def rr.keys(+rs: List<&2, Ar.KV>, +args: List<&2, Ar.Arg>, bad: {ArgRepair.ar_some_refused.go(rs, ArgSpec.sent_keys(args), args) == True{} : Bool}) -> {ArgRepair.ar_some_refused.go(rs, Ar.keys(args), args) == True{} : Bool}:
  %Equal.sym(List<&2, String>, Ar.keys(args), ArgSpec.sent_keys(args), PSpec.rs.keys(args)) : {ArgRepair.ar_some_refused.go(rs, _, args) == True{} : Bool}
  bad

def ArgRepair.arg_repair_refused_rejects(sc, d, args, bad):
  match sc:
    case Ar.Schema{+ps, +cl}:
      match d:
        case Ar.Dialect{+als, +rs}:
          rr.go(args, ps, cl, als, rs, Ar.keys(args), Nil{}, rr.keys(rs, args, bad))
