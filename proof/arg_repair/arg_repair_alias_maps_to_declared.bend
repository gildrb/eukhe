# eukhe: the proof of LAW arg_repair_alias_maps_to_declared
#
# PROOF: in a well-formed dialect every alias's canonical name is declared
# (al.wf, by induction over the aliases); a repaired step's name satisfies
# the naming facts (sv.step), so an undeclared alias is read as its first
# canonical name (al.at); by induction over the arguments (al.go) as in
# arg_repair_never_renames.

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./base.bend as AB
import ./base/step.bend as SV
import ./base/look.bend as PSpec

def al.AO(ps: List<&2, Ar.Prop>, als: List<&2, Ar.KV>, ks: List<&2, String>, args: List<&2, Ar.Arg>, v: Ar.Verdict) -> Bool:
  match v:
    case Ar.Repaired{os, rs}:
      ArgRepair.ar_alias_ok.go(ps, als, ks, args, os)
    case Ar.Rejected{x}:
      True{}

def al.conv(-ps: List<&2, Ar.Prop>, -cl: Bool, -als: List<&2, Ar.KV>, -rs: List<&2, Ar.KV>, -args: List<&2, Ar.Arg>, v: Ar.Verdict) -> {al.AO(ps, als, ArgSpec.sent_keys(args), args, v) == ArgRepair.ar_alias_ok(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, args, v) : Bool}:
  match v:
    case Ar.Repaired{os, xs}:
      {==}
    case Ar.Rejected{x}:
      {==}

# an alias's canonical name, if any, is declared
def al.text(m: Maybe<&2, String>, ps: List<&2, Ar.Prop>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{a}:
      ArgSpec.is_some(ArgSpec.declared(a, ps))

def al.wf_at(b: Bool, -c: String, -r: Maybe<&2, String>, -ps: List<&2, Ar.Prop>, hc: {ArgSpec.is_some(ArgSpec.declared(c, ps)) == True{} : Bool}, hr: {al.text(r, ps) == True{} : Bool}) -> {al.text(Ar.pick.at(b, c, r), ps) == True{} : Bool}:
  match b:
    case True{}:
      hc
    case False{}:
      hr

# in a well-formed dialect, the first alias of k names a declared argument
def al.wf(+ps: List<&2, Ar.Prop>, +rs: List<&2, Ar.KV>, als: List<&2, Ar.KV>, +k: String, h: {ArgRepair.ar_wf.alias(ps, rs, als) == True{} : Bool}) -> {al.text(Ar.lookup(k, als), ps) == True{} : Bool}:
  match als:
    case Nil{}:
      {==}
    case +e <> +t:
      match e:
        case Ar.KV{+x, +c}:
          +hh = h
          +a1 = Bool.and(ArgSpec.is_some(ArgSpec.declared(c, ps)), Bool.not(Maybe.is_some(&2, String, ArgSpec.first_text(c, rs))))
          +hd = AB.ab.and_l(a1, ArgRepair.ar_wf.alias(ps, rs, t), hh)
          al.wf_at(String.eq(k, x), c, Ar.lookup(k, t), ps, AB.ab.and_l(ArgSpec.is_some(ArgSpec.declared(c, ps)), Bool.not(Maybe.is_some(&2, String, ArgSpec.first_text(c, rs))), hd), al.wf(ps, rs, t, k, AB.ab.and_r(a1, ArgRepair.ar_wf.alias(ps, rs, t), hh)))

def al.imp_and(x: Bool, -y: Bool, -z: Bool, hy: {ArgRepair.ar_implies(x, y) == True{} : Bool}, hz: {z == True{} : Bool}) -> {ArgRepair.ar_implies(x, Bool.and(y, z)) == True{} : Bool}:
  match x:
    case True{}:
      SV.sv.and2(y, z, hy, hz)
    case False{}:
      {==}

def al.at(ha: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, +cur: String, +c: String, hw: {al.text(ha, ps) == True{} : Bool}, hn: {SV.sv.nalias(ha, Ar.found(Ar.prop(cur, ps)), cur, c) == True{} : Bool}) -> {ArgRepair.ar_alias_ok.at(ha, ps, cur, c) == True{} : Bool}:
  match ha:
    case None{}:
      {==}
    case Some{+a}:
      %PSpec.rs.prop(cur, ps) : {ArgRepair.ar_implies(Bool.not(ArgSpec.is_some(_)), Bool.and(String.eq(c, a), ArgSpec.is_some(ArgSpec.declared(a, ps)))) == True{} : Bool}
      %PSpec.rs.found(Ar.prop(cur, ps)) : {ArgRepair.ar_implies(Bool.not(_), Bool.and(String.eq(c, a), ArgSpec.is_some(ArgSpec.declared(a, ps)))) == True{} : Bool}
      al.imp_and(Bool.not(Ar.found(Ar.prop(cur, ps))), String.eq(c, a), ArgSpec.is_some(ArgSpec.declared(a, ps)), hn, hw)

def al.arg(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, ss: List<&2, Ar.Seen>, a: Ar.Arg, o: Ar.Out, r: List<&2, Ar.Record>, s: Ar.Seen, wf: {ArgRepair.ar_wf.alias(ps, rs, als) == True{} : Bool}, h: SV.sv.SVa(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a, Ar.StepOk{o, r, s})) -> {ArgRepair.ar_alias_ok.arg(ps, als, ks, a, o) == True{} : Bool}:
  match a:
    case Ar.Arg{+k, +m, v}:
      match o:
        case Ar.Out{+c, to}:
          (hn, rest) = h
          +cur = ArgRepair.ar_cur(Ar.decoded(ks, k, m), k)
          %PSpec.rs.decoded(ks, k, m) : {ArgRepair.ar_alias_ok.at(ArgSpec.first_text(ArgRepair.ar_cur(_, k), als), ps, ArgRepair.ar_cur(_, k), c) == True{} : Bool}
          %PSpec.rs.lookup(cur, als) : {ArgRepair.ar_alias_ok.at(_, ps, cur, c) == True{} : Bool}
          al.at(Ar.lookup(cur, als), ps, cur, c, al.wf(ps, rs, als, cur, wf), SV.sv.nok_alias(Ar.lookup(cur, rs), Ar.lookup(cur, als), Ar.found(Ar.prop(cur, ps)), cl, cur, c, hn))

def al.cons(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, ss: List<&2, Ar.Seen>, a: Ar.Arg, t: List<&2, Ar.Arg>, st: Ar.Step, wf: {ArgRepair.ar_wf.alias(ps, rs, als) == True{} : Bool}, h: SV.sv.SVa(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a, st), rest: Ar.Verdict, ih: {al.AO(ps, als, ks, t, rest) == True{} : Bool}) -> {al.AO(ps, als, ks, a <> t, Ar.go.cons(st, rest)) == True{} : Bool}:
  match st:
    case Ar.StepNo{x}:
      {==}
    case Ar.StepOk{+o, +r, +s}:
      match rest:
        case Ar.Rejected{x}:
          {==}
        case Ar.Repaired{os, xs}:
          SV.sv.and2(ArgRepair.ar_alias_ok.arg(ps, als, ks, a, o), ArgRepair.ar_alias_ok.go(ps, als, ks, t, os), al.arg(ps, cl, als, rs, ks, ss, a, o, r, s, wf, h), ih)

def al.go(args: List<&2, Ar.Arg>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>, +wf: {ArgRepair.ar_wf.alias(ps, rs, als) == True{} : Bool}) -> {al.AO(ps, als, ks, args, Ar.go(args, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss)) == True{} : Bool}:
  match args:
    case Nil{}:
      {==}
    case +a <> +t:
      +st = Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a)
      al.cons(ps, cl, als, rs, ks, ss, a, t, st, wf, SV.sv.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a), Ar.go(t, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, Ar.seen.next(st, ss)), al.go(t, ps, cl, als, rs, ks, Ar.seen.next(st, ss), wf))

def ArgRepair.arg_repair_alias_maps_to_declared(sc, d, args, wf):
  match sc:
    case Ar.Schema{+ps, +cl}:
      match d:
        case Ar.Dialect{+als, +rs}:
          +v = Ar.go(args, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, Ar.keys(args), Nil{})
          %al.conv(ps, cl, als, rs, args, v) : {_ == True{} : Bool}
          %PSpec.rs.keys(args) : {al.AO(ps, als, _, args, v) == True{} : Bool}
          al.go(args, ps, cl, als, rs, Ar.keys(args), Nil{}, wf)
