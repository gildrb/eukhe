# eukhe: the proof of LAW arg_repair_outs
#
# PROOF: by induction over the arguments, the sent keys and the names
# taken generalized (ou.go): a refused step refuses the call; a repaired
# step's out (SV.sv.step) is named as S2 names its key read
# (AW.aw.name_n, AW.aw.kr) and holds its value read as that name's
# declared argument; the rest's outs by the hypothesis.

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./base.bend as AB
import ./base/step.bend as SV
import ./base/look.bend as PSpec
import ./base/walk.bend as AW

# the claim about a verdict, the sent keys ks given
def ou.OK(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +ks: List<&2, String>, +args: List<&2, Ar.Arg>, v: Ar.Verdict) -> Type:
  match v:
    case Ar.Repaired{os, rs}:
      {os == ArgRepair.ar_outs(ps, als, ks, args) : List<&2, Ar.Out>}
    case Ar.Rejected{x}:
      Unit

def ou.head(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, -ss: List<&2, Ar.Seen>, a: Ar.Arg, +t: List<&2, Ar.Arg>, o: Ar.Out, -r: List<&2, Ar.Record>, -s: Ar.Seen, +os: List<&2, Ar.Out>, h: SV.sv.SVa(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a, Ar.StepOk{o, r, s}), ih: {os == ArgRepair.ar_outs(ps, als, ks, t) : List<&2, Ar.Out>}) -> {o <> os == ArgRepair.ar_outs(ps, als, ks, a <> t) : List<&2, Ar.Out>}:
  match a:
    case Ar.Arg{+k, +m, +v}:
      match o:
        case Ar.Out{+c, +to}:
          (hn, rest) = h
          (ef, rest2) = rest
          (eto, rest3) = rest2
          +dm = Ar.decoded(ks, k, m)
          +cu = ArgRepair.ar_cur(dm, k)
          +kr = ArgSpec.key_read(ks, Ar.Arg{k, m, v})
          +nk = ArgSpec.name_of(ps, als, kr)
          +e0 = AW.aw.name_n(ps, cl, als, rs, cu, c, hn)
          +ec = Equal.trans(String, c, ArgSpec.name_of(ps, als, cu), nk, e0, Equal.cong(String, String, z => ArgSpec.name_of(ps, als, z), cu, kr, Equal.sym(String, kr, cu, AW.aw.kr(ks, k, m, v))))
          +tl = ArgRepair.ar_outs(ps, als, ks, t)
          %Equal.sym(List<&2, Ar.Out>, os, tl, ih) : {Ar.Out{c, to} <> _ == ArgRepair.ar_outs(ps, als, ks, Ar.Arg{k, m, v} <> t) : List<&2, Ar.Out>}
          %Equal.sym(Maybe<&2, Ar.To>, to, Ar.coerce(Ar.prop(c, ps), v), eto) : {Ar.Out{c, _} <> tl == ArgRepair.ar_outs(ps, als, ks, Ar.Arg{k, m, v} <> t) : List<&2, Ar.Out>}
          %Equal.sym(Maybe<&2, Ar.Prop>, Ar.prop(c, ps), ArgSpec.declared(c, ps), PSpec.rs.prop(c, ps)) : {Ar.Out{c, Ar.coerce(_, v)} <> tl == ArgRepair.ar_outs(ps, als, ks, Ar.Arg{k, m, v} <> t) : List<&2, Ar.Out>}
          Equal.cong(String, List<&2, Ar.Out>, z => Ar.Out{z, Ar.coerce(ArgSpec.declared(z, ps), v)} <> tl, c, nk, ec)

def ou.cons(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, ss: List<&2, Ar.Seen>, +a: Ar.Arg, +t: List<&2, Ar.Arg>, st: Ar.Step, h: SV.sv.SVa(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a, st), rest: Ar.Verdict, ih: ou.OK(ps, als, ks, t, rest)) -> ou.OK(ps, als, ks, a <> t, Ar.go.cons(st, rest)):
  match st:
    case Ar.StepNo{x}:
      Unit{}
    case Ar.StepOk{+o, +r, +s}:
      match rest:
        case Ar.Rejected{x}:
          Unit{}
        case Ar.Repaired{+os, xs}:
          ou.head(ps, cl, als, rs, ks, ss, a, t, o, r, s, os, h, ih)

def ou.go(args: List<&2, Ar.Arg>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>) -> ou.OK(ps, als, ks, args, Ar.go(args, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss)):
  match args:
    case Nil{}:
      {==}
    case +a <> +t:
      +st = Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a)
      ou.cons(ps, cl, als, rs, ks, ss, a, t, st, SV.sv.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a), Ar.go(t, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, Ar.seen.next(st, ss)), ou.go(t, ps, cl, als, rs, ks, Ar.seen.next(st, ss)))

def ArgRepair.arg_repair_outs(ps, cl, als, rs, args, os, recs, ok):
  %ok : ou.OK(ps, als, ArgSpec.sent_keys(args), args, _)
  %PSpec.rs.keys(args) : ou.OK(ps, als, _, args, Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, args))
  ou.go(args, ps, cl, als, rs, Ar.keys(args), Nil{})
