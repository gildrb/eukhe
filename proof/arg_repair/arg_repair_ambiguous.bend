# eukhe: the proof of LAW arg_repair_ambiguous
#
# PROOF: the admitted arguments pre, b, mid each repair taking their seen
# (AW.aw.build); the names are fresh, so no argument of mid is read as b's
# name (AW.aw.fresh_mid), and the names taken find b's key for it
# (AW.aw.after_app, AW.aw.first_after); a, repaired alone and read as that
# name (am.n), refuses as ambiguous, and the walk over the admitted ones
# refuses just so (AW.aw.rej).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./base.bend as AB
import ./base/step.bend as SV
import ./base/look.bend as PSpec
import ./base/walk.bend as AW

def am.amb(c: String, f: String, k: String) -> Ar.Refusal:
  Ar.Ambiguous{c, f, k}

# the key read k, repaired alone, its name nm taken by the key j
def am.n(n: Ar.Named, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ss: List<&2, Ar.Seen>, +r0: List<&2, Ar.Record>, +k: String, +v: Ar.Val, +j: String, hn: {SV.sv.nok(Ar.lookup(k, rs), Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, k, n) == True{} : Bool}, h1: {Bool.not(ArgRepair.ar_rejected(Ar.go.cons(Ar.step.named(n, ps, Nil{}, Nil{}, k, v), Ar.Repaired{Nil{}, Nil{}}))) == True{} : Bool}, hf: {Ar.first_of(ArgSpec.name_of(ps, als, k), ss) == Some{j} : Maybe<&2, String>}) -> {Ar.step.named(n, ps, ss, r0, k, v) == Ar.StepNo{Ar.Ambiguous{ArgSpec.name_of(ps, als, k), j, k}} : Ar.Step}:
  match n:
    case Ar.NRefused{y, x}:
      AB.ab.absurd({Ar.step.named(Ar.NRefused{y, x}, ps, ss, r0, k, v) == Ar.StepNo{Ar.Ambiguous{ArgSpec.name_of(ps, als, k), j, k}} : Ar.Step}, h1)
    case Ar.NUnknown{y, ns}:
      AB.ab.absurd({Ar.step.named(Ar.NUnknown{y, ns}, ps, ss, r0, k, v) == Ar.StepNo{Ar.Ambiguous{ArgSpec.name_of(ps, als, k), j, k}} : Ar.Step}, h1)
    case Ar.NAs{+c}:
      +nm = ArgSpec.name_of(ps, als, k)
      +ec = AW.aw.name_n(ps, cl, als, rs, k, c, hn)
      %Equal.sym(String, c, nm, ec) : {Ar.step.first(Ar.first_of(_, ss), _, ps, r0, k, v) == Ar.StepNo{Ar.Ambiguous{nm, j, k}} : Ar.Step}
      %Equal.sym(Maybe<&2, String>, Ar.first_of(nm, ss), Some{j}, hf) : {Ar.step.first(_, nm, ps, r0, k, v) == Ar.StepNo{Ar.Ambiguous{nm, j, k}} : Ar.Step}
      {==}

def am.dm(dm: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ss: List<&2, Ar.Seen>, +k: String, +v: Ar.Val, +j: String, h1: {Bool.not(ArgRepair.ar_rejected(Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, [Ar.Arg{ArgRepair.ar_cur(dm, k), None{}, v}]))) == True{} : Bool}, hf: {Ar.first_of(ArgSpec.name_of(ps, als, ArgRepair.ar_cur(dm, k)), ss) == Some{j} : Maybe<&2, String>}) -> {Ar.step.read(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ss, k, dm, v) == Ar.StepNo{Ar.Ambiguous{ArgSpec.name_of(ps, als, ArgRepair.ar_cur(dm, k)), j, ArgRepair.ar_cur(dm, k)}} : Ar.Step}:
  match dm:
    case None{}:
      am.n(Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k), ps, cl, als, rs, ss, Nil{}, k, v, j, SV.sv.named(ps, cl, als, rs, k), h1, hf)
    case Some{+p}:
      am.n(Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, p), ps, cl, als, rs, ss, [Ar.RAlias{k, p}], p, v, j, SV.sv.named(ps, cl, als, rs, p), h1, hf)

# the argument a, repaired alone, its name taken by the key j
def am.step(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>, a: Ar.Arg, +j: String, h1: {Bool.not(ArgRepair.ar_rejected(ArgRepair.ar_alone(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, a))) == True{} : Bool}, hf: {Ar.first_of(ArgSpec.name_of(ps, als, ArgSpec.key_read(ks, a)), ss) == Some{j} : Maybe<&2, String>}) -> {Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a) == Ar.StepNo{Ar.Ambiguous{ArgSpec.name_of(ps, als, ArgSpec.key_read(ks, a)), j, ArgSpec.key_read(ks, a)}} : Ar.Step}:
  match a:
    case Ar.Arg{+k, +m, +v}:
      +dm = Ar.decoded(ks, k, m)
      +kr = ArgSpec.key_read(ks, Ar.Arg{k, m, v})
      +cu = ArgRepair.ar_cur(dm, k)
      +ek = Equal.sym(String, kr, cu, AW.aw.kr(ks, k, m, v))
      +h1c = Equal.trans(Bool, Bool.not(ArgRepair.ar_rejected(Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, [Ar.Arg{cu, None{}, v}]))), Bool.not(ArgRepair.ar_rejected(Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, [Ar.Arg{kr, None{}, v}]))), True{}, Equal.cong(String, Bool, z => Bool.not(ArgRepair.ar_rejected(Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, [Ar.Arg{z, None{}, v}]))), cu, kr, ek), h1)
      +hfc = Equal.trans(Maybe<&2, String>, Ar.first_of(ArgSpec.name_of(ps, als, cu), ss), Ar.first_of(ArgSpec.name_of(ps, als, kr), ss), Some{j}, Equal.cong(String, Maybe<&2, String>, z => Ar.first_of(ArgSpec.name_of(ps, als, z), ss), cu, kr, ek), hf)
      %ek : {Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{k, m, v}) == Ar.StepNo{Ar.Ambiguous{ArgSpec.name_of(ps, als, _), j, _}} : Ar.Step}
      am.dm(dm, ps, cl, als, rs, ss, k, v, j, h1c, hfc)

# the names taken after pre, b, mid find b's key for b's name
def am.first(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +ks: List<&2, String>, +pre: List<&2, Ar.Arg>, +b: Ar.Arg, +mid: List<&2, Ar.Arg>, +nm: String, eb: {nm == ArgSpec.name_of(ps, als, ArgSpec.key_read(ks, b)) : String}, hm: {ArgSpec.member(nm, ArgSpec.names(ps, als, ks, mid)) == False{} : Bool}) -> {Ar.first_of(nm, AW.aw.after(ps, als, ks, List.append(&2, Ar.Arg, pre, b <> mid), Nil{})) == Some{ArgSpec.key_read(ks, b)} : Maybe<&2, String>}:
  +y = AW.aw.after(ps, als, ks, pre, Nil{})
  +nb = ArgSpec.name_of(ps, als, ArgSpec.key_read(ks, b))
  +e1 = Equal.cong(List<&2, Ar.Seen>, Maybe<&2, String>, z => Ar.first_of(nm, z), AW.aw.after(ps, als, ks, List.append(&2, Ar.Arg, pre, b <> mid), Nil{}), AW.aw.after(ps, als, ks, mid, AW.aw.seen(ps, als, ks, b) <> y), AW.aw.after_app(ps, als, ks, pre, b <> mid, Nil{}))
  +e2 = AW.aw.first_after(ps, als, ks, nm, mid, AW.aw.seen(ps, als, ks, b) <> y, hm)
  %Equal.sym(Maybe<&2, String>, Ar.first_of(nm, AW.aw.after(ps, als, ks, List.append(&2, Ar.Arg, pre, b <> mid), Nil{})), Ar.first_of(nm, AW.aw.seen(ps, als, ks, b) <> y), Equal.trans(Maybe<&2, String>, Ar.first_of(nm, AW.aw.after(ps, als, ks, List.append(&2, Ar.Arg, pre, b <> mid), Nil{})), Ar.first_of(nm, AW.aw.after(ps, als, ks, mid, AW.aw.seen(ps, als, ks, b) <> y)), Ar.first_of(nm, AW.aw.seen(ps, als, ks, b) <> y), e1, e2)) : {_ == Some{ArgSpec.key_read(ks, b)} : Maybe<&2, String>}
  %Equal.sym(String, nm, nb, eb) : {Ar.pick.at(String.eq(_, nb), ArgSpec.key_read(ks, b), Ar.first_of(_, y)) == Some{ArgSpec.key_read(ks, b)} : Maybe<&2, String>}
  %Equal.sym(Bool, String.eq(nb, nb), True{}, AB.ab.str_refl(nb)) : {Ar.pick.at(_, ArgSpec.key_read(ks, b), Ar.first_of(nb, y)) == Some{ArgSpec.key_read(ks, b)} : Maybe<&2, String>}
  {==}

def ArgRepair.arg_repair_ambiguous(ps, cl, als, rs, pre, b, mid, a, post, ok, oa, same):
  +ok2 = ok
  +l = ArgRepair.ar_cat(pre, b, mid, a, post)
  +ks = ArgSpec.sent_keys(l)
  +xs = List.append(&2, Ar.Arg, pre, b <> mid)
  +ra = ArgRepair.ar_alone_ok(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, xs)
  +fr = ArgSpec.fresh(ArgSpec.names(ps, als, ks, xs), Nil{})
  oks = AW.aw.build(xs, ps, cl, als, rs, ks, Nil{}, Nil{}, {==}, AB.ab.and_l(ra, fr, ok2), AB.ab.and_r(ra, fr, ok2))
  +na = ArgSpec.name_of(ps, als, ArgSpec.key_read(ks, a))
  +nb = ArgSpec.name_of(ps, als, ArgSpec.key_read(ks, b))
  +eab = Equal.cong(List<&2, String>, String, z => AW.aw.head(z), ArgSpec.names(ps, als, ks, [a]), ArgSpec.names(ps, als, ks, [b]), same)
  +nsp = ArgSpec.names(ps, als, ks, pre)
  +nsm = ArgSpec.names(ps, als, ks, mid)
  +hf2 = Equal.trans(Bool, ArgSpec.fresh(List.append(&2, String, nsp, nb <> nsm), Nil{}), fr, True{}, Equal.cong(List<&2, String>, Bool, z => ArgSpec.fresh(z, Nil{}), List.append(&2, String, nsp, nb <> nsm), ArgSpec.names(ps, als, ks, xs), Equal.sym(List<&2, String>, ArgSpec.names(ps, als, ks, xs), List.append(&2, String, nsp, nb <> nsm), AW.aw.names_app(ps, als, ks, pre, b <> mid))), AB.ab.and_r(ra, fr, ok2))
  +hmb = AW.aw.fresh_mid(nsp, Nil{}, nb, nsm, hf2)
  +hma = Equal.trans(Bool, ArgSpec.member(na, nsm), ArgSpec.member(nb, nsm), False{}, Equal.cong(String, Bool, z => ArgSpec.member(z, nsm), na, nb, eab), hmb)
  +ss = AW.aw.after(ps, als, ks, xs, Nil{})
  +hf = am.first(ps, als, ks, pre, b, mid, na, eab, hma)
  +h1 = AB.ab.and_l(Bool.not(ArgRepair.ar_rejected(ArgRepair.ar_alone(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, a))), True{}, oa)
  +x = am.amb(na, ArgSpec.key_read(ks, b), ArgSpec.key_read(ks, a))
  +st = Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a)
  +hr = AW.aw.no_go(st, Ar.go(post, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, Ar.seen.next(st, ss)), x, am.step(ps, cl, als, rs, ks, ss, a, ArgSpec.key_read(ks, b), h1, hf))
  %Equal.sym(List<&2, String>, Ar.keys(l), ks, PSpec.rs.keys(l)) : {Ar.go(l, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, _, Nil{}) == Ar.Rejected{x} : Ar.Verdict}
  AW.aw.rej(xs, ps, cl, als, rs, ks, Nil{}, a <> post, x, oks, hr)
