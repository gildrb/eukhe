# eukhe: the proof of LAW arg_repair_first_refusal
#
# PROOF: the admitted arguments before it each repair taking their seen
# (AW.aw.build); the argument refused alone is refused by its key read's
# name whatever the names taken (AW.aw.no_step), so its step refuses the
# rest (AW.aw.no_go) and the walk over the admitted ones refuses just so
# (AW.aw.rej).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./base.bend as AB
import ./base/step.bend as SV
import ./base/look.bend as PSpec
import ./base/walk.bend as AW

def ArgRepair.arg_repair_first_refusal(sc, d, pre, a, post, x, ok, no):
  match sc:
    case Ar.Schema{+ps, +cl}:
      match d:
        case Ar.Dialect{+als, +rs}:
          +ok2 = ok
          +l = List.append(&2, Ar.Arg, pre, a <> post)
          +ks = ArgSpec.sent_keys(l)
          +ra = ArgRepair.ar_alone_ok(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, pre)
          +fr = ArgSpec.fresh(ArgSpec.names(ps, als, ks, pre), Nil{})
          oks = AW.aw.build(pre, ps, cl, als, rs, ks, Nil{}, Nil{}, {==}, AB.ab.and_l(ra, fr, ok2), AB.ab.and_r(ra, fr, ok2))
          +ss = AW.aw.after(ps, als, ks, pre, Nil{})
          +st = Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a)
          +hr = AW.aw.no_go(st, Ar.go(post, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, Ar.seen.next(st, ss)), x, AW.aw.no_step(ps, cl, als, rs, ks, ss, a, x, no))
          %Equal.sym(List<&2, String>, Ar.keys(l), ks, PSpec.rs.keys(l)) : {Ar.go(l, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, _, Nil{}) == Ar.Rejected{x} : Ar.Verdict}
          AW.aw.rej(pre, ps, cl, als, rs, ks, Nil{}, a <> post, x, oks, hr)
