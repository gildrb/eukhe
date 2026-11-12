# eukhe: the proof of LAW arg_repair_repairs
#
# PROOF: admitted arguments each repair taking their seen, no earlier one
# holding their name (AW.aw.build), so the walk over them repairs
# (AW.aw.rep); the code's sent keys are the spec's (rs.keys).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./base.bend as AB
import ./base/step.bend as SV
import ./base/look.bend as PSpec
import ./base/walk.bend as AW

def ArgRepair.arg_repair_repairs(sc, d, args, ok):
  match sc:
    case Ar.Schema{+ps, +cl}:
      match d:
        case Ar.Dialect{+als, +rs}:
          +ok2 = ok
          +ks = ArgSpec.sent_keys(args)
          +ra = ArgRepair.ar_alone_ok(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, args)
          +fr = ArgSpec.fresh(ArgSpec.names(ps, als, ks, args), Nil{})
          oks = AW.aw.build(args, ps, cl, als, rs, ks, Nil{}, Nil{}, {==}, AB.ab.and_l(ra, fr, ok2), AB.ab.and_r(ra, fr, ok2))
          %Equal.sym(List<&2, String>, Ar.keys(args), ks, PSpec.rs.keys(args)) : {ArgRepair.ar_rejected(Ar.go(args, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, _, Nil{})) == False{} : Bool}
          AW.aw.rep(args, ps, cl, als, rs, ks, Nil{}, oks)
