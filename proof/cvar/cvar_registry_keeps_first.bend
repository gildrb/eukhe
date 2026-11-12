# eukhe: the proof of LAW cvar_registry_keeps_first
# The registry of pre keeps none of d's id (LW.wh.reg_no_id: a kept
# declaration is a good one of pre); declare then adds d last
# (LW.wh.declare_free); what follows comes after d (LW.wh.reg), so the
# lookup passes the kept ones and finds d (LW.wh.kf_fin).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ../../laws/cvar/whole.bend as CvarWhole
import ./base/whole.bend as LW

def CvarWhole.cvar_registry_keeps_first(pre, d, post, good, first):
  +x = Cvar.spec_id(d)
  +R = Cv.registry.go(pre, Nil{})
  +nr = LW.wh.reg_no_id(pre, Nil{}, x, {==}, first)
  +ed = LW.wh.declare_free(R, d, nr, good)
  Equal.trans(Maybe<&2, Cv.Decl>, Cv.find(Cv.registry.go(List.append(&2, Cv.Decl, pre, d <> post), Nil{}), x), Cv.find(Cv.registry.go(post, Cv.declare(R, d)), x), Some{d},
    Equal.cong(List<&2, Cv.Decl>, Maybe<&2, Cv.Decl>, z => Cv.find(z, x), Cv.registry.go(List.append(&2, Cv.Decl, pre, d <> post), Nil{}), Cv.registry.go(post, Cv.declare(R, d)), LW.wh.reg_app(pre, d <> post, Nil{})),
    Equal.trans(Maybe<&2, Cv.Decl>, Cv.find(Cv.registry.go(post, Cv.declare(R, d)), x), Cv.find(Cv.registry.go(post, List.append(&2, Cv.Decl, R, [d])), x), Some{d},
      Equal.cong(List<&2, Cv.Decl>, Maybe<&2, Cv.Decl>, z => Cv.find(Cv.registry.go(post, z), x), Cv.declare(R, d), List.append(&2, Cv.Decl, R, [d]), ed),
      LW.wh.kf_fin(R, d, post, x, {==}, nr, LW.wh.reg(post, List.append(&2, Cv.Decl, R, [d])))))
