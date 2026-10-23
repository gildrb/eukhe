# eukhe: the proof of LAW cvar_inherits

import Base
import ../../bend/cvar.bend as Cv
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pv.inh_m(m: Maybe<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat) -> {Cv.value.at(m, ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{Nil{}, Nil{}}]), x) == Cv.value.at(m, ds, cfg, fam, x) : Maybe<&2, Cv.Val>}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      +r = Cv.root.val(ds, cfg, x, d)
      Equal.cong(Cv.Val, Maybe<&2, Cv.Val>, y => Some{y}, Cv.chain(List.append(&2, Cv.Ag, fam, [Cv.Ag{Nil{}, Nil{}}]), ds, x, r), Cv.chain(fam, ds, x, r), LA.pv.chain_snoc(fam, Cv.Ag{Nil{}, Nil{}}, ds, x, r))

def pv.cvar_inherits(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{Nil{}, Nil{}}]), x) == Cv.value(ds, cfg, fam, x) : Maybe<&2, Cv.Val>}:
  pv.inh_m(Cv.find(ds, x), ds, cfg, fam, x)

def Laws.cvar_inherits(ds, cfg, fam, x):
  pv.cvar_inherits(ds, cfg, fam, x)
