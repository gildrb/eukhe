# eukhe: the proof of LAW baseline_is_kept: row by row, the code's kept
# metric of a row is the spec's (AB.ah.kk); the first one found is a kept
# metric, and none found means none kept

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../spec/autoresearch/segment.bend as SG
import ../../laws/autoresearch/history.bend as AutoresearchHistory
import ./best_is_best/best.bend as AB

def bik.k(k: Maybe<&2, ArD.Dec>, b: Maybe<&2, ArD.Dec>, +r: ArS.Row, +t: List<&2, ArS.Row>, +seg: Nat, ek: {SG.kept(r, seg) == k : Maybe<&2, ArD.Dec>}, ih: AutoresearchHistory.ar_base_ok(b, t, seg)) -> AutoresearchHistory.ar_base_ok(ArS.first.at(k, b), r <> t, seg):
  match k:
    case None{}:
      match b:
        case None{}:
          %Equal.sym(Maybe<&2, ArD.Dec>, SG.kept(r, seg), None{}, ek) : {Bool.and(SG.none.at(_), SG.none_kept(t, seg)) == True{} : Bool}
          ih
        case Some{+x}:
          %Equal.sym(Maybe<&2, ArD.Dec>, SG.kept(r, seg), None{}, ek) : {Bool.or(SG.has.at(x, _), SG.has_kept(x, t, seg)) == True{} : Bool}
          ih
    case Some{+y}:
      %Equal.sym(Maybe<&2, ArD.Dec>, SG.kept(r, seg), Some{y}, ek) : {Bool.or(SG.has.at(y, _), SG.has_kept(y, t, seg)) == True{} : Bool}
      %Equal.sym(Bool, SG.dec_eq(y, y), True{}, AB.ah.dec_refl(y)) : {Bool.or(_, SG.has_kept(y, t, seg)) == True{} : Bool}
      {==}

def bik.go(rs: List<&2, ArS.Row>, +seg: Nat) -> AutoresearchHistory.ar_base_ok(ArS.first(rs, seg), rs, seg):
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      bik.k(ArS.kept(r, seg), ArS.first(t, seg), r, t, seg, AB.ah.kk(r, seg), bik.go(t, seg))

def AutoresearchHistory.baseline_is_kept(s):
  match s:
    case ArS.St{c, +seg, mode, runs, pend}:
      bik.go(runs, seg)
