# eukhe: lemmas of LAW best_is_best (prefix ah.): rows in order (each kept
# metric better than every earlier one) have their last kept metric as the
# segment's best of the spec (SG.Best): it is kept (dec_eq is reflexive),
# and no kept metric is better: not an earlier one (metric_order_reverse),
# not itself (metric_order_self).

import Base
import ../../../bend/autoresearch/dec.bend as ArD
import ../../../bend/autoresearch/state.bend as ArS
import ../../../spec/autoresearch/segment.bend as SG
import ../../../laws/autoresearch/model.bend as Autoresearch
import ../base/history.bend as AH
import ./order.bend as AO
import ../metric_order_reverse.bend as PMetricOrderReverse
import ../metric_order_self.bend as PMetricOrderSelf

# The spec's kept metric is the code's
# ------------------------------------

def ah.kst(b: Bool, st: Maybe<&2, ArS.Status>, -m: Maybe<&2, ArD.Dec>) -> {SG.kept.st(b, st, m) == ArS.kept.of(Bool.and(b, Bool.and(ArS.kept.st(st), True{})), m) : Maybe<&2, ArD.Dec>}:
  match b:
    case True{}:
      match st:
        case None{}:
          {==}
        case Some{k}:
          match k:
            case ArS.Keep{}:
              {==}
            case ArS.Discard{}:
              {==}
            case ArS.Crash{}:
              {==}
            case ArS.Checks{}:
              {==}
    case False{}:
      {==}

def ah.kk(r: ArS.Row, +seg: Nat) -> {SG.kept(r, seg) == ArS.kept(r, seg) : Maybe<&2, ArD.Dec>}:
  match r:
    case ArS.Row{i, sg, +st, m, ms, ps, fn, fl, desc}:
      match fl:
        case True{}:
          Equal.sym(Maybe<&2, ArD.Dec>, ArS.kept.of(Bool.and(Nat.is_eq(sg, seg), Bool.and(ArS.kept.st(st), False{})), m), None{}, AO.ah.kof2(Nat.is_eq(sg, seg), ArS.kept.st(st), m))
        case False{}:
          ah.kst(Nat.is_eq(sg, seg), st, m)

# Decimal facts
# -------------

def ah.ds_refl(ds: List<&2, Nat>) -> {SG.ds_eq(ds, ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case x <> u:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, AH.ah.eq_refl(x)) : {Bool.and(_, SG.ds_eq(u, u)) == True{} : Bool}
      ah.ds_refl(u)

def ah.dec_refl(a: ArD.Dec) -> {SG.dec_eq(a, a) == True{} : Bool}:
  match a:
    case ArD.Dec{n, +ds, +s}:
      match n:
        case True{}:
          AH.ah.and_i(SG.ds_eq(ds, ds), Nat.is_eq(s, s), ah.ds_refl(ds), AH.ah.eq_refl(s))
        case False{}:
          AH.ah.and_i(SG.ds_eq(ds, ds), Nat.is_eq(s, s), ah.ds_refl(ds), AH.ah.eq_refl(s))

def ah.lt_flip(c: Cmp, h: {Cmp.is_lt(c) == True{} : Bool}) -> {Bool.not(Cmp.is_lt(Autoresearch.ar_flip(c))) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      AH.ah.absurd({Bool.not(Cmp.is_lt(Autoresearch.ar_flip(EQ{}))) == True{} : Bool}, h)
    case GT{}:
      AH.ah.absurd({Bool.not(Cmp.is_lt(Autoresearch.ar_flip(GT{}))) == True{} : Bool}, h)

def ah.gt_flip(c: Cmp, h: {Cmp.is_gt(c) == True{} : Bool}) -> {Bool.not(Cmp.is_gt(Autoresearch.ar_flip(c))) == True{} : Bool}:
  match c:
    case LT{}:
      AH.ah.absurd({Bool.not(Cmp.is_gt(Autoresearch.ar_flip(LT{}))) == True{} : Bool}, h)
    case EQ{}:
      AH.ah.absurd({Bool.not(Cmp.is_gt(Autoresearch.ar_flip(EQ{}))) == True{} : Bool}, h)
    case GT{}:
      {==}

# a metric better than y: y is not better than it
def ah.anti(d: ArS.Dir, +x: ArD.Dec, +y: ArD.Dec, h: {ArS.better(d, x, y) == True{} : Bool}) -> {Bool.not(SG.is_better(~ArD.Dec.cmp, d, y, x)) == True{} : Bool}:
  match d:
    case ArS.Lower{}:
      %Equal.sym(Cmp, ArD.Dec.cmp(y, x), Autoresearch.ar_flip(ArD.Dec.cmp(x, y)), Autoresearch.metric_order_reverse(x, y)) : {Bool.not(Cmp.is_lt(_)) == True{} : Bool}
      ah.lt_flip(ArD.Dec.cmp(x, y), h)
    case ArS.Higher{}:
      %Equal.sym(Cmp, ArD.Dec.cmp(y, x), Autoresearch.ar_flip(ArD.Dec.cmp(x, y)), Autoresearch.metric_order_reverse(x, y)) : {Bool.not(Cmp.is_gt(_)) == True{} : Bool}
      ah.gt_flip(ArD.Dec.cmp(x, y), h)

# no metric is better than itself
def ah.self(d: ArS.Dir, +y: ArD.Dec) -> {Bool.not(SG.is_better(~ArD.Dec.cmp, d, y, y)) == True{} : Bool}:
  match d:
    case ArS.Lower{}:
      %Equal.sym(Cmp, ArD.Dec.cmp(y, y), EQ{}, Autoresearch.metric_order_self(y)) : {Bool.not(Cmp.is_lt(_)) == True{} : Bool}
      {==}
    case ArS.Higher{}:
      %Equal.sym(Cmp, ArD.Dec.cmp(y, y), EQ{}, Autoresearch.metric_order_self(y)) : {Bool.not(Cmp.is_gt(_)) == True{} : Bool}
      {==}

def ah.or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# The last kept metric
# --------------------

def ah.bt_at(+d: ArS.Dir, +y: ArD.Dec, -k1: Maybe<&2, ArD.Dec>, k2: Maybe<&2, ArD.Dec>, h1: {AO.ah.bt(d, y, k1) == True{} : Bool}, h2: {AO.ah.bt(d, y, k2) == True{} : Bool}) -> {AO.ah.bt(d, y, ArS.last.at(k1, k2)) == True{} : Bool}:
  match k2:
    case None{}:
      h1
    case Some{z}:
      h2

# every kept metric better than y: so the last
def ah.allb_last(+d: ArS.Dir, +y: ArD.Dec, rs: List<&2, ArS.Row>, +seg: Nat, +h: {AO.ah.allb(d, y, rs, seg) == True{} : Bool}) -> {AO.ah.bt(d, y, ArS.last(rs, seg)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      ah.bt_at(d, y, ArS.kept(r, seg), ArS.last(t, seg), AH.ah.and_l(AO.ah.bt(d, y, ArS.kept(r, seg)), AO.ah.allb(d, y, t, seg), h), ah.allb_last(d, y, t, seg, AH.ah.and_r(AO.ah.bt(d, y, ArS.kept(r, seg)), AO.ah.allb(d, y, t, seg), h)))

def ah.u1(+d: ArS.Dir, +x: ArD.Dec, +y: ArD.Dec, +t: List<&2, ArS.Row>, +seg: Nat, ha: {AO.ah.allb(d, y, t, seg) == True{} : Bool}, hl: {ArS.last(t, seg) == Some{x} : Maybe<&2, ArD.Dec>}) -> {ArS.better(d, x, y) == True{} : Bool}:
  %hl : {AO.ah.bt(d, y, _) == True{} : Bool}
  ah.allb_last(d, y, t, seg, ha)

# an earlier kept metric is not better than the last one
def ah.u(+d: ArS.Dir, +x: ArD.Dec, k: Maybe<&2, ArD.Dec>, +t: List<&2, ArS.Row>, +seg: Nat, ha: {AO.ah.above(d, k, t, seg) == True{} : Bool}, hl: {ArS.last(t, seg) == Some{x} : Maybe<&2, ArD.Dec>}) -> {SG.unbeaten.at(~ArD.Dec.cmp, d, x, k) == True{} : Bool}:
  match k:
    case None{}:
      {==}
    case Some{+y}:
      ah.anti(d, x, y, ah.u1(d, x, y, t, seg, ha, hl))

def ah.u2(+d: ArS.Dir, +x: ArD.Dec, +r: ArS.Row, +t: List<&2, ArS.Row>, +seg: Nat, +k: Maybe<&2, ArD.Dec>, eq: {ArS.kept(r, seg) == k : Maybe<&2, ArD.Dec>}, ha: {AO.ah.above(d, k, t, seg) == True{} : Bool}, hl: {ArS.last(t, seg) == Some{x} : Maybe<&2, ArD.Dec>}) -> {SG.unbeaten.at(~ArD.Dec.cmp, d, x, SG.kept(r, seg)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, ArD.Dec>, SG.kept(r, seg), k, Equal.trans(Maybe<&2, ArD.Dec>, SG.kept(r, seg), ArS.kept(r, seg), k, ah.kk(r, seg), eq)) : {SG.unbeaten.at(~ArD.Dec.cmp, d, x, _) == True{} : Bool}
  ah.u(d, x, k, t, seg, ha, hl)

def ah.nb_at(+d: ArS.Dir, +y: ArD.Dec, k: Maybe<&2, ArD.Dec>, h: {SG.none.at(k) == True{} : Bool}) -> {SG.unbeaten.at(~ArD.Dec.cmp, d, y, k) == True{} : Bool}:
  match k:
    case None{}:
      {==}
    case Some{z}:
      AH.ah.absurd({SG.unbeaten.at(~ArD.Dec.cmp, d, y, Some{z}) == True{} : Bool}, h)

# nothing kept: nothing better
def ah.nb_nk(+d: ArS.Dir, +y: ArD.Dec, rs: List<&2, ArS.Row>, +seg: Nat, +h: {SG.none_kept(rs, seg) == True{} : Bool}) -> {SG.none_better(~ArD.Dec.cmp, d, y, rs, seg) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      AH.ah.and_i(SG.unbeaten.at(~ArD.Dec.cmp, d, y, SG.kept(r, seg)), SG.none_better(~ArD.Dec.cmp, d, y, t, seg), ah.nb_at(d, y, SG.kept(r, seg), AH.ah.and_l(SG.none.at(SG.kept(r, seg)), SG.none_kept(t, seg), h)), ah.nb_nk(d, y, t, seg, AH.ah.and_r(SG.none.at(SG.kept(r, seg)), SG.none_kept(t, seg), h)))

# The best
# --------

def ah.best_cons(+d: ArS.Dir, +r: ArS.Row, +t: List<&2, ArS.Row>, +seg: Nat, k2: Maybe<&2, ArD.Dec>, k1: Maybe<&2, ArD.Dec>, +eq2: {ArS.last(t, seg) == k2 : Maybe<&2, ArD.Dec>}, +eq1: {ArS.kept(r, seg) == k1 : Maybe<&2, ArD.Dec>}, ih: SG.Best(~ArD.Dec.cmp, d, k2, t, seg), ha: {AO.ah.above(d, k1, t, seg) == True{} : Bool}) -> SG.Best(~ArD.Dec.cmp, d, ArS.last.at(k1, k2), r <> t, seg):
  match k2:
    case Some{+x}:
      (ihh, ihn) = ih
      (Equal.trans(Bool, Bool.or(SG.has.at(x, SG.kept(r, seg)), SG.has_kept(x, t, seg)), Bool.or(SG.has.at(x, SG.kept(r, seg)), True{}), True{}, Equal.cong(Bool, Bool, v => Bool.or(SG.has.at(x, SG.kept(r, seg)), v), SG.has_kept(x, t, seg), True{}, ihh), ah.or_true(SG.has.at(x, SG.kept(r, seg)))), AH.ah.and_i(SG.unbeaten.at(~ArD.Dec.cmp, d, x, SG.kept(r, seg)), SG.none_better(~ArD.Dec.cmp, d, x, t, seg), ah.u2(d, x, r, t, seg, k1, eq1, ha, eq2), ihn))
    case None{}:
      match k1:
        case None{}:
          %Equal.sym(Maybe<&2, ArD.Dec>, SG.kept(r, seg), None{}, Equal.trans(Maybe<&2, ArD.Dec>, SG.kept(r, seg), ArS.kept(r, seg), None{}, ah.kk(r, seg), eq1)) : {Bool.and(SG.none.at(_), SG.none_kept(t, seg)) == True{} : Bool}
          ih
        case Some{+y}:
          %Equal.sym(Maybe<&2, ArD.Dec>, SG.kept(r, seg), Some{y}, Equal.trans(Maybe<&2, ArD.Dec>, SG.kept(r, seg), ArS.kept(r, seg), Some{y}, ah.kk(r, seg), eq1)) : ({Bool.or(SG.has.at(y, _), SG.has_kept(y, t, seg)) == True{} : Bool} & {Bool.and(SG.unbeaten.at(~ArD.Dec.cmp, d, y, _), SG.none_better(~ArD.Dec.cmp, d, y, t, seg)) == True{} : Bool})
          (Equal.cong(Bool, Bool, v => Bool.or(v, SG.has_kept(y, t, seg)), SG.dec_eq(y, y), True{}, ah.dec_refl(y)), AH.ah.and_i(Bool.not(SG.is_better(~ArD.Dec.cmp, d, y, y)), SG.none_better(~ArD.Dec.cmp, d, y, t, seg), ah.self(d, y), ah.nb_nk(d, y, t, seg, ih)))

# rows in order: their last kept metric is the best
def ah.best(+d: ArS.Dir, rs: List<&2, ArS.Row>, +seg: Nat, +h: {AO.ah.ord(d, rs, seg) == True{} : Bool}) -> SG.Best(~ArD.Dec.cmp, d, ArS.last(rs, seg), rs, seg):
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      ah.best_cons(d, r, t, seg, ArS.last(t, seg), ArS.kept(r, seg), {==}, {==}, ah.best(d, t, seg, AH.ah.and_r(AO.ah.above(d, ArS.kept(r, seg), t, seg), AO.ah.ord(d, t, seg), h)), AH.ah.and_l(AO.ah.above(d, ArS.kept(r, seg), t, seg), AO.ah.ord(d, t, seg), h))
