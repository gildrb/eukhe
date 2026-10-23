# eukhe: the proof of LAW cvar_persist_roundtrip

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# a set that hits a persisted cvar is written
def pv.out_hit(+s: Cv.Bind, +ds: List<&2, Cv.Decl>, +x: Nat, keeps: {Cv.flag.at(Cv.find(ds, x), Cv.Persist{}) == True{} : Bool}, +h: {Cv.hit.at([s], ds, Cv.Agent{}, x) == True{} : Bool}) -> {Cv.out.at([s], ds, Cv.Persist{}) == True{} : Bool}:
  +ex = LA.pv.eq_true(Cv.Bind.id(s), x, LA.cvar.pv.and_l(Nat.is_eq(Cv.Bind.id(s), x), Cv.valid(ds, Cv.Agent{}, s), h))
  +hv = LA.cvar.pv.and_r(Nat.is_eq(Cv.Bind.id(s), x), Cv.valid(ds, Cv.Agent{}, s), h)
  %Equal.sym(Nat, Cv.Bind.id(s), x, ex) : {Bool.and(Cv.flag.at(Cv.find(ds, _), Cv.Persist{}), Cv.valid(ds, Cv.Agent{}, s)) == True{} : Bool}
  LA.pv.and_t(Cv.flag.at(Cv.find(ds, x), Cv.Persist{}), Cv.valid(ds, Cv.Agent{}, s), keeps, hv)

# a set that is not written misses a persisted cvar
def pv.out_miss(b: Bool, +s: Cv.Bind, +ds: List<&2, Cv.Decl>, +x: Nat, keeps: {Cv.flag.at(Cv.find(ds, x), Cv.Persist{}) == True{} : Bool}, eb: {Cv.hit.at([s], ds, Cv.Agent{}, x) == b : Bool}, ho: {Cv.out.at([s], ds, Cv.Persist{}) == False{} : Bool}) -> {Cv.hit.at([s], ds, Cv.Agent{}, x) == False{} : Bool}:
  match b:
    case True{}:
      LLogicLogic.cvar.pv.absurd({Cv.hit.at([s], ds, Cv.Agent{}, x) == False{} : Bool}, Equal.trans(Bool, True{}, Cv.out.at([s], ds, Cv.Persist{}), False{}, Equal.sym(Bool, Cv.out.at([s], ds, Cv.Persist{}), True{}, pv.out_hit(s, ds, x, keeps, eb)), ho))
    case False{}:
      eb

# the written sets give every persisted cvar the value of all sets
def pv.persist_go(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +x: Nat, +keeps: {Cv.flag.at(Cv.find(ds, x), Cv.Persist{}) == True{} : Bool}, +cur: Maybe<&2, Cv.Val>, ho: Bool, eho: {Cv.out.at(ss, ds, Cv.Persist{}) == ho : Bool}) -> {Cv.layer(Cv.written.go(ss, ds, Cv.Persist{}, ho), ds, Cv.Agent{}, x, cur) == Cv.layer(ss, ds, Cv.Agent{}, x, cur) : Maybe<&2, Cv.Val>}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      match ho:
        case True{}:
          +w = Cv.written.go(rest, ds, Cv.Persist{}, Cv.out.at(rest, ds, Cv.Persist{}))
          +c1 = Cv.layer([s], ds, Cv.Agent{}, x, cur)
          %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> rest, ds, Cv.Agent{}, x, cur), Cv.layer(rest, ds, Cv.Agent{}, x, c1), LA.pv.layer_cons(s, rest, ds, Cv.Agent{}, x, cur)) : {Cv.layer(s <> w, ds, Cv.Agent{}, x, cur) == _ : Maybe<&2, Cv.Val>}
          %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> w, ds, Cv.Agent{}, x, cur), Cv.layer(w, ds, Cv.Agent{}, x, c1), LA.pv.layer_cons(s, w, ds, Cv.Agent{}, x, cur)) : {_ == Cv.layer(rest, ds, Cv.Agent{}, x, c1) : Maybe<&2, Cv.Val>}
          pv.persist_go(rest, ds, x, keeps, c1, Cv.out.at(rest, ds, Cv.Persist{}), {==})
        case False{}:
          +w = Cv.written.go(rest, ds, Cv.Persist{}, Cv.out.at(rest, ds, Cv.Persist{}))
          +c1 = Cv.layer([s], ds, Cv.Agent{}, x, cur)
          +miss = pv.out_miss(Cv.hit.at([s], ds, Cv.Agent{}, x), s, ds, x, keeps, {==}, eho)
          %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> rest, ds, Cv.Agent{}, x, cur), Cv.layer(rest, ds, Cv.Agent{}, x, c1), LA.pv.layer_cons(s, rest, ds, Cv.Agent{}, x, cur)) : {Cv.layer(w, ds, Cv.Agent{}, x, cur) == _ : Maybe<&2, Cv.Val>}
          %Equal.sym(Maybe<&2, Cv.Val>, c1, cur, LA.pv.layer_miss(s, ds, Cv.Agent{}, x, cur, miss)) : {Cv.layer(w, ds, Cv.Agent{}, x, cur) == Cv.layer(rest, ds, Cv.Agent{}, x, _) : Maybe<&2, Cv.Val>}
          pv.persist_go(rest, ds, x, keeps, cur, Cv.out.at(rest, ds, Cv.Persist{}), {==})

def pv.pr_m(m: Maybe<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, keeps: {Cv.flag.at(Cv.find(ds, x), Cv.Persist{}) == True{} : Bool}) -> {Cv.value.at(m, ds, cfg, [Cv.Ag{Cv.written(ss, ds, Cv.Persist{}), Nil{}}], x) == Cv.value.at(m, ds, cfg, [Cv.Ag{Nil{}, ss}], x) : Maybe<&2, Cv.Val>}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      +r = Cv.root.val(ds, cfg, x, d)
      Equal.cong(Maybe<&2, Cv.Val>, Maybe<&2, Cv.Val>, z => Some{Maybe.default(&2, Cv.Val, z, r)}, Cv.layer(Cv.written(ss, ds, Cv.Persist{}), ds, Cv.Agent{}, x, None{}), Cv.layer(ss, ds, Cv.Agent{}, x, None{}), pv.persist_go(ss, ds, x, keeps, None{}, Cv.out.at(ss, ds, Cv.Persist{}), {==}))

def pv.cvar_persist_roundtrip(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, keeps: {Cv.flag.at(Cv.find(ds, x), Cv.Persist{}) == True{} : Bool}) -> {Cv.value(ds, cfg, [Cv.Ag{Cv.written(ss, ds, Cv.Persist{}), Nil{}}], x) == Cv.value(ds, cfg, [Cv.Ag{Nil{}, ss}], x) : Maybe<&2, Cv.Val>}:
  pv.pr_m(Cv.find(ds, x), ds, cfg, ss, x, keeps)

def Cvar.cvar_persist_roundtrip(ds, cfg, ss, x, keeps):
  pv.cvar_persist_roundtrip(ds, cfg, ss, x, keeps)
