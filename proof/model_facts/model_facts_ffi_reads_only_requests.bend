# eukhe: the proof of LAW model_facts_ffi_reads_only_requests
#
# PROOF: whatever a decoder of bend/ffi_model_facts.bend reads is the
# laws' spelling (laws/model_facts.bend mf.*) of what it read, then its
# rest, and its numbers fit: a tag by the wire's exactness law
# (wire_nat_exact; an unknown tag is Bad), a Bool by wire_bool_exact, a
# number by wire_nat_exact and wire_nat_decoded_fits, the price rows by
# their count and row by row, a request field by field, the equation of the
# input so far carried from stage to stage (`pre`). An answer that is no
# error form comes from a request read whole with nothing left (mfo.fin).

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_model_facts.bend as FMF
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/model_facts.bend as ModelFacts
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/base/spell.bend as LAWireSpell
import ../base/logic/bool.bend as LLogicBool

# s spelled up to a field a is s spelled up to its spelling b
def mfo.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# a request as the laws spell it, then the rest r
def mfo.spell(q: FMF.Req, r: String) -> String:
  match q:
    case FMF.QFlag{a, d}:
      Wr.put_nat(0n, ModelFacts.mf.ans(a, Wr.put_bool(d, r)))
    case FMF.QAdaptive{c, a}:
      Wr.put_nat(1n, ModelFacts.mf.mbool(c, ModelFacts.mf.ans(a, r)))
    case FMF.QEffort{m, l}:
      Wr.put_nat(2n, ModelFacts.mf.map(m, ModelFacts.mf.elv(l, r)))
    case FMF.QPrice{+rows, m, t}:
      Wr.put_nat(3n, Wr.put_nat(List.length(&2, Fx.PRow, rows), ModelFacts.mf.items(rows, Wr.put_nat(m, Wr.put_nat(t, r)))))
    case FMF.QReasoning{x, e, l}:
      Wr.put_nat(4n, ModelFacts.mf.shape(x, ModelFacts.mf.ent(e, ModelFacts.mf.elv(l, r))))

# with nothing after it, it is the laws' speller
def mfo.spell_nil(q: FMF.Req) -> {mfo.spell(q, "") == ModelFacts.mf.spell(q) : String}:
  match q:
    case FMF.QFlag{a, d}:
      {==}
    case FMF.QAdaptive{c, a}:
      {==}
    case FMF.QEffort{m, l}:
      {==}
    case FMF.QPrice{rows, m, t}:
      {==}
    case FMF.QReasoning{x, e, l}:
      {==}

# Fields
# ------

# the rulebook's answer: 0, the value | 1
def mfo.Ans(x: String, d: Wr.Dec<If.Ans>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {x == ModelFacts.mf.ans(a, r) : String} & {ModelFacts.mf.ans_fits(a) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def mfo.ans.known(+x: String, +x0: String, pre: {x == Wr.put_nat(0n, x0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x0) == d : Wr.Dec<Nat>}) -> mfo.Ans(x, FMF.get_ans.known(d)):
  match d:
    case Wr.Got{+v, +x1}:
      +ee = ed
      (mfo.step(z => Wr.put_nat(0n, z), x, x0, Wr.put_nat(v, x1), pre, Wire.wire_nat_exact(x0, v, x1, ee)), Wire.wire_nat_decoded_fits(x0, v, x1, ee))
    case Wr.Bad{}:
      Unit{}

def mfo.ans.go(+x: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x) == d : Wr.Dec<Nat>}) -> mfo.Ans(x, FMF.get_ans(d)):
  match d:
    case Wr.Got{+t, +x0}:
      match t:
        case 0n:
          mfo.ans.known(x, x0, Wire.wire_nat_exact(x, 0n, x0, ed), Wr.get_nat(x0), {==})
        case 1n:
          (Wire.wire_nat_exact(x, 1n, x0, ed), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def mfo.ans(+x: String) -> mfo.Ans(x, FMF.get_ans(Wr.get_nat(x))):
  mfo.ans.go(x, Wr.get_nat(x), {==})

# a Bool: T | F
def mfo.Bool(x: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {x == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def mfo.bool.go(+x: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(x) == d : Wr.Dec<Bool>}) -> mfo.Bool(x, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(x, b, r, ed)
    case Wr.Bad{}:
      Unit{}

def mfo.bool(+x: String) -> mfo.Bool(x, Wr.get_bool(x)):
  mfo.bool.go(x, Wr.get_bool(x), {==})

# the compat flag: 0 | 1, the Bool
def mfo.MBool(x: String, d: Wr.Dec<Maybe<&2, Bool>>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {x == ModelFacts.mf.mbool(c, r) : String}
    case Wr.Bad{}:
      Unit

def mfo.mbool.some(-x: String, +x0: String, pre: {x == Wr.put_nat(1n, x0) : String}, d: Wr.Dec<Bool>, xd: mfo.Bool(x0, d)) -> mfo.MBool(x, FMF.get_mbool.some(d)):
  match d:
    case Wr.Got{+b, +x1}:
      mfo.step(z => Wr.put_nat(1n, z), x, x0, Wr.put_bool(b, x1), pre, xd)
    case Wr.Bad{}:
      Unit{}

def mfo.mbool.go(+x: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x) == d : Wr.Dec<Nat>}) -> mfo.MBool(x, FMF.get_mbool(d)):
  match d:
    case Wr.Got{+t, +x0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(x, 0n, x0, ed)
        case 1n:
          mfo.mbool.some(x, x0, Wire.wire_nat_exact(x, 1n, x0, ed), Wr.get_bool(x0), mfo.bool(x0))
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def mfo.mbool(+x: String) -> mfo.MBool(x, FMF.get_mbool(Wr.get_nat(x))):
  mfo.mbool.go(x, Wr.get_nat(x), {==})

# a map entry: 0 | 1, 0 | 1, 1, the code
def mfo.Ent(x: String, d: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {x == ModelFacts.mf.ent(e, r) : String} & {ModelFacts.mf.ent_fits(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def mfo.ent.val(+x: String, +x1: String, pre: {x == Wr.put_nat(1n, Wr.put_nat(1n, x1)) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x1) == d : Wr.Dec<Nat>}) -> mfo.Ent(x, FMF.get_ent.val(d)):
  match d:
    case Wr.Got{+v, +x2}:
      +ee = ed
      (mfo.step(z => Wr.put_nat(1n, Wr.put_nat(1n, z)), x, x1, Wr.put_nat(v, x2), pre, Wire.wire_nat_exact(x1, v, x2, ee)), Wire.wire_nat_decoded_fits(x1, v, x2, ee))
    case Wr.Bad{}:
      Unit{}

def mfo.ent.inner(+x: String, +x0: String, pre: {x == Wr.put_nat(1n, x0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x0) == d : Wr.Dec<Nat>}) -> mfo.Ent(x, FMF.get_ent.inner(d)):
  match d:
    case Wr.Got{+t, +x1}:
      match t:
        case 0n:
          (mfo.step(z => Wr.put_nat(1n, z), x, x0, Wr.put_nat(0n, x1), pre, Wire.wire_nat_exact(x0, 0n, x1, ed)), {==})
        case 1n:
          mfo.ent.val(x, x1, mfo.step(z => Wr.put_nat(1n, z), x, x0, Wr.put_nat(1n, x1), pre, Wire.wire_nat_exact(x0, 1n, x1, ed)), Wr.get_nat(x1), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def mfo.ent.go(+x: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x) == d : Wr.Dec<Nat>}) -> mfo.Ent(x, FMF.get_ent(d)):
  match d:
    case Wr.Got{+t, +x0}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(x, 0n, x0, ed), {==})
        case 1n:
          mfo.ent.inner(x, x0, Wire.wire_nat_exact(x, 1n, x0, ed), Wr.get_nat(x0), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def mfo.ent(+x: String) -> mfo.Ent(x, FMF.get_ent(Wr.get_nat(x))):
  mfo.ent.go(x, Wr.get_nat(x), {==})

# a level: 0 .. 5
def mfo.ELv(x: String, d: Wr.Dec<Fx.ELv>) -> Type:
  match d:
    case Wr.Got{l, r}:
      {x == ModelFacts.mf.elv(l, r) : String}
    case Wr.Bad{}:
      Unit

def mfo.elv.tag(-x: String, t: Nat, -x0: String, en: {x == Wr.put_nat(t, x0) : String}) -> mfo.ELv(x, FMF.get_elv.tag(t, x0)):
  match t:
    case 0n:
      en
    case 1n:
      en
    case 2n:
      en
    case 3n:
      en
    case 4n:
      en
    case 5n:
      en
    case 6n+k:
      Unit{}

def mfo.elv.go(+x: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x) == d : Wr.Dec<Nat>}) -> mfo.ELv(x, FMF.get_elv(d)):
  match d:
    case Wr.Got{+t, +x0}:
      mfo.elv.tag(x, t, x0, Wire.wire_nat_exact(x, t, x0, ed))
    case Wr.Bad{}:
      Unit{}

def mfo.elv(+x: String) -> mfo.ELv(x, FMF.get_elv(Wr.get_nat(x))):
  mfo.elv.go(x, Wr.get_nat(x), {==})

# a shape: 0 none | 1 Claude | 2 GPT | 3 gpt-oss
def mfo.Shape(x: String, d: Wr.Dec<Maybe<&2, Fx.Shape>>) -> Type:
  match d:
    case Wr.Got{sh, r}:
      {x == ModelFacts.mf.shape(sh, r) : String}
    case Wr.Bad{}:
      Unit

def mfo.shape.tag(-x: String, t: Nat, -x0: String, en: {x == Wr.put_nat(t, x0) : String}) -> mfo.Shape(x, FMF.get_shape.tag(t, x0)):
  match t:
    case 0n:
      en
    case 1n:
      en
    case 2n:
      en
    case 3n:
      en
    case 4n+k:
      Unit{}

def mfo.shape.go(+x: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x) == d : Wr.Dec<Nat>}) -> mfo.Shape(x, FMF.get_shape(d)):
  match d:
    case Wr.Got{+t, +x0}:
      mfo.shape.tag(x, t, x0, Wire.wire_nat_exact(x, t, x0, ed))
    case Wr.Bad{}:
      Unit{}

def mfo.shape(+x: String) -> mfo.Shape(x, FMF.get_shape(Wr.get_nat(x))):
  mfo.shape.go(x, Wr.get_nat(x), {==})

# a row's model: 0 every model | 1, the model
def mfo.MNat(x: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {x == ModelFacts.mf.mnat(m, r) : String} & {LawsBase.wire_mfits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def mfo.mnat.some(+x: String, +x0: String, pre: {x == Wr.put_nat(1n, x0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x0) == d : Wr.Dec<Nat>}) -> mfo.MNat(x, FMF.get_mnat.some(d)):
  match d:
    case Wr.Got{+n, +x1}:
      +ee = ed
      (mfo.step(z => Wr.put_nat(1n, z), x, x0, Wr.put_nat(n, x1), pre, Wire.wire_nat_exact(x0, n, x1, ee)), Wire.wire_nat_decoded_fits(x0, n, x1, ee))
    case Wr.Bad{}:
      Unit{}

def mfo.mnat.go(+x: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x) == d : Wr.Dec<Nat>}) -> mfo.MNat(x, FMF.get_mnat(d)):
  match d:
    case Wr.Got{+t, +x0}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(x, 0n, x0, ed), {==})
        case 1n:
          mfo.mnat.some(x, x0, Wire.wire_nat_exact(x, 1n, x0, ed), Wr.get_nat(x0), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def mfo.mnat(+x: String) -> mfo.MNat(x, FMF.get_mnat(Wr.get_nat(x))):
  mfo.mnat.go(x, Wr.get_nat(x), {==})

# The price rows
# --------------

# a row's numbers fit
def mfo.row_fit(p: Fx.PRow) -> Bool:
  match p:
    case Fx.PRow{m, t, k}:
      Bool.and(LawsBase.wire_mfits(m), Bool.and(LawsBase.wire_fits(t), LawsBase.wire_fits(k)))

def mfo.rows_fit_cons(p: Fx.PRow, -ys: List<&2, Fx.PRow>, fp: {mfo.row_fit(p) == True{} : Bool}, fy: {ModelFacts.mf.rows_fit(ys) == True{} : Bool}) -> {ModelFacts.mf.rows_fit(p <> ys) == True{} : Bool}:
  match p:
    case Fx.PRow{+m, +t, +k}:
      +f1 = fp
      +f2 = LLogicBool.wr_and_r(LawsBase.wire_mfits(m), Bool.and(LawsBase.wire_fits(t), LawsBase.wire_fits(k)), f1)
      LAWireSpell.ws_and_tt(LawsBase.wire_mfits(m), Bool.and(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(k), ModelFacts.mf.rows_fit(ys))), LLogicBool.wr_and_l(LawsBase.wire_mfits(m), Bool.and(LawsBase.wire_fits(t), LawsBase.wire_fits(k)), f1), LAWireSpell.ws_and_tt(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(k), ModelFacts.mf.rows_fit(ys)), LLogicBool.wr_and_l(LawsBase.wire_fits(t), LawsBase.wire_fits(k), f2), LAWireSpell.ws_and_tt(LawsBase.wire_fits(k), ModelFacts.mf.rows_fit(ys), LLogicBool.wr_and_r(LawsBase.wire_fits(t), LawsBase.wire_fits(k), f2), fy)))

# a row: its model, its tier, its multiplier
def mfo.Row(x: String, d: Wr.Dec<Fx.PRow>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {x == ModelFacts.mf.row(p, r) : String} & {mfo.row_fit(p) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def mfo.row.k(+x: String, +m: Maybe<&2, Nat>, +t: Nat, +x2: String, pre: {x == ModelFacts.mf.mnat(m, Wr.put_nat(t, x2)) : String}, fm: {LawsBase.wire_mfits(m) == True{} : Bool}, ft: {LawsBase.wire_fits(t) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x2) == d : Wr.Dec<Nat>}) -> mfo.Row(x, FMF.get_row.k(m, t, d)):
  match d:
    case Wr.Got{+k, +x3}:
      +ee = ed
      (mfo.step(z => ModelFacts.mf.mnat(m, Wr.put_nat(t, z)), x, x2, Wr.put_nat(k, x3), pre, Wire.wire_nat_exact(x2, k, x3, ee)), LAWireSpell.ws_and_tt(LawsBase.wire_mfits(m), Bool.and(LawsBase.wire_fits(t), LawsBase.wire_fits(k)), fm, LAWireSpell.ws_and_tt(LawsBase.wire_fits(t), LawsBase.wire_fits(k), ft, Wire.wire_nat_decoded_fits(x2, k, x3, ee))))
    case Wr.Bad{}:
      Unit{}

def mfo.row.t(+x: String, +m: Maybe<&2, Nat>, +x1: String, pre: {x == ModelFacts.mf.mnat(m, x1) : String}, fm: {LawsBase.wire_mfits(m) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x1) == d : Wr.Dec<Nat>}) -> mfo.Row(x, FMF.get_row.t(m, d)):
  match d:
    case Wr.Got{+t, +x2}:
      +ee = ed
      mfo.row.k(x, m, t, x2, mfo.step(z => ModelFacts.mf.mnat(m, z), x, x1, Wr.put_nat(t, x2), pre, Wire.wire_nat_exact(x1, t, x2, ee)), fm, Wire.wire_nat_decoded_fits(x1, t, x2, ee), Wr.get_nat(x2), {==})
    case Wr.Bad{}:
      Unit{}

def mfo.row.m(+x: String, d: Wr.Dec<Maybe<&2, Nat>>, xd: mfo.MNat(x, d)) -> mfo.Row(x, FMF.get_row.m(d)):
  match d:
    case Wr.Got{+m, +x1}:
      (e, fm) = xd
      mfo.row.t(x, m, x1, e, fm, Wr.get_nat(x1), {==})
    case Wr.Bad{}:
      Unit{}

def mfo.row(+x: String) -> mfo.Row(x, FMF.get_row(x)):
  mfo.row.m(x, FMF.get_mnat(Wr.get_nat(x)), mfo.mnat(x))

# what the row loop's answer says about its input x (k + 1 rows)
def mfo.Tl(x: String, k: Nat, d: Wr.Dec<List<&2, Fx.PRow>>) -> Type:
  match d:
    case Wr.Got{ps, r}:
      {x == ModelFacts.mf.items(ps, r) : String} & ({List.length(&2, Fx.PRow, ps) == 1n+k : Nat} & {ModelFacts.mf.rows_fit(ps) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def mfo.tl.at(+x: String, -d: Wr.Dec<Fx.PRow>, er: {FMF.get_row(x) == d : Wr.Dec<Fx.PRow>}) -> mfo.Row(x, d):
  %er : mfo.Row(x, _)
  mfo.row(x)

def mfo.tl.one(-x: String, +p: Fx.PRow, -x3: String, ra: mfo.Row(x, Wr.Got{p, x3})) -> mfo.Tl(x, 0n, Wr.Got{[p], x3}):
  (ea, fp) = ra
  (ea, ({==}, mfo.rows_fit_cons(p, Nil{}, fp, {==})))

def mfo.tl.step(-x: String, +p: Fx.PRow, +x3: String, -k: Nat, d: Wr.Dec<List<&2, Fx.PRow>>, ih: mfo.Tl(x3, k, d), ra: mfo.Row(x, Wr.Got{p, x3})) -> mfo.Tl(x, 1n+k, FMF.get_rows.cons(p, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (ea, fp) = ra
      (mfo.step(z => ModelFacts.mf.row(p, z), x, x3, ModelFacts.mf.items(ys, r), ea, e1),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Fx.PRow, ys), 1n+k, e2), mfo.rows_fit_cons(p, ys, fp, e3)))
    case Wr.Bad{}:
      Unit{}

# the row loop accepts only spelled rows
def mfo.tl(k: Nat, cur: Wr.Dec<Fx.PRow>, +x: String, er: {FMF.get_row(x) == cur : Wr.Dec<Fx.PRow>}) -> mfo.Tl(x, k, FMF.get_rows.go(k, cur)):
  match k cur:
    case 0n Wr.Got{+p, +x3}:
      mfo.tl.one(x, p, x3, mfo.tl.at(x, Wr.Got{p, x3}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++j Wr.Got{+p, +x3}:
      mfo.tl.step(x, p, x3, j, FMF.get_rows.go(j, FMF.get_row(x3)), mfo.tl(j, FMF.get_row(x3), x3, {==}), mfo.tl.at(x, Wr.Got{p, x3}, er))
    case 1n++j Wr.Bad{}:
      Unit{}

# what the rows decoder's answer says about its input x
def mfo.Rows(x: String, d: Wr.Dec<List<&2, Fx.PRow>>) -> Type:
  match d:
    case Wr.Got{ps, r}:
      {x == Wr.put_nat(List.length(&2, Fx.PRow, ps), ModelFacts.mf.items(ps, r)) : String} & ({LawsBase.wire_fits(List.length(&2, Fx.PRow, ps)) == True{} : Bool} & {ModelFacts.mf.rows_fit(ps) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def mfo.rows.eq(-x: String, -x0: String, -m: Nat, en: {x == Wr.put_nat(1n+m, x0) : String}, +t: List<&2, Fx.PRow>, -r: String, e1: {x0 == ModelFacts.mf.items(t, r) : String}, e2: {List.length(&2, Fx.PRow, t) == 1n+m : Nat}) -> {x == Wr.put_nat(List.length(&2, Fx.PRow, t), ModelFacts.mf.items(t, r)) : String}:
  %Equal.sym(Nat, List.length(&2, Fx.PRow, t), 1n+m, e2) : {x == Wr.put_nat(_, ModelFacts.mf.items(t, r)) : String}
  %e1 : {x == Wr.put_nat(1n+m, _) : String}
  en

def mfo.rows.fit(-m: Nat, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, +t: List<&2, Fx.PRow>, e2: {List.length(&2, Fx.PRow, t) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Fx.PRow, t)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Fx.PRow, t), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  hn

def mfo.rows.conv(-x: String, -x0: String, -m: Nat, en: {x == Wr.put_nat(1n+m, x0) : String}, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Fx.PRow>>, tl: mfo.Tl(x0, m, d)) -> mfo.Rows(x, d):
  match d:
    case Wr.Got{+t, +r}:
      (e1, e23) = tl
      (e2, e3) = e23
      +e4 = e2
      (mfo.rows.eq(x, x0, m, en, t, r, e1, e4), (mfo.rows.fit(m, hn, t, e4), e3))
    case Wr.Bad{}:
      Unit{}

def mfo.rows.nat(-x: String, n: Nat, +x0: String, en: {x == Wr.put_nat(n, x0) : String}, hn: {LawsBase.wire_fits(n) == True{} : Bool}) -> mfo.Rows(x, FMF.get_rows.count(n, x0)):
  match n:
    case 0n:
      (en, (hn, {==}))
    case 1n++m:
      mfo.rows.conv(x, x0, m, en, hn, FMF.get_rows.go(m, FMF.get_row(x0)), mfo.tl(m, FMF.get_row(x0), x0, {==}))

def mfo.rows.top(+x: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x) == d : Wr.Dec<Nat>}) -> mfo.Rows(x, FMF.get_rows(d)):
  match d:
    case Wr.Got{+n, +x0}:
      +e2 = ed
      mfo.rows.nat(x, n, x0, Wire.wire_nat_exact(x, n, x0, e2), Wire.wire_nat_decoded_fits(x, n, x0, e2))
    case Wr.Bad{}:
      Unit{}

def mfo.rows(+x: String) -> mfo.Rows(x, FMF.get_rows(Wr.get_nat(x))):
  mfo.rows.top(x, Wr.get_nat(x), {==})

# Requests
# --------

# what the request decoder's answer says about its input s
def mfo.Q(s: String, d: Wr.Dec<FMF.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == mfo.spell(q, r) : String} & {ModelFacts.mf.fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# 0 a flag: the answer, the default
def mfo.flag.d(+s: String, +a: If.Ans, +x1: String, pre: {s == Wr.put_nat(0n, ModelFacts.mf.ans(a, x1)) : String}, f: {ModelFacts.mf.ans_fits(a) == True{} : Bool}, d: Wr.Dec<Bool>, xd: mfo.Bool(x1, d)) -> mfo.Q(s, FMF.get_flag.d(a, d)):
  match d:
    case Wr.Got{+b, +x2}:
      (mfo.step(z => Wr.put_nat(0n, ModelFacts.mf.ans(a, z)), s, x1, Wr.put_bool(b, x2), pre, xd), f)
    case Wr.Bad{}:
      Unit{}

def mfo.flag(+s: String, +x0: String, pre: {s == Wr.put_nat(0n, x0) : String}, d: Wr.Dec<If.Ans>, xd: mfo.Ans(x0, d)) -> mfo.Q(s, FMF.get_flag(d)):
  match d:
    case Wr.Got{+a, +x1}:
      (e, f) = xd
      mfo.flag.d(s, a, x1, mfo.step(z => Wr.put_nat(0n, z), s, x0, ModelFacts.mf.ans(a, x1), pre, e), f, Wr.get_bool(x1), mfo.bool(x1))
    case Wr.Bad{}:
      Unit{}

# 1 adaptive thinking: the compat flag, the answer
def mfo.ad.a(+s: String, +c: Maybe<&2, Bool>, +x1: String, pre: {s == Wr.put_nat(1n, ModelFacts.mf.mbool(c, x1)) : String}, d: Wr.Dec<If.Ans>, xd: mfo.Ans(x1, d)) -> mfo.Q(s, FMF.get_adaptive.a(c, d)):
  match d:
    case Wr.Got{+a, +x2}:
      (e, f) = xd
      (mfo.step(z => Wr.put_nat(1n, ModelFacts.mf.mbool(c, z)), s, x1, ModelFacts.mf.ans(a, x2), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def mfo.ad(+s: String, +x0: String, pre: {s == Wr.put_nat(1n, x0) : String}, d: Wr.Dec<Maybe<&2, Bool>>, xd: mfo.MBool(x0, d)) -> mfo.Q(s, FMF.get_adaptive(d)):
  match d:
    case Wr.Got{+c, +x1}:
      mfo.ad.a(s, c, x1, mfo.step(z => Wr.put_nat(1n, z), s, x0, ModelFacts.mf.mbool(c, x1), pre, xd), FMF.get_ans(Wr.get_nat(x1)), mfo.ans(x1))
    case Wr.Bad{}:
      Unit{}

# 2 the Bedrock effort: six entries, the level
def mfo.eff.l(+s: String, +mi: Maybe<&2, Maybe<&2, Nat>>, +lo: Maybe<&2, Maybe<&2, Nat>>, +me: Maybe<&2, Maybe<&2, Nat>>, +hi: Maybe<&2, Maybe<&2, Nat>>, +xh: Maybe<&2, Maybe<&2, Nat>>, +mx: Maybe<&2, Maybe<&2, Nat>>, +x6: String,
  pre: {s == Wr.put_nat(2n, ModelFacts.mf.ent(mi, ModelFacts.mf.ent(lo, ModelFacts.mf.ent(me, ModelFacts.mf.ent(hi, ModelFacts.mf.ent(xh, ModelFacts.mf.ent(mx, x6))))))) : String},
  f1: {ModelFacts.mf.ent_fits(mi) == True{} : Bool}, f2: {ModelFacts.mf.ent_fits(lo) == True{} : Bool}, f3: {ModelFacts.mf.ent_fits(me) == True{} : Bool}, f4: {ModelFacts.mf.ent_fits(hi) == True{} : Bool}, f5: {ModelFacts.mf.ent_fits(xh) == True{} : Bool}, f6: {ModelFacts.mf.ent_fits(mx) == True{} : Bool},
  d: Wr.Dec<Fx.ELv>, xd: mfo.ELv(x6, d)) -> mfo.Q(s, FMF.get_effort.l(mi, lo, me, hi, xh, mx, d)):
  match d:
    case Wr.Got{+l, +x7}:
      (mfo.step(z => Wr.put_nat(2n, ModelFacts.mf.ent(mi, ModelFacts.mf.ent(lo, ModelFacts.mf.ent(me, ModelFacts.mf.ent(hi, ModelFacts.mf.ent(xh, ModelFacts.mf.ent(mx, z))))))), s, x6, ModelFacts.mf.elv(l, x7), pre, xd),
        LAWireSpell.ws_and_tt(ModelFacts.mf.ent_fits(mi), Bool.and(ModelFacts.mf.ent_fits(lo), Bool.and(ModelFacts.mf.ent_fits(me), Bool.and(ModelFacts.mf.ent_fits(hi), Bool.and(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx))))), f1,
          LAWireSpell.ws_and_tt(ModelFacts.mf.ent_fits(lo), Bool.and(ModelFacts.mf.ent_fits(me), Bool.and(ModelFacts.mf.ent_fits(hi), Bool.and(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx)))), f2,
            LAWireSpell.ws_and_tt(ModelFacts.mf.ent_fits(me), Bool.and(ModelFacts.mf.ent_fits(hi), Bool.and(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx))), f3,
              LAWireSpell.ws_and_tt(ModelFacts.mf.ent_fits(hi), Bool.and(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx)), f4,
                LAWireSpell.ws_and_tt(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx), f5, f6))))))
    case Wr.Bad{}:
      Unit{}

def mfo.eff.mx(+s: String, +mi: Maybe<&2, Maybe<&2, Nat>>, +lo: Maybe<&2, Maybe<&2, Nat>>, +me: Maybe<&2, Maybe<&2, Nat>>, +hi: Maybe<&2, Maybe<&2, Nat>>, +xh: Maybe<&2, Maybe<&2, Nat>>, +x5: String,
  pre: {s == Wr.put_nat(2n, ModelFacts.mf.ent(mi, ModelFacts.mf.ent(lo, ModelFacts.mf.ent(me, ModelFacts.mf.ent(hi, ModelFacts.mf.ent(xh, x5)))))) : String},
  f1: {ModelFacts.mf.ent_fits(mi) == True{} : Bool}, f2: {ModelFacts.mf.ent_fits(lo) == True{} : Bool}, f3: {ModelFacts.mf.ent_fits(me) == True{} : Bool}, f4: {ModelFacts.mf.ent_fits(hi) == True{} : Bool}, f5: {ModelFacts.mf.ent_fits(xh) == True{} : Bool},
  d: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>, xd: mfo.Ent(x5, d)) -> mfo.Q(s, FMF.get_effort.mx(mi, lo, me, hi, xh, d)):
  match d:
    case Wr.Got{+mx, +x6}:
      (e, f6) = xd
      mfo.eff.l(s, mi, lo, me, hi, xh, mx, x6, mfo.step(z => Wr.put_nat(2n, ModelFacts.mf.ent(mi, ModelFacts.mf.ent(lo, ModelFacts.mf.ent(me, ModelFacts.mf.ent(hi, ModelFacts.mf.ent(xh, z)))))), s, x5, ModelFacts.mf.ent(mx, x6), pre, e), f1, f2, f3, f4, f5, f6, FMF.get_elv(Wr.get_nat(x6)), mfo.elv(x6))
    case Wr.Bad{}:
      Unit{}

def mfo.eff.xh(+s: String, +mi: Maybe<&2, Maybe<&2, Nat>>, +lo: Maybe<&2, Maybe<&2, Nat>>, +me: Maybe<&2, Maybe<&2, Nat>>, +hi: Maybe<&2, Maybe<&2, Nat>>, +x4: String,
  pre: {s == Wr.put_nat(2n, ModelFacts.mf.ent(mi, ModelFacts.mf.ent(lo, ModelFacts.mf.ent(me, ModelFacts.mf.ent(hi, x4))))) : String},
  f1: {ModelFacts.mf.ent_fits(mi) == True{} : Bool}, f2: {ModelFacts.mf.ent_fits(lo) == True{} : Bool}, f3: {ModelFacts.mf.ent_fits(me) == True{} : Bool}, f4: {ModelFacts.mf.ent_fits(hi) == True{} : Bool},
  d: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>, xd: mfo.Ent(x4, d)) -> mfo.Q(s, FMF.get_effort.xh(mi, lo, me, hi, d)):
  match d:
    case Wr.Got{+xh, +x5}:
      (e, f5) = xd
      mfo.eff.mx(s, mi, lo, me, hi, xh, x5, mfo.step(z => Wr.put_nat(2n, ModelFacts.mf.ent(mi, ModelFacts.mf.ent(lo, ModelFacts.mf.ent(me, ModelFacts.mf.ent(hi, z))))), s, x4, ModelFacts.mf.ent(xh, x5), pre, e), f1, f2, f3, f4, f5, FMF.get_ent(Wr.get_nat(x5)), mfo.ent(x5))
    case Wr.Bad{}:
      Unit{}

def mfo.eff.hi(+s: String, +mi: Maybe<&2, Maybe<&2, Nat>>, +lo: Maybe<&2, Maybe<&2, Nat>>, +me: Maybe<&2, Maybe<&2, Nat>>, +x3: String,
  pre: {s == Wr.put_nat(2n, ModelFacts.mf.ent(mi, ModelFacts.mf.ent(lo, ModelFacts.mf.ent(me, x3)))) : String},
  f1: {ModelFacts.mf.ent_fits(mi) == True{} : Bool}, f2: {ModelFacts.mf.ent_fits(lo) == True{} : Bool}, f3: {ModelFacts.mf.ent_fits(me) == True{} : Bool},
  d: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>, xd: mfo.Ent(x3, d)) -> mfo.Q(s, FMF.get_effort.hi(mi, lo, me, d)):
  match d:
    case Wr.Got{+hi, +x4}:
      (e, f4) = xd
      mfo.eff.xh(s, mi, lo, me, hi, x4, mfo.step(z => Wr.put_nat(2n, ModelFacts.mf.ent(mi, ModelFacts.mf.ent(lo, ModelFacts.mf.ent(me, z)))), s, x3, ModelFacts.mf.ent(hi, x4), pre, e), f1, f2, f3, f4, FMF.get_ent(Wr.get_nat(x4)), mfo.ent(x4))
    case Wr.Bad{}:
      Unit{}

def mfo.eff.me(+s: String, +mi: Maybe<&2, Maybe<&2, Nat>>, +lo: Maybe<&2, Maybe<&2, Nat>>, +x2: String,
  pre: {s == Wr.put_nat(2n, ModelFacts.mf.ent(mi, ModelFacts.mf.ent(lo, x2))) : String},
  f1: {ModelFacts.mf.ent_fits(mi) == True{} : Bool}, f2: {ModelFacts.mf.ent_fits(lo) == True{} : Bool},
  d: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>, xd: mfo.Ent(x2, d)) -> mfo.Q(s, FMF.get_effort.me(mi, lo, d)):
  match d:
    case Wr.Got{+me, +x3}:
      (e, f3) = xd
      mfo.eff.hi(s, mi, lo, me, x3, mfo.step(z => Wr.put_nat(2n, ModelFacts.mf.ent(mi, ModelFacts.mf.ent(lo, z))), s, x2, ModelFacts.mf.ent(me, x3), pre, e), f1, f2, f3, FMF.get_ent(Wr.get_nat(x3)), mfo.ent(x3))
    case Wr.Bad{}:
      Unit{}

def mfo.eff.lo(+s: String, +mi: Maybe<&2, Maybe<&2, Nat>>, +x1: String,
  pre: {s == Wr.put_nat(2n, ModelFacts.mf.ent(mi, x1)) : String},
  f1: {ModelFacts.mf.ent_fits(mi) == True{} : Bool},
  d: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>, xd: mfo.Ent(x1, d)) -> mfo.Q(s, FMF.get_effort.lo(mi, d)):
  match d:
    case Wr.Got{+lo, +x2}:
      (e, f2) = xd
      mfo.eff.me(s, mi, lo, x2, mfo.step(z => Wr.put_nat(2n, ModelFacts.mf.ent(mi, z)), s, x1, ModelFacts.mf.ent(lo, x2), pre, e), f1, f2, FMF.get_ent(Wr.get_nat(x2)), mfo.ent(x2))
    case Wr.Bad{}:
      Unit{}

def mfo.eff(+s: String, +x0: String, pre: {s == Wr.put_nat(2n, x0) : String}, d: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>, xd: mfo.Ent(x0, d)) -> mfo.Q(s, FMF.get_effort(d)):
  match d:
    case Wr.Got{+mi, +x1}:
      (e, f1) = xd
      mfo.eff.lo(s, mi, x1, mfo.step(z => Wr.put_nat(2n, z), s, x0, ModelFacts.mf.ent(mi, x1), pre, e), f1, FMF.get_ent(Wr.get_nat(x1)), mfo.ent(x1))
    case Wr.Bad{}:
      Unit{}

# 3 a tier's multiplier: the rows, the model, the tier
def mfo.pr.t(+s: String, +rows: List<&2, Fx.PRow>, +m: Nat, +x2: String,
  pre: {s == Wr.put_nat(3n, Wr.put_nat(List.length(&2, Fx.PRow, rows), ModelFacts.mf.items(rows, Wr.put_nat(m, x2)))) : String},
  fl: {LawsBase.wire_fits(List.length(&2, Fx.PRow, rows)) == True{} : Bool}, fr: {ModelFacts.mf.rows_fit(rows) == True{} : Bool}, fm: {LawsBase.wire_fits(m) == True{} : Bool},
  d: Wr.Dec<Nat>, ed: {Wr.get_nat(x2) == d : Wr.Dec<Nat>}) -> mfo.Q(s, FMF.get_price.t(rows, m, d)):
  match d:
    case Wr.Got{+t, +x3}:
      +ee = ed
      (mfo.step(z => Wr.put_nat(3n, Wr.put_nat(List.length(&2, Fx.PRow, rows), ModelFacts.mf.items(rows, Wr.put_nat(m, z)))), s, x2, Wr.put_nat(t, x3), pre, Wire.wire_nat_exact(x2, t, x3, ee)),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Fx.PRow, rows)), Bool.and(ModelFacts.mf.rows_fit(rows), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(t))), fl,
          LAWireSpell.ws_and_tt(ModelFacts.mf.rows_fit(rows), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(t)), fr,
            LAWireSpell.ws_and_tt(LawsBase.wire_fits(m), LawsBase.wire_fits(t), fm, Wire.wire_nat_decoded_fits(x2, t, x3, ee)))))
    case Wr.Bad{}:
      Unit{}

def mfo.pr.m(+s: String, +rows: List<&2, Fx.PRow>, +x1: String,
  pre: {s == Wr.put_nat(3n, Wr.put_nat(List.length(&2, Fx.PRow, rows), ModelFacts.mf.items(rows, x1))) : String},
  fl: {LawsBase.wire_fits(List.length(&2, Fx.PRow, rows)) == True{} : Bool}, fr: {ModelFacts.mf.rows_fit(rows) == True{} : Bool},
  d: Wr.Dec<Nat>, ed: {Wr.get_nat(x1) == d : Wr.Dec<Nat>}) -> mfo.Q(s, FMF.get_price.m(rows, d)):
  match d:
    case Wr.Got{+m, +x2}:
      +ee = ed
      mfo.pr.t(s, rows, m, x2, mfo.step(z => Wr.put_nat(3n, Wr.put_nat(List.length(&2, Fx.PRow, rows), ModelFacts.mf.items(rows, z))), s, x1, Wr.put_nat(m, x2), pre, Wire.wire_nat_exact(x1, m, x2, ee)), fl, fr, Wire.wire_nat_decoded_fits(x1, m, x2, ee), Wr.get_nat(x2), {==})
    case Wr.Bad{}:
      Unit{}

def mfo.pr(+s: String, +x0: String, pre: {s == Wr.put_nat(3n, x0) : String}, d: Wr.Dec<List<&2, Fx.PRow>>, xd: mfo.Rows(x0, d)) -> mfo.Q(s, FMF.get_price(d)):
  match d:
    case Wr.Got{+rows, +x1}:
      (e, ff) = xd
      (fl, fr) = ff
      mfo.pr.m(s, rows, x1, mfo.step(z => Wr.put_nat(3n, z), s, x0, Wr.put_nat(List.length(&2, Fx.PRow, rows), ModelFacts.mf.items(rows, x1)), pre, e), fl, fr, Wr.get_nat(x1), {==})
    case Wr.Bad{}:
      Unit{}

# 4 the Bedrock reasoning fields: the shape, the entry, the level
def mfo.rs.l(+s: String, +sh: Maybe<&2, Fx.Shape>, +e: Maybe<&2, Maybe<&2, Nat>>, +x2: String, pre: {s == Wr.put_nat(4n, ModelFacts.mf.shape(sh, ModelFacts.mf.ent(e, x2))) : String}, f: {ModelFacts.mf.ent_fits(e) == True{} : Bool}, d: Wr.Dec<Fx.ELv>, xd: mfo.ELv(x2, d)) -> mfo.Q(s, FMF.get_reasoning.l(sh, e, d)):
  match d:
    case Wr.Got{+l, +x3}:
      (mfo.step(z => Wr.put_nat(4n, ModelFacts.mf.shape(sh, ModelFacts.mf.ent(e, z))), s, x2, ModelFacts.mf.elv(l, x3), pre, xd), f)
    case Wr.Bad{}:
      Unit{}

def mfo.rs.e(+s: String, +sh: Maybe<&2, Fx.Shape>, +x1: String, pre: {s == Wr.put_nat(4n, ModelFacts.mf.shape(sh, x1)) : String}, d: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>, xd: mfo.Ent(x1, d)) -> mfo.Q(s, FMF.get_reasoning.e(sh, d)):
  match d:
    case Wr.Got{+e, +x2}:
      (eq, f) = xd
      mfo.rs.l(s, sh, e, x2, mfo.step(z => Wr.put_nat(4n, ModelFacts.mf.shape(sh, z)), s, x1, ModelFacts.mf.ent(e, x2), pre, eq), f, FMF.get_elv(Wr.get_nat(x2)), mfo.elv(x2))
    case Wr.Bad{}:
      Unit{}

def mfo.rs(+s: String, +x0: String, pre: {s == Wr.put_nat(4n, x0) : String}, d: Wr.Dec<Maybe<&2, Fx.Shape>>, xd: mfo.Shape(x0, d)) -> mfo.Q(s, FMF.get_reasoning(d)):
  match d:
    case Wr.Got{+sh, +x1}:
      mfo.rs.e(s, sh, x1, mfo.step(z => Wr.put_nat(4n, z), s, x0, ModelFacts.mf.shape(sh, x1), pre, xd), FMF.get_ent(Wr.get_nat(x1)), mfo.ent(x1))
    case Wr.Bad{}:
      Unit{}

# the request: its tag, then its fields
def mfo.req.tag(+s: String, t: Nat, +x0: String, en: {s == Wr.put_nat(t, x0) : String}) -> mfo.Q(s, FMF.get_req.tag(t, x0)):
  match t:
    case 0n:
      mfo.flag(s, x0, en, FMF.get_ans(Wr.get_nat(x0)), mfo.ans(x0))
    case 1n:
      mfo.ad(s, x0, en, FMF.get_mbool(Wr.get_nat(x0)), mfo.mbool(x0))
    case 2n:
      mfo.eff(s, x0, en, FMF.get_ent(Wr.get_nat(x0)), mfo.ent(x0))
    case 3n:
      mfo.pr(s, x0, en, FMF.get_rows(Wr.get_nat(x0)), mfo.rows(x0))
    case 4n:
      mfo.rs(s, x0, en, FMF.get_shape(Wr.get_nat(x0)), mfo.shape(x0))
    case 5n+k:
      Unit{}

def mfo.req.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> mfo.Q(s, FMF.get_req.go(d)):
  match d:
    case Wr.Got{+t, +x0}:
      mfo.req.tag(s, t, x0, Wire.wire_nat_exact(s, t, x0, ed))
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled request that fits, then
# the rest
def mfo.req(+s: String) -> mfo.Q(s, FMF.get_req(s)):
  mfo.req.go(s, Wr.get_nat(s), {==})

# The entry
# ---------

def mfo.G(s: String) -> Type:
  Sigma<&1, &1, FMF.Req, q => {s == ModelFacts.mf.spell(q) : String} & {ModelFacts.mf.fits(q) == True{} : Bool}>

# the end check: nothing left answers the request, anything left is the
# error form
def mfo.fin(+s: String, +q: FMF.Req, r: String, pre: {s == mfo.spell(q, r) : String}, f: {ModelFacts.mf.fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FMF.run.end(Wr.end(r), q)) == False{} : Bool}) -> mfo.G(s):
  match r:
    case SNil{}:
      (q, (Equal.trans(String, s, mfo.spell(q, ""), ModelFacts.mf.spell(q), pre, mfo.spell_nil(q)), f))
    case SCon{c, y}:
      LAWireSpell.ws_absurd(mfo.G(s), ok)

def mfo.main(+s: String, d: Wr.Dec<FMF.Req>, inv: mfo.Q(s, d), ok: {LawsBase.wire_opens_err(FMF.run(d)) == False{} : Bool}) -> mfo.G(s):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      mfo.fin(s, q, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(mfo.G(s), ok)

def ModelFacts.model_facts_ffi_reads_only_requests(s, ok):
  mfo.main(s, FMF.get_req(s), mfo.req(s), ok)
