# eukhe: lemmas the proofs of area model_facts share: each part of a
# request Rust writes reads back (the wire's round trips, LWire.pw6.nat).

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_model_facts.bend as FMF
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/model_facts.bend as ModelFacts
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

def mfb.ans(a: If.Ans, +rest: String, h: {ModelFacts.mf.ans_fits(a) == True{} : Bool}) -> {Wr.Got{a, rest} == FMF.get_ans(Wr.get_nat(ModelFacts.mf.ans(a, rest))) : Wr.Dec<If.Ans>}:
  match a:
    case If.Known{+v}:
      %LWire.pw6.nat(v, rest, h) : {Wr.Got{If.Known{v}, rest} == FMF.get_ans.known(_) : Wr.Dec<If.Ans>}
      {==}
    case If.Unknown{}:
      {==}

def mfb.ent(e: Maybe<&2, Maybe<&2, Nat>>, +rest: String, h: {ModelFacts.mf.ent_fits(e) == True{} : Bool}) -> {Wr.Got{e, rest} == FMF.get_ent(Wr.get_nat(ModelFacts.mf.ent(e, rest))) : Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>}:
  match e:
    case None{}:
      {==}
    case Some{w}:
      match w:
        case None{}:
          {==}
        case Some{+v}:
          %LWire.pw6.nat(v, rest, h) : {Wr.Got{Some{Some{v}}, rest} == FMF.get_ent.val(_) : Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>}
          {==}

def mfb.elv(l: Fx.ELv, -rest: String) -> {Wr.Got{l, rest} == FMF.get_elv(Wr.get_nat(ModelFacts.mf.elv(l, rest))) : Wr.Dec<Fx.ELv>}:
  match l:
    case Fx.EMinimal{}:
      {==}
    case Fx.ELow{}:
      {==}
    case Fx.EMedium{}:
      {==}
    case Fx.EHigh{}:
      {==}
    case Fx.EXhigh{}:
      {==}
    case Fx.EMax{}:
      {==}

def mfb.row(m: Maybe<&2, Nat>, +t: Nat, +k: Nat, +rest: String, hm: {LawsBase.wire_mfits(m) == True{} : Bool}, +ht: {LawsBase.wire_fits(t) == True{} : Bool}, +hk: {LawsBase.wire_fits(k) == True{} : Bool}) -> {Wr.Got{Fx.PRow{m, t, k}, rest} == FMF.get_row(ModelFacts.mf.row(Fx.PRow{m, t, k}, rest)) : Wr.Dec<Fx.PRow>}:
  match m:
    case None{}:
      %LWire.pw6.nat(t, Wr.put_nat(k, rest), ht) : {Wr.Got{Fx.PRow{None{}, t, k}, rest} == FMF.get_row.t(None{}, _) : Wr.Dec<Fx.PRow>}
      %LWire.pw6.nat(k, rest, hk) : {Wr.Got{Fx.PRow{None{}, t, k}, rest} == FMF.get_row.k(None{}, t, _) : Wr.Dec<Fx.PRow>}
      {==}
    case Some{+x}:
      %LWire.pw6.nat(x, Wr.put_nat(t, Wr.put_nat(k, rest)), hm) : {Wr.Got{Fx.PRow{Some{x}, t, k}, rest} == FMF.get_row.m(FMF.get_mnat.some(_)) : Wr.Dec<Fx.PRow>}
      %LWire.pw6.nat(t, Wr.put_nat(k, rest), ht) : {Wr.Got{Fx.PRow{Some{x}, t, k}, rest} == FMF.get_row.t(Some{x}, _) : Wr.Dec<Fx.PRow>}
      %LWire.pw6.nat(k, rest, hk) : {Wr.Got{Fx.PRow{Some{x}, t, k}, rest} == FMF.get_row.k(Some{x}, t, _) : Wr.Dec<Fx.PRow>}
      {==}

# the row x = PRow{m, t, k} and the rows xs after it read back
def mfb.go(xs: List<&2, Fx.PRow>, +m: Maybe<&2, Nat>, +t: Nat, +k: Nat, +rest: String, +hm: {LawsBase.wire_mfits(m) == True{} : Bool}, +ht: {LawsBase.wire_fits(t) == True{} : Bool}, +hk: {LawsBase.wire_fits(k) == True{} : Bool}, +hr: {ModelFacts.mf.rows_fit(xs) == True{} : Bool}) -> {Wr.Got{Fx.PRow{m, t, k} <> xs, rest} == FMF.get_rows.go(List.length(&2, Fx.PRow, xs), FMF.get_row(ModelFacts.mf.row(Fx.PRow{m, t, k}, ModelFacts.mf.items(xs, rest)))) : Wr.Dec<List<&2, Fx.PRow>>}:
  match xs:
    case Nil{}:
      %mfb.row(m, t, k, rest, hm, ht, hk) : {Wr.Got{[Fx.PRow{m, t, k}], rest} == FMF.get_rows.go(0n, _) : Wr.Dec<List<&2, Fx.PRow>>}
      {==}
    case Fx.PRow{+m2, +t2, +k2} <> +ys:
      +items = ModelFacts.mf.items(Fx.PRow{m2, t2, k2} <> ys, rest)
      %mfb.row(m, t, k, items, hm, ht, hk) : {Wr.Got{Fx.PRow{m, t, k} <> Fx.PRow{m2, t2, k2} <> ys, rest} == FMF.get_rows.go(List.length(&2, Fx.PRow, Fx.PRow{m2, t2, k2} <> ys), _) : Wr.Dec<List<&2, Fx.PRow>>}
      +hm2 = LLogicBool.wr_and_l(LawsBase.wire_mfits(m2), Bool.and(LawsBase.wire_fits(t2), Bool.and(LawsBase.wire_fits(k2), ModelFacts.mf.rows_fit(ys))), hr)
      +hr1 = LLogicBool.wr_and_r(LawsBase.wire_mfits(m2), Bool.and(LawsBase.wire_fits(t2), Bool.and(LawsBase.wire_fits(k2), ModelFacts.mf.rows_fit(ys))), hr)
      +ht2 = LLogicBool.wr_and_l(LawsBase.wire_fits(t2), Bool.and(LawsBase.wire_fits(k2), ModelFacts.mf.rows_fit(ys)), hr1)
      +hr2 = LLogicBool.wr_and_r(LawsBase.wire_fits(t2), Bool.and(LawsBase.wire_fits(k2), ModelFacts.mf.rows_fit(ys)), hr1)
      +hk2 = LLogicBool.wr_and_l(LawsBase.wire_fits(k2), ModelFacts.mf.rows_fit(ys), hr2)
      +hys = LLogicBool.wr_and_r(LawsBase.wire_fits(k2), ModelFacts.mf.rows_fit(ys), hr2)
      %mfb.go(ys, m2, t2, k2, rest, hm2, ht2, hk2, hys) : {Wr.Got{Fx.PRow{m, t, k} <> Fx.PRow{m2, t2, k2} <> ys, rest} == FMF.get_rows.cons(Fx.PRow{m, t, k}, _) : Wr.Dec<List<&2, Fx.PRow>>}
      {==}

def mfb.mnat(x: Maybe<&2, Nat>) -> {FMF.put_mnat(x) == ModelFacts.mf.mnat(x, "") : String}:
  match x:
    case None{}:
      {==}
    case Some{k}:
      {==}
