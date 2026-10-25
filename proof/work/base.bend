# eukhe: lemmas the proofs of area work share: the entry reads back what
# the laws' spellers write (wk.*_rt), its reply writer writes what the
# laws' speller writes, and its reader answers what the laws' reader
# answers on every input (wq.*).

import Base
import ../../bend/ffi_work.bend as FW
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/work.bend as Work
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

# Round trips
# -----------

def wk.blk_rt(b: Pr.Blk, +rest: String, +h: {Work.wk_blk_fits(b) == True{} : Bool}) -> {FW.get_blk(Work.wk_spell_blk(b, rest)) == Wr.Got{b, rest} : Wr.Dec<Pr.Blk>}:
  match b:
    case Pr.Call{+k, +f}:
      %LWire.pw6.nat(k, Wr.put_nat(f, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(k), LawsBase.wire_fits(f), h)) : {FW.get_blk.call(_) == Wr.Got{Pr.Call{k, f}, rest} : Wr.Dec<Pr.Blk>}
      %LWire.pw6.nat(f, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(k), LawsBase.wire_fits(f), h)) : {FW.get_blk.call.fp(k, _) == Wr.Got{Pr.Call{k, f}, rest} : Wr.Dec<Pr.Blk>}
      {==}
    case Pr.Res{+k, +f}:
      %LWire.pw6.nat(k, Wr.put_nat(f, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(k), LawsBase.wire_fits(f), h)) : {FW.get_blk.res(_) == Wr.Got{Pr.Res{k, f}, rest} : Wr.Dec<Pr.Blk>}
      %LWire.pw6.nat(f, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(k), LawsBase.wire_fits(f), h)) : {FW.get_blk.res.fp(k, _) == Wr.Got{Pr.Res{k, f}, rest} : Wr.Dec<Pr.Blk>}
      {==}
    case Pr.Txt{}:
      {==}
    case Pr.Think{}:
      {==}
    case Pr.User{}:
      {==}
    case Pr.Sys{}:
      {==}

# the items of a list of blocks, then rest
def wk.b.items(xs: List<&2, Pr.Blk>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      Work.wk_spell_blk(x, wk.b.items(t, rest))

def wk.b.put_go(xs: List<&2, Pr.Blk>, +rest: String) -> {Wr.put_list.go(~Pr.Blk, ~Work.wk_spell_blk, xs, rest) == (List.length(&2, Pr.Blk, xs), wk.b.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Pr.Blk, ~Work.wk_spell_blk, t, rest), (List.length(&2, Pr.Blk, t), wk.b.items(t, rest)), wk.b.put_go(t, rest)) : {Wr.put_list.step(~Pr.Blk, ~Work.wk_spell_blk, x, _) == (1n+List.length(&2, Pr.Blk, t), Work.wk_spell_blk(x, wk.b.items(t, rest))) : Nat & String}
      {==}

# a list of blocks is its count, then its items
def wk.b.put_list(+xs: List<&2, Pr.Blk>, +rest: String) -> {Wr.put_list(~Pr.Blk, ~Work.wk_spell_blk, xs, rest) == Wr.put_nat(List.length(&2, Pr.Blk, xs), wk.b.items(xs, rest)) : String}:
  Equal.cong(Nat & String, String, x => Wr.put_list.fin(x), Wr.put_list.go(~Pr.Blk, ~Work.wk_spell_blk, xs, rest), (List.length(&2, Pr.Blk, xs), wk.b.items(xs, rest)), wk.b.put_go(xs, rest))

def wk.b.fit_l(x: Pr.Blk, -xs: List<&2, Pr.Blk>, h: {Work.wk_blks_fit(x <> xs) == True{} : Bool}) -> {Work.wk_blk_fits(x) == True{} : Bool}:
  LLogicBool.wr_and_l(Work.wk_blk_fits(x), Work.wk_blks_fit(xs), h)

def wk.b.fit_r(x: Pr.Blk, -xs: List<&2, Pr.Blk>, h: {Work.wk_blks_fit(x <> xs) == True{} : Bool}) -> {Work.wk_blks_fit(xs) == True{} : Bool}:
  LLogicBool.wr_and_r(Work.wk_blk_fits(x), Work.wk_blks_fit(xs), h)

def wk.b.list_go(xs: List<&2, Pr.Blk>, +x: Pr.Blk, +rest: String, +hf: {Work.wk_blks_fit(x <> xs) == True{} : Bool}) -> {Wr.get_list.go(~Pr.Blk, ~FW.get_blk, List.length(&2, Pr.Blk, xs), FW.get_blk(Work.wk_spell_blk(x, wk.b.items(xs, rest)))) == Wr.Got{x <> xs, rest} : Wr.Dec<List<&2, Pr.Blk>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Pr.Blk>, FW.get_blk(Work.wk_spell_blk(x, rest)), Wr.Got{x, rest}, wk.blk_rt(x, rest, wk.b.fit_l(x, Nil{}, hf))) : {Wr.get_list.go(~Pr.Blk, ~FW.get_blk, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Pr.Blk>>}
      {==}
    case +x2 <> +xs2:
      %Equal.sym(Wr.Dec<Pr.Blk>, FW.get_blk(Work.wk_spell_blk(x, wk.b.items(x2 <> xs2, rest))), Wr.Got{x, wk.b.items(x2 <> xs2, rest)}, wk.blk_rt(x, wk.b.items(x2 <> xs2, rest), wk.b.fit_l(x, x2 <> xs2, hf))) : {Wr.get_list.go(~Pr.Blk, ~FW.get_blk, 1n+List.length(&2, Pr.Blk, xs2), _) == Wr.Got{x <> x2 <> xs2, rest} : Wr.Dec<List<&2, Pr.Blk>>}
      %Equal.sym(Wr.Dec<List<&2, Pr.Blk>>, Wr.get_list.go(~Pr.Blk, ~FW.get_blk, List.length(&2, Pr.Blk, xs2), FW.get_blk(Work.wk_spell_blk(x2, wk.b.items(xs2, rest)))), Wr.Got{x2 <> xs2, rest}, wk.b.list_go(xs2, x2, rest, wk.b.fit_r(x, x2 <> xs2, hf))) : {Wr.get_list.cons(Pr.Blk, x, _) == Wr.Got{x <> x2 <> xs2, rest} : Wr.Dec<List<&2, Pr.Blk>>}
      {==}

def wk.b.list_start(xs: List<&2, Pr.Blk>, +rest: String, +hf: {Work.wk_blks_fit(xs) == True{} : Bool}) -> {Wr.get_list.start(~Pr.Blk, ~FW.get_blk, Wr.Got{List.length(&2, Pr.Blk, xs), wk.b.items(xs, rest)}) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Pr.Blk>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      wk.b.list_go(t, x, rest, hf)

# a list of blocks that fits reads back
def wk.b.list_rt(+xs: List<&2, Pr.Blk>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, Pr.Blk, xs)) == True{} : Bool}, +hf: {Work.wk_blks_fit(xs) == True{} : Bool}) -> {Wr.get_list(~Pr.Blk, ~FW.get_blk, Wr.put_list(~Pr.Blk, ~Work.wk_spell_blk, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Pr.Blk>>}:
  %Equal.sym(String, Wr.put_list(~Pr.Blk, ~Work.wk_spell_blk, xs, rest), Wr.put_nat(List.length(&2, Pr.Blk, xs), wk.b.items(xs, rest)), wk.b.put_list(xs, rest)) : {Wr.get_list(~Pr.Blk, ~FW.get_blk, _) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Pr.Blk>>}
  %LWire.pw6.nat(List.length(&2, Pr.Blk, xs), wk.b.items(xs, rest), hl) : {Wr.get_list.start(~Pr.Blk, ~FW.get_blk, _) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Pr.Blk>>}
  wk.b.list_start(xs, rest, hf)

def wk.ent_rt(e: Pr.Ent, +rest: String, +h: {Work.wk_ent_fits(e) == True{} : Bool}) -> {FW.get_ent(Work.wk_spell_ent(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Pr.Ent>}:
  match e:
    case Pr.Ent{+i, +bs}:
      +lf = Bool.and(LawsBase.wire_fits(List.length(&2, Pr.Blk, bs)), Work.wk_blks_fit(bs))
      +hr = LLogicBool.wr_and_r(LawsBase.wire_fits(i), lf, h)
      %LWire.pw6.nat(i, Wr.put_list(~Pr.Blk, ~Work.wk_spell_blk, bs, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(i), lf, h)) : {FW.get_ent.go(_) == Wr.Got{Pr.Ent{i, bs}, rest} : Wr.Dec<Pr.Ent>}
      %Equal.sym(Wr.Dec<List<&2, Pr.Blk>>, Wr.get_list(~Pr.Blk, ~FW.get_blk, Wr.put_list(~Pr.Blk, ~Work.wk_spell_blk, bs, rest)), Wr.Got{bs, rest}, wk.b.list_rt(bs, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Pr.Blk, bs)), Work.wk_blks_fit(bs), hr), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Pr.Blk, bs)), Work.wk_blks_fit(bs), hr))) : {FW.get_ent.bs(i, _) == Wr.Got{Pr.Ent{i, bs}, rest} : Wr.Dec<Pr.Ent>}
      {==}

# the items of a list of entries, then rest
def wk.e.items(xs: List<&2, Pr.Ent>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      Work.wk_spell_ent(x, wk.e.items(t, rest))

def wk.e.put_go(xs: List<&2, Pr.Ent>, +rest: String) -> {Wr.put_list.go(~Pr.Ent, ~Work.wk_spell_ent, xs, rest) == (List.length(&2, Pr.Ent, xs), wk.e.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Pr.Ent, ~Work.wk_spell_ent, t, rest), (List.length(&2, Pr.Ent, t), wk.e.items(t, rest)), wk.e.put_go(t, rest)) : {Wr.put_list.step(~Pr.Ent, ~Work.wk_spell_ent, x, _) == (1n+List.length(&2, Pr.Ent, t), Work.wk_spell_ent(x, wk.e.items(t, rest))) : Nat & String}
      {==}

# a list of entries is its count, then its items
def wk.e.put_list(+xs: List<&2, Pr.Ent>, +rest: String) -> {Wr.put_list(~Pr.Ent, ~Work.wk_spell_ent, xs, rest) == Wr.put_nat(List.length(&2, Pr.Ent, xs), wk.e.items(xs, rest)) : String}:
  Equal.cong(Nat & String, String, x => Wr.put_list.fin(x), Wr.put_list.go(~Pr.Ent, ~Work.wk_spell_ent, xs, rest), (List.length(&2, Pr.Ent, xs), wk.e.items(xs, rest)), wk.e.put_go(xs, rest))

def wk.e.fit_l(x: Pr.Ent, -xs: List<&2, Pr.Ent>, h: {Work.wk_ents_fit(x <> xs) == True{} : Bool}) -> {Work.wk_ent_fits(x) == True{} : Bool}:
  LLogicBool.wr_and_l(Work.wk_ent_fits(x), Work.wk_ents_fit(xs), h)

def wk.e.fit_r(x: Pr.Ent, -xs: List<&2, Pr.Ent>, h: {Work.wk_ents_fit(x <> xs) == True{} : Bool}) -> {Work.wk_ents_fit(xs) == True{} : Bool}:
  LLogicBool.wr_and_r(Work.wk_ent_fits(x), Work.wk_ents_fit(xs), h)

def wk.e.list_go(xs: List<&2, Pr.Ent>, +x: Pr.Ent, +rest: String, +hf: {Work.wk_ents_fit(x <> xs) == True{} : Bool}) -> {Wr.get_list.go(~Pr.Ent, ~FW.get_ent, List.length(&2, Pr.Ent, xs), FW.get_ent(Work.wk_spell_ent(x, wk.e.items(xs, rest)))) == Wr.Got{x <> xs, rest} : Wr.Dec<List<&2, Pr.Ent>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Pr.Ent>, FW.get_ent(Work.wk_spell_ent(x, rest)), Wr.Got{x, rest}, wk.ent_rt(x, rest, wk.e.fit_l(x, Nil{}, hf))) : {Wr.get_list.go(~Pr.Ent, ~FW.get_ent, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Pr.Ent>>}
      {==}
    case +x2 <> +xs2:
      %Equal.sym(Wr.Dec<Pr.Ent>, FW.get_ent(Work.wk_spell_ent(x, wk.e.items(x2 <> xs2, rest))), Wr.Got{x, wk.e.items(x2 <> xs2, rest)}, wk.ent_rt(x, wk.e.items(x2 <> xs2, rest), wk.e.fit_l(x, x2 <> xs2, hf))) : {Wr.get_list.go(~Pr.Ent, ~FW.get_ent, 1n+List.length(&2, Pr.Ent, xs2), _) == Wr.Got{x <> x2 <> xs2, rest} : Wr.Dec<List<&2, Pr.Ent>>}
      %Equal.sym(Wr.Dec<List<&2, Pr.Ent>>, Wr.get_list.go(~Pr.Ent, ~FW.get_ent, List.length(&2, Pr.Ent, xs2), FW.get_ent(Work.wk_spell_ent(x2, wk.e.items(xs2, rest)))), Wr.Got{x2 <> xs2, rest}, wk.e.list_go(xs2, x2, rest, wk.e.fit_r(x, x2 <> xs2, hf))) : {Wr.get_list.cons(Pr.Ent, x, _) == Wr.Got{x <> x2 <> xs2, rest} : Wr.Dec<List<&2, Pr.Ent>>}
      {==}

def wk.e.list_start(xs: List<&2, Pr.Ent>, +rest: String, +hf: {Work.wk_ents_fit(xs) == True{} : Bool}) -> {Wr.get_list.start(~Pr.Ent, ~FW.get_ent, Wr.Got{List.length(&2, Pr.Ent, xs), wk.e.items(xs, rest)}) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Pr.Ent>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      wk.e.list_go(t, x, rest, hf)

# a list of entries that fits reads back
def wk.e.list_rt(+xs: List<&2, Pr.Ent>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, Pr.Ent, xs)) == True{} : Bool}, +hf: {Work.wk_ents_fit(xs) == True{} : Bool}) -> {Wr.get_list(~Pr.Ent, ~FW.get_ent, Wr.put_list(~Pr.Ent, ~Work.wk_spell_ent, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Pr.Ent>>}:
  %Equal.sym(String, Wr.put_list(~Pr.Ent, ~Work.wk_spell_ent, xs, rest), Wr.put_nat(List.length(&2, Pr.Ent, xs), wk.e.items(xs, rest)), wk.e.put_list(xs, rest)) : {Wr.get_list(~Pr.Ent, ~FW.get_ent, _) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Pr.Ent>>}
  %LWire.pw6.nat(List.length(&2, Pr.Ent, xs), wk.e.items(xs, rest), hl) : {Wr.get_list.start(~Pr.Ent, ~FW.get_ent, _) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Pr.Ent>>}
  wk.e.list_start(xs, rest, hf)

def wk.at_rt(m: Maybe<&2, Nat>, +rest: String, h: {LawsBase.core_mfits(m) == True{} : Bool}) -> {FW.get_at(Work.wk_spell_at(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %LWire.pw6.nat(x, rest, h) : {FW.get_at.some(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, Nat>>}
      {==}

# an event the laws spell reads back
def wk.ev_rt(e: Pr.Ev, +rest: String, +h: {Work.wk_ev_fits(e) == True{} : Bool}) -> {FW.get_ev(Work.wk_spell_ev(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Pr.Ev>}:
  match e:
    case Pr.View{+at, +es}:
      +x = Wr.put_list(~Pr.Ent, ~Work.wk_spell_ent, es, rest)
      +lf = Bool.and(LawsBase.wire_fits(List.length(&2, Pr.Ent, es)), Work.wk_ents_fit(es))
      +hr = LLogicBool.wr_and_r(LawsBase.core_mfits(at), lf, h)
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, FW.get_at(Work.wk_spell_at(at, x)), Wr.Got{at, x}, wk.at_rt(at, x, LLogicBool.wr_and_l(LawsBase.core_mfits(at), lf, h))) : {FW.get_ev.at(_) == Wr.Got{Pr.View{at, es}, rest} : Wr.Dec<Pr.Ev>}
      %Equal.sym(Wr.Dec<List<&2, Pr.Ent>>, Wr.get_list(~Pr.Ent, ~FW.get_ent, x), Wr.Got{es, rest}, wk.e.list_rt(es, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Pr.Ent, es)), Work.wk_ents_fit(es), hr), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Pr.Ent, es)), Work.wk_ents_fit(es), hr))) : {FW.get_ev.view(at, _) == Wr.Got{Pr.View{at, es}, rest} : Wr.Dec<Pr.Ev>}
      {==}
    case Pr.Page{+es}:
      %Equal.sym(Wr.Dec<List<&2, Pr.Ent>>, Wr.get_list(~Pr.Ent, ~FW.get_ent, Wr.put_list(~Pr.Ent, ~Work.wk_spell_ent, es, rest)), Wr.Got{es, rest}, wk.e.list_rt(es, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Pr.Ent, es)), Work.wk_ents_fit(es), h), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Pr.Ent, es)), Work.wk_ents_fit(es), h))) : {FW.get_ev.page(_) == Wr.Got{Pr.Page{es}, rest} : Wr.Dec<Pr.Ev>}
      {==}
    case Pr.Note{+x}:
      %LWire.pw6.nat(x, rest, h) : {FW.get_ev.note(_) == Wr.Got{Pr.Note{x}, rest} : Wr.Dec<Pr.Ev>}
      {==}

# The replies
# -----------

# the entry's step writes the reply the laws spell
def wk.out(r: Pr.Led & Pr.Out) -> {FW.step.out(r) == Work.wk_spell_step(r) : FW.St & String}:
  match r:
    case (l, o):
      match o:
        case Pr.Read{w, n, z}:
          match z:
            case None{}:
              {==}
            case Some{x}:
              {==}
        case Pr.Again{}:
          {==}

# an event the laws spell steps the entry as the model steps it
def wk.step(+l: Pr.Led, +e: Pr.Ev, h: {Work.wk_ev_fits(e) == True{} : Bool}) -> {FW.step(FW.Live{l}, Work.wk_spell_ev(e, "")) == Work.wk_spell_step(Pr.next(l, e)) : FW.St & String}:
  %Equal.sym(Wr.Dec<Pr.Ev>, FW.get_ev(Work.wk_spell_ev(e, "")), Wr.Got{e, ""}, wk.ev_rt(e, "", h)) : {FW.step.ev(l, _) == Work.wk_spell_step(Pr.next(l, e)) : FW.St & String}
  wk.out(Pr.next(l, e))

# The numbers of the acts
# -----------------------

def wt.refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      wt.refl(p)

def wt.and_true(b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# doubling keeps equality
def wt.dbl(a: Nat, b: Nat) -> {Nat.is_eq(Nat.double(a), Nat.double(b)) == Nat.is_eq(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      wt.dbl(p, q)

# an even number is never odd
def wt.eo(a: Nat, b: Nat) -> {Nat.is_eq(Nat.double(a), 1n+Nat.double(b)) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      wt.eo(p, q)

# an odd number is never even
def wt.oe(a: Nat, b: Nat) -> {Nat.is_eq(1n+Nat.double(a), Nat.double(b)) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      wt.oe(p, q)

# two towers are equal exactly when their heights and their bottoms are
def wt.tower(j: Nat, k: Nat, +n: Nat, +m: Nat) -> {Nat.is_eq(Pr.tower(j, n), Pr.tower(k, m)) == Bool.and(Nat.is_eq(j, k), Nat.is_eq(n, m)) : Bool}:
  match j k:
    case 0n 0n:
      wt.dbl(n, m)
    case 0n 1n+kq:
      wt.eo(n, Pr.tower(kq, m))
    case 1n+jp 0n:
      wt.oe(Pr.tower(jp, n), m)
    case 1n++jp 1n++kq:
      Equal.trans(Bool, Nat.is_eq(Nat.double(Pr.tower(jp, n)), Nat.double(Pr.tower(kq, m))), Nat.is_eq(Pr.tower(jp, n), Pr.tower(kq, m)), Bool.and(Nat.is_eq(jp, kq), Nat.is_eq(n, m)), wt.dbl(Pr.tower(jp, n), Pr.tower(kq, m)), wt.tower(jp, kq, n, m))

# two results' numbers are equal exactly when the results are the same act
def wt.res(m: Maybe<&2, Nat>, n: Maybe<&2, Nat>, +r: Nat, +x: Nat) -> {Nat.is_eq(Pr.act(m, r), Pr.act(n, x)) == Bool.and(Pr.meq(m, n), Nat.is_eq(r, x)) : Bool}:
  match m n:
    case None{} None{}:
      wt.tower(1n, 1n, r, x)
    case None{} Some{d}:
      wt.tower(1n, 2n+d, r, x)
    case Some{c} None{}:
      wt.tower(2n+c, 1n, r, x)
    case Some{c} Some{d}:
      wt.tower(2n+c, 2n+d, r, x)

def wt.res_note(m: Maybe<&2, Nat>, +r: Nat, +y: Nat) -> {Nat.is_eq(Pr.act(m, r), Pr.note(y)) == False{} : Bool}:
  match m:
    case None{}:
      wt.tower(1n, 0n, r, y)
    case Some{c}:
      wt.tower(2n+c, 0n, r, y)

def wt.note_res(+x: Nat, n: Maybe<&2, Nat>, +y: Nat) -> {Nat.is_eq(Pr.note(x), Pr.act(n, y)) == False{} : Bool}:
  match n:
    case None{}:
      wt.tower(0n, 1n, x, y)
    case Some{d}:
      wt.tower(0n, 2n+d, x, y)

# two acts' numbers are equal exactly when they are the same act
def wt.num(a: Pr.Act, b: Pr.Act) -> {Nat.is_eq(Work.wk_num(a), Work.wk_num(b)) == Pr.Act.same(a, b) : Bool}:
  match a b:
    case Pr.ARes{m, r} Pr.ARes{n, x}:
      wt.res(m, n, r, x)
    case Pr.ARes{m, r} Pr.ANote{y}:
      wt.res_note(m, r, y)
    case Pr.ANote{x} Pr.ARes{n, y}:
      wt.note_res(x, n, y)
    case Pr.ANote{x} Pr.ANote{y}:
      wt.tower(0n, 0n, x, y)
