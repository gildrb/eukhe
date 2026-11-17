# eukhe: lemmas the proofs of area irreversible share: Bools and Nats,
# lists, what finding a key answers, what recording does to the ledger,
# and the entry: a request read back, the reply spelled

import Base
import ../../bend/irreversible.bend as Ir
import ../../bend/ffi_irreversible.bend as FIr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/irreversible.bend as Irreversible
import ../base/staging.bend as LStg
import ../base/wire.bend as LWire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/wire_bool_not_err.bend as PWireBoolNotErr

# Bools and Nats
# --------------

def irb.or_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def irb.or_false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def irb.or_false_l(+a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      LStg.stg.absurd({True{} == False{} : Bool}, e)

def irb.or_false_r(+a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      LStg.stg.absurd({b == False{} : Bool}, e)

def irb.or_true_r(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def irb.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      irb.eq_refl(p)

def irb.eq_comm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      irb.eq_comm(p, q)

def irb.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LStg.stg.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LStg.stg.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, p, q, irb.eq_true(p, q, h))

def irb.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %irb.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def irb.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %irb.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# a + 1 is 1 + a
def irb.add_one(+a: Nat) -> {Nat.add(a, 1n) == 1n+a : Nat}:
  %irb.add_zero(a) : {Nat.add(a, 1n) == 1n+_ : Nat}
  irb.add_succ(a, 0n)

# Lists
# -----

def irb.app_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %irb.app_nil(A, t) : {x <> List.append(&2, A, t, Nil{}) == x <> _ : List<&2, A>}
      {==}

def irb.app_assoc(-A: Data, xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %irb.app_assoc(A, t, ys, zs) : {x <> List.append(&2, A, List.append(&2, A, t, ys), zs) == x <> _ : List<&2, A>}
      {==}

def irb.len_last(es: List<&2, Ir.Entry>, -x: Ir.Entry) -> {List.length(&2, Ir.Entry, List.append(&2, Ir.Entry, es, [x])) == 1n+List.length(&2, Ir.Entry, es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> +t:
      %irb.len_last(t, x) : {1n+List.length(&2, Ir.Entry, List.append(&2, Ir.Entry, t, [x])) == 1n+_ : Nat}
      {==}

# Finding a key
# -------------

# a ledger that lacks k: finding k answers None
def irb.fresh(es: List<&2, Ir.Entry>, +k: Nat, +at: Nat, +h: {Irreversible.ir_has(es, k) == False{} : Bool}) -> {Ir.find(es, k, at) == None{} : Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Ir.Entry{+j, +r}:
          +hj = irb.or_false_l(Nat.is_eq(j, k), Irreversible.ir_has(rest, k), h)
          +hr = irb.or_false_r(Nat.is_eq(j, k), Irreversible.ir_has(rest, k), h)
          %Equal.sym(Bool, Nat.is_eq(j, k), False{}, hj) : {Ir.find.go(Ir.Entry{j, r} <> rest, k, at, _) == None{} : Maybe<&2, Nat>}
          irb.fresh(rest, k, 1n+at, hr)

# a ledger whose first entry with key k comes after pre: finding k
# answers its id, counting from at
def irb.known(pre: List<&2, Ir.Entry>, +k: Nat, +q: Nat, +post: List<&2, Ir.Entry>, +at: Nat, +h: {Irreversible.ir_has(pre, k) == False{} : Bool}) -> {Ir.find(List.append(&2, Ir.Entry, pre, Ir.Entry{k, q} <> post), k, at) == Some{Nat.add(List.length(&2, Ir.Entry, pre), 1n+at)} : Maybe<&2, Nat>}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(k, k), True{}, irb.eq_refl(k)) : {Ir.find.go(Ir.Entry{k, q} <> post, k, at, _) == Some{1n+at} : Maybe<&2, Nat>}
      {==}
    case e <> +rest:
      match e:
        case Ir.Entry{+j, +r}:
          +hj = irb.or_false_l(Nat.is_eq(j, k), Irreversible.ir_has(rest, k), h)
          +hr = irb.or_false_r(Nat.is_eq(j, k), Irreversible.ir_has(rest, k), h)
          +n = List.length(&2, Ir.Entry, rest)
          %Equal.sym(Bool, Nat.is_eq(j, k), False{}, hj) : {Ir.find.go(Ir.Entry{j, r} <> List.append(&2, Ir.Entry, rest, Ir.Entry{k, q} <> post), k, at, _) == Some{1n+Nat.add(n, 1n+at)} : Maybe<&2, Nat>}
          %irb.add_succ(n, 1n+at) : {Ir.find(List.append(&2, Ir.Entry, rest, Ir.Entry{k, q} <> post), k, 1n+at) == Some{_} : Maybe<&2, Nat>}
          irb.known(rest, k, q, post, 1n+at, hr)

# a ledger that holds k: finding k answers some id (b: whether the first
# entry has key k)
def irb.found(es: List<&2, Ir.Entry>, +k: Nat, +at: Nat, b: Bool, eb: {Ir.key.at(es, k) == b : Bool}, h: {Irreversible.ir_has(es, k) == True{} : Bool}) -> Sigma<&1, &1, Nat, n => {Ir.find.go(es, k, at, b) == Some{n} : Maybe<&2, Nat>}>:
  match es:
    case Nil{}:
      LStg.stg.absurdF(Sigma<&1, &1, Nat, n => {Ir.find.go(Nil{}, k, at, b) == Some{n} : Maybe<&2, Nat>}>, h)
    case e <> +rest:
      match e:
        case Ir.Entry{+j, +r}:
          match b:
            case True{}:
              (1n+at, {==})
            case False{}:
              +hr = Equal.trans(Bool, Irreversible.ir_has(rest, k), Bool.or(Nat.is_eq(j, k), Irreversible.ir_has(rest, k)), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, Irreversible.ir_has(rest, k)), False{}, Nat.is_eq(j, k), Equal.sym(Bool, Nat.is_eq(j, k), False{}, eb)), h)
              irb.found(rest, k, 1n+at, Ir.key.at(rest, k), {==}, hr)

# Recording
# ---------

# a new key: recording answers the next id
def irb.rec_new(+es: List<&2, Ir.Entry>, +k: Nat, h: {Irreversible.ir_has(es, k) == False{} : Bool}) -> {Ir.record(es, k) == Ir.New{1n+List.length(&2, Ir.Entry, es)} : Ir.Recorded}:
  %Equal.sym(Maybe<&2, Nat>, Ir.find(es, k, 0n), None{}, irb.fresh(es, k, 0n, h)) : {Ir.record.of(_, es) == Ir.New{1n+List.length(&2, Ir.Entry, es)} : Ir.Recorded}
  {==}

# a new key: the ledger gets it last
def irb.keep_new(+es: List<&2, Ir.Entry>, +k: Nat, +r: Nat, h: {Irreversible.ir_has(es, k) == False{} : Bool}) -> {Ir.keep(es, k, r) == List.append(&2, Ir.Entry, es, [Ir.Entry{k, r}]) : List<&2, Ir.Entry>}:
  %Equal.sym(Maybe<&2, Nat>, Ir.find(es, k, 0n), None{}, irb.fresh(es, k, 0n, h)) : {Ir.keep.of(_, es, k, r) == List.append(&2, Ir.Entry, es, [Ir.Entry{k, r}]) : List<&2, Ir.Entry>}
  {==}

def irb.keep_known.of(+es: List<&2, Ir.Entry>, +k: Nat, +r: Nat, s: Sigma<&1, &1, Nat, n => {Ir.find(es, k, 0n) == Some{n} : Maybe<&2, Nat>}>) -> {Ir.keep(es, k, r) == es : List<&2, Ir.Entry>}:
  match s:
    case (n, e):
      %Equal.sym(Maybe<&2, Nat>, Ir.find(es, k, 0n), Some{n}, e) : {Ir.keep.of(_, es, k, r) == es : List<&2, Ir.Entry>}
      {==}

# a known key: the ledger stays
def irb.keep_known(+es: List<&2, Ir.Entry>, +k: Nat, +r: Nat, h: {Irreversible.ir_has(es, k) == True{} : Bool}) -> {Ir.keep(es, k, r) == es : List<&2, Ir.Entry>}:
  irb.keep_known.of(es, k, r, irb.found(es, k, 0n, Ir.key.at(es, k), {==}, h))

def irb.rec_known.of(+es: List<&2, Ir.Entry>, +k: Nat, s: Sigma<&1, &1, Nat, n => {Ir.find(es, k, 0n) == Some{n} : Maybe<&2, Nat>}>) -> Sigma<&1, &1, Nat, n => {Ir.record(es, k) == Ir.Known{n} : Ir.Recorded}>:
  match s:
    case (+n, e):
      (n, Equal.cong(Maybe<&2, Nat>, Ir.Recorded, z => Ir.record.of(z, es), Ir.find(es, k, 0n), Some{n}, e))

# a known key: recording answers some known id
def irb.rec_known(+es: List<&2, Ir.Entry>, +k: Nat, h: {Irreversible.ir_has(es, k) == True{} : Bool}) -> Sigma<&1, &1, Nat, n => {Ir.record(es, k) == Ir.Known{n} : Ir.Recorded}>:
  irb.rec_known.of(es, k, irb.found(es, k, 0n, Ir.key.at(es, k), {==}, h))

# a key k is among xs then ys exactly when it is among xs or among ys
def irb.has_app(xs: List<&2, Ir.Entry>, +ys: List<&2, Ir.Entry>, +k: Nat) -> {Irreversible.ir_has(List.append(&2, Ir.Entry, xs, ys), k) == Bool.or(Irreversible.ir_has(xs, k), Irreversible.ir_has(ys, k)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case Ir.Entry{+j, +q}:
          %Equal.sym(Bool, Irreversible.ir_has(List.append(&2, Ir.Entry, t, ys), k), Bool.or(Irreversible.ir_has(t, k), Irreversible.ir_has(ys, k)), irb.has_app(t, ys, k)) : {Bool.or(Nat.is_eq(j, k), _) == Bool.or(Bool.or(Nat.is_eq(j, k), Irreversible.ir_has(t, k)), Irreversible.ir_has(ys, k)) : Bool}
          irb.or_assoc(Nat.is_eq(j, k), Irreversible.ir_has(t, k), Irreversible.ir_has(ys, k))

def irb.and_l(+a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LStg.stg.absurdF({False{} == True{} : Bool}, h)

def irb.and_r(+a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LStg.stg.absurdF({b == True{} : Bool}, h)

# The entry
# ---------

# the ledger Rust writes reads back as the ledger
def irb.ledger_rt(es: List<&2, Ir.Entry>) -> {FIr.entries.of(Irreversible.sp_ir_ledger(es)) == Some{es} : Maybe<&2, List<&2, Ir.Entry>>}:
  match es:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case Ir.Entry{+k, +r}:
          %Equal.sym(Maybe<&2, List<&2, Ir.Entry>>, FIr.entries.of(Irreversible.sp_ir_ledger(t)), Some{t}, irb.ledger_rt(t)) : {FIr.entries.cons(k, r, _) == Some{Ir.Entry{k, r} <> t} : Maybe<&2, List<&2, Ir.Entry>>}
          {==}

def irb.LedgerOk(xs: List<&2, Nat>, m: Maybe<&2, List<&2, Ir.Entry>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{es}:
      {xs == Irreversible.sp_ir_ledger(es) : List<&2, Nat>}

def irb.ledger_cons(+k: Nat, +r: Nat, +more: List<&2, Nat>, m: Maybe<&2, List<&2, Ir.Entry>>, hm: irb.LedgerOk(more, m)) -> irb.LedgerOk(k <> r <> more, FIr.entries.cons(k, r, m)):
  match m:
    case None{}:
      Unit{}
    case Some{+es}:
      %hm : {k <> r <> more == k <> r <> _ : List<&2, Nat>}
      {==}

# a list that reads as a ledger is the ledger's spelling
def irb.ledger_exact(xs: List<&2, Nat>) -> irb.LedgerOk(xs, FIr.entries.of(xs)):
  match xs:
    case Nil{}:
      {==}
    case +k <> rest:
      match rest:
        case Nil{}:
          Unit{}
        case +r <> +more:
          irb.ledger_cons(k, r, more, FIr.entries.of(more), irb.ledger_exact(more))

# the request Rust writes reads back, the rest untouched
def irb.rt(q: FIr.Req, +rest: String, +fits: {Irreversible.ir_req_fits(q) == True{} : Bool}) -> {FIr.get_req(Irreversible.sp_ir_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FIr.Req>}:
  match q:
    case FIr.QClasses{+cs}:
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Irreversible.sp_ir_ns(cs, rest)), Wr.Got{cs, rest}, Wire.wire_list_round_trip(cs, rest, fits)) : {FIr.get_classes(_) == Wr.Got{FIr.QClasses{cs}, rest} : Wr.Dec<FIr.Req>}
      {==}
    case FIr.QRecord{+es, +k}:
      +l = Irreversible.sp_ir_ledger(es)
      +fl = irb.and_l(Irreversible.ir_ns_fit(l), LawsBase.wire_fits(k), fits)
      +fk = irb.and_r(Irreversible.ir_ns_fit(l), LawsBase.wire_fits(k), fits)
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Irreversible.sp_ir_ns(l, Wr.put_nat(k, rest))), Wr.Got{l, Wr.put_nat(k, rest)}, Wire.wire_list_round_trip(l, Wr.put_nat(k, rest), fl)) : {FIr.get_ledger(True{}, _) == Wr.Got{FIr.QRecord{es, k}, rest} : Wr.Dec<FIr.Req>}
      %Equal.sym(Maybe<&2, List<&2, Ir.Entry>>, FIr.entries.of(l), Some{es}, irb.ledger_rt(es)) : {FIr.get_ledger.then(True{}, _, Wr.put_nat(k, rest)) == Wr.Got{FIr.QRecord{es, k}, rest} : Wr.Dec<FIr.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(k, rest)), Wr.Got{k, rest}, Wire.wire_nat_round_trip(k, rest, fk)) : {FIr.get_record.key(es, _) == Wr.Got{FIr.QRecord{es, k}, rest} : Wr.Dec<FIr.Req>}
      {==}
    case FIr.QReport{+es, +r}:
      +l = Irreversible.sp_ir_ledger(es)
      +fl = irb.and_l(Irreversible.ir_ns_fit(l), LawsBase.wire_fits(r), fits)
      +fr = irb.and_r(Irreversible.ir_ns_fit(l), LawsBase.wire_fits(r), fits)
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Irreversible.sp_ir_ns(l, Wr.put_nat(r, rest))), Wr.Got{l, Wr.put_nat(r, rest)}, Wire.wire_list_round_trip(l, Wr.put_nat(r, rest), fl)) : {FIr.get_ledger(False{}, _) == Wr.Got{FIr.QReport{es, r}, rest} : Wr.Dec<FIr.Req>}
      %Equal.sym(Maybe<&2, List<&2, Ir.Entry>>, FIr.entries.of(l), Some{es}, irb.ledger_rt(es)) : {FIr.get_ledger.then(False{}, _, Wr.put_nat(r, rest)) == Wr.Got{FIr.QReport{es, r}, rest} : Wr.Dec<FIr.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(r, rest)), Wr.Got{r, rest}, Wire.wire_nat_round_trip(r, rest, fr)) : {FIr.get_report.run(es, _) == Wr.Got{FIr.QReport{es, r}, rest} : Wr.Dec<FIr.Req>}
      {==}

def irb.recorded(a: Ir.Recorded) -> {FIr.put_recorded(a, "") == Irreversible.sp_ir_recorded(a) : String}:
  match a:
    case Ir.New{n}:
      {==}
    case Ir.Known{n}:
      {==}

# the entry's reply is the laws' spelling of the model's answer
def irb.reply(q: FIr.Req) -> {FIr.answer(q) == Irreversible.sp_ir_reply(q) : String}:
  match q:
    case FIr.QClasses{cs}:
      {==}
    case FIr.QRecord{+es, +k}:
      irb.recorded(Ir.record(es, k))
    case FIr.QReport{es, r}:
      {==}

def irb.fin_not_err(p: Nat & String) -> {LawsBase.wire_opens_err(Wr.put_list.fin(p)) == False{} : Bool}:
  match p:
    case (n, s):
      Wire.wire_nat_not_err(n, s)

def irb.recorded_not_err(a: Ir.Recorded) -> {LawsBase.wire_opens_err(FIr.put_recorded(a, "")) == False{} : Bool}:
  match a:
    case Ir.New{n}:
      Wire.wire_nat_not_err(0n, Wr.put_nat(n, ""))
    case Ir.Known{n}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(n, ""))

# no answer of the model opens with the error mark
def irb.answer_ok(q: FIr.Req) -> {LawsBase.wire_opens_err(FIr.answer(q)) == False{} : Bool}:
  match q:
    case FIr.QClasses{cs}:
      Wire.wire_bool_not_err(Ir.irreversible(cs), "")
    case FIr.QRecord{+es, +k}:
      irb.recorded_not_err(Ir.record(es, k))
    case FIr.QReport{+es, +r}:
      irb.fin_not_err(Wr.put_list.go(~Nat, ~Wr.put_nat, Ir.report(es, r), ""))
