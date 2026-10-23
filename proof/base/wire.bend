# eukhe: lemmas the proofs of two or more areas share: wire

import Base
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ./list.bend as LList
import ./logic/bool.bend as LLogicBool
import ./logic/list.bend as LLogicList
import ./logic/logic.bend as LLogicLogic
import ./logic/nat.bend as LLogicNat
import ./logic/string.bend as LLogicString
import ./logic/wire.bend as LLogicWire
import ./nat.bend as LNat
import ./pair.bend as LPair
import ./string.bend as LString

# a digit below 10 reads back as itself
def wn_tok_dig(+d: Nat, h: {LLogicBool.wn_lt10(d) == True{} : Bool}) -> {Wr.tok(Wr.dchar(d)) == Wr.Dig{d} : Wr.Tok}:
  match d:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+p:
      LLogicLogic.wn_absurd({Wr.tok(Wr.dchar(10n+p)) == Wr.Dig{10n+p} : Wr.Tok}, h)

def wn_pe(g: Nat, +q: Nat, acc: String) -> {Wr.put_nat.go(g, q, acc) == LLogicString.wn_emit(LLogicList.wn_L(g, q), acc) : String}:
  match g:
    case 0n:
      {==}
    case 1n+f:
      match q:
        case 0n:
          {==}
        case 1n+p:
          wn_pe(f, Nat.div(1n+p, 10n), SCon{Wr.dchar(Nat.mod(1n+p, 10n)), acc})

# put_nat writes the chars of all the digits of n, then ',' and rest
def wn_put_emit(+n: Nat, rest: String) -> {Wr.put_nat(n, rest) == LLogicString.wn_emit(LLogicList.wn_full(n), SCon{',', rest}) : String}:
  wn_pe(n, Nat.div(n, 10n), SCon{Wr.dchar(Nat.mod(n, 10n)), SCon{',', rest}})

def wn_gc(k: Nat, ds: List<&2, Nat>, s: String) -> {LLogicWire.wo_go(k, (Wr.Comma{}, s), ds) == Wr.Got{LLogicNat.wo_value(ds), s} : Wr.Dec<Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}

def wn_gother(k: Nat, ds: List<&2, Nat>, s: String) -> {LLogicWire.wo_go(k, (Wr.Other{}, s), ds) == Wr.Bad{} : Wr.Dec<Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}

# The fast decoder equals the reference: the end of the digits
def wn_eq_end(t: Wr.Tok, s: String, -v: Nat, -ds: List<&2, Nat>, e: {v == LLogicNat.wo_value(ds) : Nat})
  -> {Wr.get_nat.end(t, s, v) == LLogicWire.wo_end((t, s), ds) : Wr.Dec<Nat>}:
  match t:
    case Wr.Dig{d}:
      {==}
    case Wr.Comma{}:
      %e : {Wr.Got{v, s} == Wr.Got{_, s} : Wr.Dec<Nat>}
      {==}
    case Wr.Other{}:
      {==}

# ... the loop over the digits, the value folded so far being worth ds
def wn_eq_go(k: Nat, t: Wr.Tok, s: String, +v: Nat, +ds: List<&2, Nat>, e: {v == LLogicNat.wo_value(ds) : Nat})
  -> {Wr.get_nat.go(k, t, s, v) == LLogicWire.wo_go(k, (t, s), ds) : Wr.Dec<Nat>}:
  match k:
    case 0n:
      wn_eq_end(t, s, v, ds, e)
    case 1n+j:
      match t:
        case Wr.Dig{+d}:
          match s:
            case SNil{}:
              Equal.sym(Wr.Dec<Nat>, LLogicWire.wo_go(j, (Wr.Other{}, SNil{}), d <> ds), Wr.Bad{}, wn_gother(j, d <> ds, SNil{}))
            case SCon{c, r}:
              wn_eq_go(j, Wr.tok(c), r, Nat.add(d, Nat.mul(10n, v)), d <> ds,
                Equal.cong(Nat, Nat, x => Nat.add(d, Nat.mul(10n, x)), v, LLogicNat.wo_value(ds), e))
        case Wr.Comma{}:
          %e : {Wr.Got{v, s} == Wr.Got{_, s} : Wr.Dec<Nat>}
          {==}
        case Wr.Other{}:
          {==}

def wn_eq_lead(d: Nat, t: Wr.Tok, s: String) -> {Wr.get_nat.lead(d, t, s) == LLogicWire.wo_lead(d, (t, s)) : Wr.Dec<Nat>}:
  match d:
    case 0n:
      wn_eq_end(t, s, 0n, [0n], {==})
    case 1n++p:
      wn_eq_go(13n, t, s, 1n+p, [1n+p], Equal.sym(Nat, Nat.add(1n+p, 0n), 1n+p, LNat.wn_add_zero_r(1n+p)))

def wn_eq_first(t: Wr.Tok, s: String) -> {Wr.get_nat.first(t, s) == LLogicWire.wo_first((t, s)) : Wr.Dec<Nat>}:
  match t:
    case Wr.Dig{d}:
      match d:
        case 0n:
          match s:
            case SNil{}:
              {==}
            case SCon{c, r}:
              wn_eq_lead(0n, Wr.tok(c), r)
        case 1n+p:
          match s:
            case SNil{}:
              {==}
            case SCon{c, r}:
              wn_eq_lead(1n+p, Wr.tok(c), r)
    case Wr.Comma{}:
      {==}
    case Wr.Other{}:
      {==}

# the fast decoder answers what the reference answers, on every input
def wn_eqv(s: String) -> {Wr.get_nat(s) == LLogicWire.wo_get_nat(s) : Wr.Dec<Nat>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, r}:
      wn_eq_first(Wr.tok(c), r)

def wn_f1_one(+d: Nat, x: String, +k: Nat, c: {LLogicBool.wn_nz10(d) == True{} : Bool}, e: {1n+k == 14n : Nat})
  -> {LLogicWire.wo_first(LLogicWire.wo_peek(LLogicString.wn_emit([d], x))) == LLogicWire.wo_go(k, LLogicWire.wo_peek(x), [d]) : Wr.Dec<Nat>}:
  match d:
    case 0n:
      LLogicLogic.wn_absurd({LLogicWire.wo_first(LLogicWire.wo_peek(LLogicString.wn_emit([0n], x))) == LLogicWire.wo_go(k, LLogicWire.wo_peek(x), [0n]) : Wr.Dec<Nat>}, c)
    case 1n+p:
      %Equal.sym(Nat, k, 13n, Equal.cong(Nat, Nat, LLogicNat.wn_pred, 1n+k, 14n, e)) : {LLogicWire.wo_first(LLogicWire.wo_peek(LLogicString.wn_emit([1n+p], x))) == LLogicWire.wo_go(_, LLogicWire.wo_peek(x), [1n+p]) : Wr.Dec<Nat>}
      %Equal.sym(Wr.Tok, Wr.tok(Wr.dchar(1n+p)), Wr.Dig{1n+p}, wn_tok_dig(1n+p, c)) : {LLogicWire.wo_first((_, x)) == LLogicWire.wo_go(13n, LLogicWire.wo_peek(x), [1n+p]) : Wr.Dec<Nat>}
      {==}

# a canonical list of at most 14 digits: the decoder reads all of it and
# has k digits left to read
def wn_f1(t: List<&2, Nat>, +d: Nat, +x: String, +k: Nat, +c: {LLogicBool.wn_okc(t, d) == True{} : Bool},
  e: {Nat.add(List.length(&2, Nat, d <> t), k) == 14n : Nat})
  -> {LLogicWire.wo_first(LLogicWire.wo_peek(LLogicString.wn_emit(d <> t, x))) == LLogicWire.wo_go(k, LLogicWire.wo_peek(x), d <> t) : Wr.Dec<Nat>}:
  match t:
    case Nil{}:
      wn_f1_one(d, x, k, c, e)
    case Con{+e2, +u}:
      +hd = LLogicBool.wn_and_l(LLogicBool.wn_lt10(d), LLogicBool.wn_okc(u, e2), c)
      +ih = wn_f1(u, e2, SCon{Wr.dchar(d), x}, 1n+k, LLogicBool.wn_and_r(LLogicBool.wn_lt10(d), LLogicBool.wn_okc(u, e2), c),
        Equal.trans(Nat, Nat.add(List.length(&2, Nat, e2 <> u), 1n+k), 1n+Nat.add(List.length(&2, Nat, e2 <> u), k), 14n,
          LNat.wn_add_succ_r(List.length(&2, Nat, e2 <> u), k), e))
      %Equal.sym(Wr.Dec<Nat>, LLogicWire.wo_first(LLogicWire.wo_peek(LLogicString.wn_emit(e2 <> u, SCon{Wr.dchar(d), x}))), LLogicWire.wo_go(1n+k, LLogicWire.wo_peek(SCon{Wr.dchar(d), x}), e2 <> u), ih) : {_ == LLogicWire.wo_go(k, LLogicWire.wo_peek(x), d <> (e2 <> u)) : Wr.Dec<Nat>}
      %Equal.sym(Wr.Tok, Wr.tok(Wr.dchar(d)), Wr.Dig{d}, wn_tok_dig(d, hd)) : {LLogicWire.wo_go(1n+k, (_, x), e2 <> u) == LLogicWire.wo_go(k, LLogicWire.wo_peek(x), d <> (e2 <> u)) : Wr.Dec<Nat>}
      {==}

def wn_rt(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {LLogicWire.wo_get_nat(Wr.put_nat(n, rest)) == Wr.Got{n, rest} : Wr.Dec<Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +hl = Equal.trans(Bool, Nat.is_le(List.length(&2, Nat, LLogicList.wn_full(1n+p)), 14n), Nat.is_le(LawsBase.wire_digits(1n+p), 14n), True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, 14n), List.length(&2, Nat, LLogicList.wn_full(1n+p)), LawsBase.wire_digits(1n+p),
          Equal.sym(Nat, LawsBase.wire_digits(1n+p), List.length(&2, Nat, LLogicList.wn_full(1n+p)), LList.wn_wl(1n+p))), h)
      +k = LLogicNat.wn_sub(14n, List.length(&2, Nat, LLogicList.wn_full(1n+p)))
      +f1 = wn_f1(LLogicList.wn_L(1n+p, Nat.div(1n+p, 10n)), Nat.mod(1n+p, 10n), SCon{',', rest}, k, LPair.wn_cf(p),
        LNat.wn_le_k(List.length(&2, Nat, LLogicList.wn_full(1n+p)), 14n, hl))
      %Equal.sym(String, Wr.put_nat(1n+p, rest), LLogicString.wn_emit(LLogicList.wn_full(1n+p), SCon{',', rest}), wn_put_emit(1n+p, rest)) : {LLogicWire.wo_get_nat(_) == Wr.Got{1n+p, rest} : Wr.Dec<Nat>}
      %Equal.sym(Wr.Dec<Nat>, LLogicWire.wo_first(LLogicWire.wo_peek(LLogicString.wn_emit(LLogicList.wn_full(1n+p), SCon{',', rest}))), LLogicWire.wo_go(k, LLogicWire.wo_peek(SCon{',', rest}), LLogicList.wn_full(1n+p)), f1) : {_ == Wr.Got{1n+p, rest} : Wr.Dec<Nat>}
      %Equal.sym(Wr.Dec<Nat>, LLogicWire.wo_go(k, (Wr.Comma{}, rest), LLogicList.wn_full(1n+p)), Wr.Got{LLogicNat.wo_value(LLogicList.wn_full(1n+p)), rest}, wn_gc(k, LLogicList.wn_full(1n+p), rest)) : {_ == Wr.Got{1n+p, rest} : Wr.Dec<Nat>}
      %LPair.wn_vf(1n+p) : {Wr.Got{LLogicNat.wo_value(LLogicList.wn_full(1n+p)), rest} == Wr.Got{_, rest} : Wr.Dec<Nat>}
      {==}

def Wire.wire_nat_round_trip(n, rest, h):
  +r = rest
  Equal.trans(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, r)), LLogicWire.wo_get_nat(Wr.put_nat(n, r)), Wr.Got{n, r},
    wn_eqv(Wr.put_nat(n, r)), wn_rt(n, r, h))

# put_str.go turns a around onto acc and adds its length to n
def wr_put_str_go(a: String, -acc: String, -n: Nat) ->
  {Wr.put_str.go(a, acc, n) == (Nat.add(String.length(a), n), String.reverse.go(a, acc)) : Nat & String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      %Equal.sym(Nat & String, Wr.put_str.go(t, SCon{c, acc}, 1n+n), (Nat.add(String.length(t), 1n+n), String.reverse.go(t, SCon{c, acc})), wr_put_str_go(t, SCon{c, acc}, 1n+n)) : {_ == (1n+Nat.add(String.length(t), n), String.reverse.go(t, SCon{c, acc})) : Nat & String}
      %LNat.wn_add_succ_r(String.length(t), n) : {(Nat.add(String.length(t), 1n+n), String.reverse.go(t, SCon{c, acc})) == (_, String.reverse.go(t, SCon{c, acc})) : Nat & String}
      {==}

# a string is its length, then its chars
def wr_put_str(+a: String, +rest: String) ->
  {Wr.put_str(a, rest) == Wr.put_nat(String.length(a), LLogicString.wr_app(a, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_str.go(a, SNil{}, 0n), (Nat.add(String.length(a), 0n), String.reverse.go(a, SNil{})), wr_put_str_go(a, SNil{}, 0n)) : {Wr.put_str.fin(_, rest) == Wr.put_nat(String.length(a), LLogicString.wr_app(a, rest)) : String}
  %Equal.sym(Nat, Nat.add(String.length(a), 0n), String.length(a), LNat.wn_add_zero_r(String.length(a))) : {Wr.put_nat(_, String.reverse.go(String.reverse.go(a, SNil{}), rest)) == Wr.put_nat(String.length(a), LLogicString.wr_app(a, rest)) : String}
  %Equal.sym(String, String.reverse.go(String.reverse.go(a, SNil{}), rest), LLogicString.wr_app(a, rest), LString.wr_rev_rev(a, SNil{}, rest)) : {Wr.put_nat(String.length(a), _) == Wr.put_nat(String.length(a), LLogicString.wr_app(a, rest)) : String}
  {==}

# the flat take.go answers the reference, with the chars read so far in front
def wr_take_go(n: Nat, s: String, +acc: String) -> {Wr.take.go(n, s, acc) == LLogicWire.wr_tfix(acc, LLogicWire.wo_take(n, s)) : Wr.Dec<String>}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      match s:
        case SNil{}:
          {==}
        case SCon{+c, +t}:
          Equal.trans(Wr.Dec<String>, Wr.take.go(m, t, SCon{c, acc}), LLogicWire.wr_tfix(SCon{c, acc}, LLogicWire.wo_take(m, t)), LLogicWire.wr_tfix(acc, LLogicWire.wo_take_cons(c, LLogicWire.wo_take(m, t))),
            wr_take_go(m, t, SCon{c, acc}), LLogicWire.wr_tfix_cons(acc, c, LLogicWire.wo_take(m, t)))

# take answers what the reference answers
def wr_take_eq(+n: Nat, +s: String) -> {Wr.take(n, s) == LLogicWire.wo_take(n, s) : Wr.Dec<String>}:
  Equal.trans(Wr.Dec<String>, Wr.take.go(n, s, SNil{}), LLogicWire.wr_tfix(SNil{}, LLogicWire.wo_take(n, s)), LLogicWire.wo_take(n, s),
    wr_take_go(n, s, SNil{}), LLogicWire.wr_tfix_nil(LLogicWire.wo_take(n, s)))

# Nat laws used as lemmas (proved in the Nat slice)
def Wire.wire_str_round_trip(a, rest, h):
  +r = rest
  %Equal.sym(String, Wr.put_str(a, r), Wr.put_nat(String.length(a), LLogicString.wr_app(a, r)), wr_put_str(a, r)) : {Wr.get_str(_) == Wr.Got{a, r} : Wr.Dec<String>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(String.length(a), LLogicString.wr_app(a, r))), Wr.Got{String.length(a), LLogicString.wr_app(a, r)}, Wire.wire_nat_round_trip(String.length(a), LLogicString.wr_app(a, r), h)) : {Wr.get_str.go(_) == Wr.Got{a, r} : Wr.Dec<String>}
  Equal.trans(Wr.Dec<String>, Wr.take(String.length(a), LLogicString.wr_app(a, r)), LLogicWire.wo_take(String.length(a), LLogicString.wr_app(a, r)), Wr.Got{a, r},
    wr_take_eq(String.length(a), LLogicString.wr_app(a, r)), LString.wr_take_rt(a, r))

def wr_put_list_go(xs: List<&2, Nat>, -rest: String) ->
  {Wr.put_list.go(~Nat, ~Wr.put_nat, xs, rest) == (List.length(&2, Nat, xs), LLogicString.wr_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Nat, ~Wr.put_nat, t, rest), (List.length(&2, Nat, t), LLogicString.wr_items(t, rest)), wr_put_list_go(t, rest)) : {Wr.put_list.step(~Nat, ~Wr.put_nat, x, _) == (1n+List.length(&2, Nat, t), Wr.put_nat(x, LLogicString.wr_items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def wr_put_list(+xs: List<&2, Nat>, -rest: String) ->
  {Wr.put_list(~Nat, ~Wr.put_nat, xs, rest) == Wr.put_nat(List.length(&2, Nat, xs), LLogicString.wr_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Nat, ~Wr.put_nat, xs, rest), (List.length(&2, Nat, xs), LLogicString.wr_items(xs, rest)), wr_put_list_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Nat, xs), LLogicString.wr_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def wr_list_go_rt(+t: List<&2, Nat>, +x: Nat, +rest: String,
  +hf: {LawsBase.wire_nats_fit(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Nat, ~Wr.get_nat, List.length(&2, Nat, t), Wr.get_nat(Wr.put_nat(x, LLogicString.wr_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Nat>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(x, rest)), Wr.Got{x, rest}, Wire.wire_nat_round_trip(x, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(x), True{}, hf))) : {Wr.get_list.go(~Nat, ~Wr.get_nat, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Nat>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(x, Wr.put_nat(y, LLogicString.wr_items(u, rest)))), Wr.Got{x, Wr.put_nat(y, LLogicString.wr_items(u, rest))}, Wire.wire_nat_round_trip(x, Wr.put_nat(y, LLogicString.wr_items(u, rest)), LLogicBool.wr_and_l(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(y <> u), hf))) : {Wr.get_list.go(~Nat, ~Wr.get_nat, 1n+List.length(&2, Nat, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Nat>>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list.go(~Nat, ~Wr.get_nat, List.length(&2, Nat, u), Wr.get_nat(Wr.put_nat(y, LLogicString.wr_items(u, rest)))), Wr.Got{y <> u, rest}, wr_list_go_rt(u, y, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(y <> u), hf))) : {Wr.get_list.cons(Nat, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Nat>>}
      {==}

def Wire.wire_list_round_trip(xs, rest, h):
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Nat, ~Wr.get_nat, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Nat>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, x <> t, r), Wr.put_nat(List.length(&2, Nat, x <> t), LLogicString.wr_items(x <> t, r)), wr_put_list(x <> t, r)) : {Wr.get_list(~Nat, ~Wr.get_nat, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Nat>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Nat, x <> t), LLogicString.wr_items(x <> t, r))), Wr.Got{List.length(&2, Nat, x <> t), LLogicString.wr_items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Nat, x <> t), LLogicString.wr_items(x <> t, r), LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Nat, x <> t)), LawsBase.wire_nats_fit(x <> t), hh))) : {Wr.get_list.start(~Nat, ~Wr.get_nat, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Nat>>}
      wr_list_go_rt(t, x, r, LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Nat, x <> t)), LawsBase.wire_nats_fit(x <> t), hh))

# ---- core_w6 ----

# proof_core_w6: the entries of the child task, the jobs, the goal's check
# and the hand-back (LAWS.bend section core_w6). Each decoder reads back
# what its encoder wrote (pw6.*, from the wire laws), so the entry runs
# the model on the request's values.

def pw6.nat(+n: Nat, +rest: String, +h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

# ---- core entries ----

# Place after PROOF.bend section wire: the proofs use its Laws.wire_*
# fills and wr_and_l / wr_and_r. Every lemma here is turned around
# ({Got{x, rest} == get(put(x, rest))}) so that it rewrites a decoder of an
# encoding into its value.

# a Nat that fits reads back (Laws.wire_nat_round_trip, turned around)
def pc.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

# (D1) the orphan and restart-budget entries of the compiled core (they
# follow the wire section: they build on its laws)

# the wire round trips, turned to rewrite a decode of an encoding into
# its value
def ps.ffi_nat(+n: Nat, +r: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, r} == Wr.get_nat(Wr.put_nat(n, r)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, r)), Wr.Got{n, r}, Wire.wire_nat_round_trip(n, r, h))

def fe.lists_back(t: List<&2, List<&2, Nat>>) -> {Fl.St.lists(LLogicWire.fe.lists_of(t)) == t : List<&2, List<&2, Nat>>}:
  match t:
    case Nil{}:
      {==}
    case xs <> d:
      {==}

# a list in front of the lists t decodes to the open list xs before t
def fe.one_fold(xs: List<&2, Nat>, +t: List<&2, List<&2, Nat>>, h: {Fl.fold(Fl.flat(t)) == Some{LLogicWire.fe.lists_of(t)} : Maybe<&2, Fl.St>}) -> {Fl.fold(Fl.one(xs, Fl.flat(t))) == Some{Fl.Mid{xs, t}} : Maybe<&2, Fl.St>}:
  match xs:
    case Nil{}:
      %Equal.sym(Maybe<&2, Fl.St>, Fl.fold(Fl.flat(t)), Some{LLogicWire.fe.lists_of(t)}, h) : {Fl.step(0n, _) == Some{Fl.Mid{Nil{}, t}} : Maybe<&2, Fl.St>}
      %Equal.sym(List<&2, List<&2, Nat>>, Fl.St.lists(LLogicWire.fe.lists_of(t)), t, fe.lists_back(t)) : {Some{Fl.Mid{Nil{}, _}} == Some{Fl.Mid{Nil{}, t}} : Maybe<&2, Fl.St>}
      {==}
    case +x <> +r:
      %Equal.sym(Maybe<&2, Fl.St>, Fl.fold(Fl.one(r, Fl.flat(t))), Some{Fl.Mid{r, t}}, fe.one_fold(r, t, h)) : {Fl.step({1n+x : Nat}, _) == Some{Fl.Mid{x <> r, t}} : Maybe<&2, Fl.St>}
      {==}

def fe.fold_flat(xss: List<&2, List<&2, Nat>>) -> {Fl.fold(Fl.flat(xss)) == Some{LLogicWire.fe.lists_of(xss)} : Maybe<&2, Fl.St>}:
  match xss:
    case Nil{}:
      {==}
    case xs <> +t:
      fe.one_fold(xs, t, fe.fold_flat(t))

# lists of lists read back from their flat list
def fe.unflat_flat(+xss: List<&2, List<&2, Nat>>) -> {Fl.unflat(Fl.flat(xss)) == Some{xss} : Maybe<&2, List<&2, List<&2, Nat>>>}:
  %Equal.sym(Maybe<&2, Fl.St>, Fl.fold(Fl.flat(xss)), Some{LLogicWire.fe.lists_of(xss)}, fe.fold_flat(xss)) : {Fl.unflat.fin(_) == Some{xss} : Maybe<&2, List<&2, List<&2, Nat>>>}
  %Equal.sym(List<&2, List<&2, Nat>>, Fl.St.lists(LLogicWire.fe.lists_of(xss)), xss, fe.lists_back(xss)) : {Some{_} == Some{xss} : Maybe<&2, List<&2, List<&2, Nat>>>}
  {==}
