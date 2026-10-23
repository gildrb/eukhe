# eukhe: lemmas the proofs of two or more areas share: wire

import Base
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ./bool/and.bend as LBoolAnd
import ./bool/misc.bend as LBoolMisc
import ./list.bend as LList
import ./nat/add.bend as LNatAdd
import ./nat/misc.bend as LNatMisc
import ./pair.bend as LPair
import ./string.bend as LString

# The proofs of LAWS.bend section wire (bend/wire.bend): the Nat codec
# (lemmas wn_), the U32 codec (wu_), and the Bool, String and List codecs
# and the replies (wr_). The kit lemmas are copied from the bend skill's
# examples/sort/proof (kit.bend, nat_add.bend, u32_order.bend).

# ---- wire: nat ----

# ---- wire nat (wo_): the list decoder, the reference the fast one equals ----

# bend/wire.bend reads a Nat in one flat loop that folds the value as it
# reads. The proofs below are about this reference: it collects the digits
# (read last first) and folds them at the end. wn_eqv proves the two equal
# on every input, so every lemma about the reference holds for get_nat.

# The token at the head of s and the rest (the end of input reads Other).
def wo_peek(s: String) -> Wr.Tok & String:
  match s:
    case SNil{}:
      (Wr.Other{}, SNil{})
    case SCon{c, t}:
      (Wr.tok(c), t)

# No digit is left: only the end mark may follow.
def wo_end(ts: Wr.Tok & String, ds: List<&2, Nat>) -> Wr.Dec<Nat>:
  (t, s) = ts
  match t:
    case Wr.Dig{d}:
      Wr.Bad{}
    case Wr.Comma{}:
      Wr.Got{LNatMisc.wo_value(ds), s}
    case Wr.Other{}:
      Wr.Bad{}

# Read at most k more digits after ds (read last first), then ','.
def wo_go(k: Nat, ts: Wr.Tok & String, ds: List<&2, Nat>) -> Wr.Dec<Nat>:
  match k:
    case 0n:
      wo_end(ts, ds)
    case 1n+j:
      (t, s) = ts
      match t:
        case Wr.Dig{d}:
          wo_go(j, wo_peek(s), d <> ds)
        case Wr.Comma{}:
          Wr.Got{LNatMisc.wo_value(ds), s}
        case Wr.Other{}:
          Wr.Bad{}

def wo_lead(d: Nat, ts: Wr.Tok & String) -> Wr.Dec<Nat>:
  match d:
    case 0n:
      wo_end(ts, [0n])
    case 1n+p:
      wo_go(13n, ts, [1n+p])

# The first digit: 0 stands alone, any other starts up to 13 more.
def wo_first(ts: Wr.Tok & String) -> Wr.Dec<Nat>:
  (t, s) = ts
  match t:
    case Wr.Dig{d}:
      wo_lead(d, wo_peek(s))
    case Wr.Comma{}:
      Wr.Bad{}
    case Wr.Other{}:
      Wr.Bad{}

def wo_get_nat(s: String) -> Wr.Dec<Nat>:
  wo_first(wo_peek(s))

# a digit below 10 reads back as itself
def wn_tok_dig(+d: Nat, h: {LBoolMisc.wn_lt10(d) == True{} : Bool}) -> {Wr.tok(Wr.dchar(d)) == Wr.Dig{d} : Wr.Tok}:
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
      LBoolMisc.wn_absurd({Wr.tok(Wr.dchar(10n+p)) == Wr.Dig{10n+p} : Wr.Tok}, h)

def wn_pe(g: Nat, +q: Nat, acc: String) -> {Wr.put_nat.go(g, q, acc) == LString.wn_emit(LList.wn_L(g, q), acc) : String}:
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
def wn_put_emit(+n: Nat, rest: String) -> {Wr.put_nat(n, rest) == LString.wn_emit(LList.wn_full(n), SCon{',', rest}) : String}:
  wn_pe(n, Nat.div(n, 10n), SCon{Wr.dchar(Nat.mod(n, 10n)), SCon{',', rest}})

def wn_gc(k: Nat, ds: List<&2, Nat>, s: String) -> {wo_go(k, (Wr.Comma{}, s), ds) == Wr.Got{LNatMisc.wo_value(ds), s} : Wr.Dec<Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}

def wn_gother(k: Nat, ds: List<&2, Nat>, s: String) -> {wo_go(k, (Wr.Other{}, s), ds) == Wr.Bad{} : Wr.Dec<Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}

# The fast decoder equals the reference: the end of the digits
def wn_eq_end(t: Wr.Tok, s: String, -v: Nat, -ds: List<&2, Nat>, e: {v == LNatMisc.wo_value(ds) : Nat})
  -> {Wr.get_nat.end(t, s, v) == wo_end((t, s), ds) : Wr.Dec<Nat>}:
  match t:
    case Wr.Dig{d}:
      {==}
    case Wr.Comma{}:
      %e : {Wr.Got{v, s} == Wr.Got{_, s} : Wr.Dec<Nat>}
      {==}
    case Wr.Other{}:
      {==}

# ... the loop over the digits, the value folded so far being worth ds
def wn_eq_go(k: Nat, t: Wr.Tok, s: String, +v: Nat, +ds: List<&2, Nat>, e: {v == LNatMisc.wo_value(ds) : Nat})
  -> {Wr.get_nat.go(k, t, s, v) == wo_go(k, (t, s), ds) : Wr.Dec<Nat>}:
  match k:
    case 0n:
      wn_eq_end(t, s, v, ds, e)
    case 1n+j:
      match t:
        case Wr.Dig{+d}:
          match s:
            case SNil{}:
              Equal.sym(Wr.Dec<Nat>, wo_go(j, (Wr.Other{}, SNil{}), d <> ds), Wr.Bad{}, wn_gother(j, d <> ds, SNil{}))
            case SCon{c, r}:
              wn_eq_go(j, Wr.tok(c), r, Nat.add(d, Nat.mul(10n, v)), d <> ds,
                Equal.cong(Nat, Nat, x => Nat.add(d, Nat.mul(10n, x)), v, LNatMisc.wo_value(ds), e))
        case Wr.Comma{}:
          %e : {Wr.Got{v, s} == Wr.Got{_, s} : Wr.Dec<Nat>}
          {==}
        case Wr.Other{}:
          {==}

def wn_eq_lead(d: Nat, t: Wr.Tok, s: String) -> {Wr.get_nat.lead(d, t, s) == wo_lead(d, (t, s)) : Wr.Dec<Nat>}:
  match d:
    case 0n:
      wn_eq_end(t, s, 0n, [0n], {==})
    case 1n++p:
      wn_eq_go(13n, t, s, 1n+p, [1n+p], Equal.sym(Nat, Nat.add(1n+p, 0n), 1n+p, LNatAdd.wn_add_zero_r(1n+p)))

def wn_eq_first(t: Wr.Tok, s: String) -> {Wr.get_nat.first(t, s) == wo_first((t, s)) : Wr.Dec<Nat>}:
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
def wn_eqv(s: String) -> {Wr.get_nat(s) == wo_get_nat(s) : Wr.Dec<Nat>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, r}:
      wn_eq_first(Wr.tok(c), r)

def wn_f1_one(+d: Nat, x: String, +k: Nat, c: {LBoolMisc.wn_nz10(d) == True{} : Bool}, e: {1n+k == 14n : Nat})
  -> {wo_first(wo_peek(LString.wn_emit([d], x))) == wo_go(k, wo_peek(x), [d]) : Wr.Dec<Nat>}:
  match d:
    case 0n:
      LBoolMisc.wn_absurd({wo_first(wo_peek(LString.wn_emit([0n], x))) == wo_go(k, wo_peek(x), [0n]) : Wr.Dec<Nat>}, c)
    case 1n+p:
      %Equal.sym(Nat, k, 13n, Equal.cong(Nat, Nat, LNatMisc.wn_pred, 1n+k, 14n, e)) : {wo_first(wo_peek(LString.wn_emit([1n+p], x))) == wo_go(_, wo_peek(x), [1n+p]) : Wr.Dec<Nat>}
      %Equal.sym(Wr.Tok, Wr.tok(Wr.dchar(1n+p)), Wr.Dig{1n+p}, wn_tok_dig(1n+p, c)) : {wo_first((_, x)) == wo_go(13n, wo_peek(x), [1n+p]) : Wr.Dec<Nat>}
      {==}

# a canonical list of at most 14 digits: the decoder reads all of it and
# has k digits left to read
def wn_f1(t: List<&2, Nat>, +d: Nat, +x: String, +k: Nat, +c: {LBoolMisc.wn_okc(t, d) == True{} : Bool},
  e: {Nat.add(List.length(&2, Nat, d <> t), k) == 14n : Nat})
  -> {wo_first(wo_peek(LString.wn_emit(d <> t, x))) == wo_go(k, wo_peek(x), d <> t) : Wr.Dec<Nat>}:
  match t:
    case Nil{}:
      wn_f1_one(d, x, k, c, e)
    case Con{+e2, +u}:
      +hd = LBoolAnd.wn_and_l(LBoolMisc.wn_lt10(d), LBoolMisc.wn_okc(u, e2), c)
      +ih = wn_f1(u, e2, SCon{Wr.dchar(d), x}, 1n+k, LBoolAnd.wn_and_r(LBoolMisc.wn_lt10(d), LBoolMisc.wn_okc(u, e2), c),
        Equal.trans(Nat, Nat.add(List.length(&2, Nat, e2 <> u), 1n+k), 1n+Nat.add(List.length(&2, Nat, e2 <> u), k), 14n,
          LNatAdd.wn_add_succ_r(List.length(&2, Nat, e2 <> u), k), e))
      %Equal.sym(Wr.Dec<Nat>, wo_first(wo_peek(LString.wn_emit(e2 <> u, SCon{Wr.dchar(d), x}))), wo_go(1n+k, wo_peek(SCon{Wr.dchar(d), x}), e2 <> u), ih) : {_ == wo_go(k, wo_peek(x), d <> (e2 <> u)) : Wr.Dec<Nat>}
      %Equal.sym(Wr.Tok, Wr.tok(Wr.dchar(d)), Wr.Dig{d}, wn_tok_dig(d, hd)) : {wo_go(1n+k, (_, x), e2 <> u) == wo_go(k, wo_peek(x), d <> (e2 <> u)) : Wr.Dec<Nat>}
      {==}

def wn_rt(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {wo_get_nat(Wr.put_nat(n, rest)) == Wr.Got{n, rest} : Wr.Dec<Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +hl = Equal.trans(Bool, Nat.is_le(List.length(&2, Nat, LList.wn_full(1n+p)), 14n), Nat.is_le(LawsBase.wire_digits(1n+p), 14n), True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, 14n), List.length(&2, Nat, LList.wn_full(1n+p)), LawsBase.wire_digits(1n+p),
          Equal.sym(Nat, LawsBase.wire_digits(1n+p), List.length(&2, Nat, LList.wn_full(1n+p)), LList.wn_wl(1n+p))), h)
      +k = LNatMisc.wn_sub(14n, List.length(&2, Nat, LList.wn_full(1n+p)))
      +f1 = wn_f1(LList.wn_L(1n+p, Nat.div(1n+p, 10n)), Nat.mod(1n+p, 10n), SCon{',', rest}, k, LPair.wn_cf(p),
        LNatAdd.wn_le_k(List.length(&2, Nat, LList.wn_full(1n+p)), 14n, hl))
      %Equal.sym(String, Wr.put_nat(1n+p, rest), LString.wn_emit(LList.wn_full(1n+p), SCon{',', rest}), wn_put_emit(1n+p, rest)) : {wo_get_nat(_) == Wr.Got{1n+p, rest} : Wr.Dec<Nat>}
      %Equal.sym(Wr.Dec<Nat>, wo_first(wo_peek(LString.wn_emit(LList.wn_full(1n+p), SCon{',', rest}))), wo_go(k, wo_peek(SCon{',', rest}), LList.wn_full(1n+p)), f1) : {_ == Wr.Got{1n+p, rest} : Wr.Dec<Nat>}
      %Equal.sym(Wr.Dec<Nat>, wo_go(k, (Wr.Comma{}, rest), LList.wn_full(1n+p)), Wr.Got{LNatMisc.wo_value(LList.wn_full(1n+p)), rest}, wn_gc(k, LList.wn_full(1n+p), rest)) : {_ == Wr.Got{1n+p, rest} : Wr.Dec<Nat>}
      %LPair.wn_vf(1n+p) : {Wr.Got{LNatMisc.wo_value(LList.wn_full(1n+p)), rest} == Wr.Got{_, rest} : Wr.Dec<Nat>}
      {==}

def Wire.wire_nat_round_trip(n, rest, h):
  +r = rest
  Equal.trans(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, r)), wo_get_nat(Wr.put_nat(n, r)), Wr.Got{n, r},
    wn_eqv(Wr.put_nat(n, r)), wn_rt(n, r, h))

# put_str.go turns a around onto acc and adds its length to n
def wr_put_str_go(a: String, -acc: String, -n: Nat) ->
  {Wr.put_str.go(a, acc, n) == (Nat.add(String.length(a), n), String.reverse.go(a, acc)) : Nat & String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      %Equal.sym(Nat & String, Wr.put_str.go(t, SCon{c, acc}, 1n+n), (Nat.add(String.length(t), 1n+n), String.reverse.go(t, SCon{c, acc})), wr_put_str_go(t, SCon{c, acc}, 1n+n)) : {_ == (1n+Nat.add(String.length(t), n), String.reverse.go(t, SCon{c, acc})) : Nat & String}
      %LNatAdd.wn_add_succ_r(String.length(t), n) : {(Nat.add(String.length(t), 1n+n), String.reverse.go(t, SCon{c, acc})) == (_, String.reverse.go(t, SCon{c, acc})) : Nat & String}
      {==}

# a string is its length, then its chars
def wr_put_str(+a: String, +rest: String) ->
  {Wr.put_str(a, rest) == Wr.put_nat(String.length(a), LString.wr_app(a, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_str.go(a, SNil{}, 0n), (Nat.add(String.length(a), 0n), String.reverse.go(a, SNil{})), wr_put_str_go(a, SNil{}, 0n)) : {Wr.put_str.fin(_, rest) == Wr.put_nat(String.length(a), LString.wr_app(a, rest)) : String}
  %Equal.sym(Nat, Nat.add(String.length(a), 0n), String.length(a), LNatAdd.wn_add_zero_r(String.length(a))) : {Wr.put_nat(_, String.reverse.go(String.reverse.go(a, SNil{}), rest)) == Wr.put_nat(String.length(a), LString.wr_app(a, rest)) : String}
  %Equal.sym(String, String.reverse.go(String.reverse.go(a, SNil{}), rest), LString.wr_app(a, rest), LString.wr_rev_rev(a, SNil{}, rest)) : {Wr.put_nat(String.length(a), _) == Wr.put_nat(String.length(a), LString.wr_app(a, rest)) : String}
  {==}

# the reference take: the chars one by one, head first
def wo_take_cons(c: Char, r: Wr.Dec<String>) -> Wr.Dec<String>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{SCon{c, a}, s}
    case Wr.Bad{}:
      Wr.Bad{}

# The first n chars of s and the rest.
def wo_take(n: Nat, s: String) -> Wr.Dec<String>:
  match n:
    case 0n:
      Wr.Got{SNil{}, s}
    case 1n+m:
      match s:
        case SNil{}:
          Wr.Bad{}
        case SCon{c, t}:
          wo_take_cons(c, wo_take(m, t))

# the chars of an answer of the reference, after acc turned around
def wr_tfix(acc: String, r: Wr.Dec<String>) -> Wr.Dec<String>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{String.reverse.go(acc, a), s}
    case Wr.Bad{}:
      Wr.Bad{}

def wr_tfix_cons(-acc: String, -c: Char, r: Wr.Dec<String>) ->
  {wr_tfix(SCon{c, acc}, r) == wr_tfix(acc, wo_take_cons(c, r)) : Wr.Dec<String>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

# the flat take.go answers the reference, with the chars read so far in front
def wr_take_go(n: Nat, s: String, +acc: String) -> {Wr.take.go(n, s, acc) == wr_tfix(acc, wo_take(n, s)) : Wr.Dec<String>}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      match s:
        case SNil{}:
          {==}
        case SCon{+c, +t}:
          Equal.trans(Wr.Dec<String>, Wr.take.go(m, t, SCon{c, acc}), wr_tfix(SCon{c, acc}, wo_take(m, t)), wr_tfix(acc, wo_take_cons(c, wo_take(m, t))),
            wr_take_go(m, t, SCon{c, acc}), wr_tfix_cons(acc, c, wo_take(m, t)))

def wr_tfix_nil(r: Wr.Dec<String>) -> {wr_tfix(SNil{}, r) == r : Wr.Dec<String>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

# take answers what the reference answers
def wr_take_eq(+n: Nat, +s: String) -> {Wr.take(n, s) == wo_take(n, s) : Wr.Dec<String>}:
  Equal.trans(Wr.Dec<String>, Wr.take.go(n, s, SNil{}), wr_tfix(SNil{}, wo_take(n, s)), wo_take(n, s),
    wr_take_go(n, s, SNil{}), wr_tfix_nil(wo_take(n, s)))

# the reference reads back the chars of a
def wr_take_rt(+a: String, -rest: String) ->
  {wo_take(String.length(a), LString.wr_app(a, rest)) == Wr.Got{a, rest} : Wr.Dec<String>}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      %Equal.sym(Wr.Dec<String>, wo_take(String.length(t), LString.wr_app(t, rest)), Wr.Got{t, rest}, wr_take_rt(t, rest)) : {wo_take_cons(c, _) == Wr.Got{SCon{c, t}, rest} : Wr.Dec<String>}
      {==}

# Nat laws used as lemmas (proved in the Nat slice)
def Wire.wire_str_round_trip(a, rest, h):
  +r = rest
  %Equal.sym(String, Wr.put_str(a, r), Wr.put_nat(String.length(a), LString.wr_app(a, r)), wr_put_str(a, r)) : {Wr.get_str(_) == Wr.Got{a, r} : Wr.Dec<String>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(String.length(a), LString.wr_app(a, r))), Wr.Got{String.length(a), LString.wr_app(a, r)}, Wire.wire_nat_round_trip(String.length(a), LString.wr_app(a, r), h)) : {Wr.get_str.go(_) == Wr.Got{a, r} : Wr.Dec<String>}
  Equal.trans(Wr.Dec<String>, Wr.take(String.length(a), LString.wr_app(a, r)), wo_take(String.length(a), LString.wr_app(a, r)), Wr.Got{a, r},
    wr_take_eq(String.length(a), LString.wr_app(a, r)), wr_take_rt(a, r))

def wr_put_list_go(xs: List<&2, Nat>, -rest: String) ->
  {Wr.put_list.go(~Nat, ~Wr.put_nat, xs, rest) == (List.length(&2, Nat, xs), LString.wr_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Nat, ~Wr.put_nat, t, rest), (List.length(&2, Nat, t), LString.wr_items(t, rest)), wr_put_list_go(t, rest)) : {Wr.put_list.step(~Nat, ~Wr.put_nat, x, _) == (1n+List.length(&2, Nat, t), Wr.put_nat(x, LString.wr_items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def wr_put_list(+xs: List<&2, Nat>, -rest: String) ->
  {Wr.put_list(~Nat, ~Wr.put_nat, xs, rest) == Wr.put_nat(List.length(&2, Nat, xs), LString.wr_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Nat, ~Wr.put_nat, xs, rest), (List.length(&2, Nat, xs), LString.wr_items(xs, rest)), wr_put_list_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Nat, xs), LString.wr_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def wr_list_go_rt(+t: List<&2, Nat>, +x: Nat, +rest: String,
  +hf: {LawsBase.wire_nats_fit(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Nat, ~Wr.get_nat, List.length(&2, Nat, t), Wr.get_nat(Wr.put_nat(x, LString.wr_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Nat>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(x, rest)), Wr.Got{x, rest}, Wire.wire_nat_round_trip(x, rest, LBoolAnd.wr_and_l(LawsBase.wire_fits(x), True{}, hf))) : {Wr.get_list.go(~Nat, ~Wr.get_nat, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Nat>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(x, Wr.put_nat(y, LString.wr_items(u, rest)))), Wr.Got{x, Wr.put_nat(y, LString.wr_items(u, rest))}, Wire.wire_nat_round_trip(x, Wr.put_nat(y, LString.wr_items(u, rest)), LBoolAnd.wr_and_l(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(y <> u), hf))) : {Wr.get_list.go(~Nat, ~Wr.get_nat, 1n+List.length(&2, Nat, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Nat>>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list.go(~Nat, ~Wr.get_nat, List.length(&2, Nat, u), Wr.get_nat(Wr.put_nat(y, LString.wr_items(u, rest)))), Wr.Got{y <> u, rest}, wr_list_go_rt(u, y, rest, LBoolAnd.wr_and_r(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(y <> u), hf))) : {Wr.get_list.cons(Nat, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Nat>>}
      {==}

def Wire.wire_list_round_trip(xs, rest, h):
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, LBoolAnd.wr_and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Nat, ~Wr.get_nat, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Nat>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, x <> t, r), Wr.put_nat(List.length(&2, Nat, x <> t), LString.wr_items(x <> t, r)), wr_put_list(x <> t, r)) : {Wr.get_list(~Nat, ~Wr.get_nat, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Nat>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Nat, x <> t), LString.wr_items(x <> t, r))), Wr.Got{List.length(&2, Nat, x <> t), LString.wr_items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Nat, x <> t), LString.wr_items(x <> t, r), LBoolAnd.wr_and_l(LawsBase.wire_fits(List.length(&2, Nat, x <> t)), LawsBase.wire_nats_fit(x <> t), hh))) : {Wr.get_list.start(~Nat, ~Wr.get_nat, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Nat>>}
      wr_list_go_rt(t, x, r, LBoolAnd.wr_and_r(LawsBase.wire_fits(List.length(&2, Nat, x <> t)), LawsBase.wire_nats_fit(x <> t), hh))

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

# ---- ffi_edges ----

# The proofs of the compiled-core entry laws of the W9 areas (LAWS.bend:
# tools_ffi_*, tiny_ffi_*, catalog_union_ffi_*, gateway_width_ffi_*,
# path_policy_ffi_*). A request is a record of the wire's Nat lists (and a
# Bool), so each round trip is the wire's list round trip (Laws.
# wire_list_round_trip) and a lemma that the request's parts decode from
# their lists (`fe.*`). An entry answers a request read whole with the
# model's reply, and anything else with the error form.

# Lists of lists (bend/wire_flat.bend)
# ------------------------------------

def fe.lists_of(t: List<&2, List<&2, Nat>>) -> Fl.St:
  match t:
    case Nil{}:
      Fl.Start{}
    case xs <> d:
      Fl.Mid{xs, d}

def fe.lists_back(t: List<&2, List<&2, Nat>>) -> {Fl.St.lists(fe.lists_of(t)) == t : List<&2, List<&2, Nat>>}:
  match t:
    case Nil{}:
      {==}
    case xs <> d:
      {==}

# a list in front of the lists t decodes to the open list xs before t
def fe.one_fold(xs: List<&2, Nat>, +t: List<&2, List<&2, Nat>>, h: {Fl.fold(Fl.flat(t)) == Some{fe.lists_of(t)} : Maybe<&2, Fl.St>}) -> {Fl.fold(Fl.one(xs, Fl.flat(t))) == Some{Fl.Mid{xs, t}} : Maybe<&2, Fl.St>}:
  match xs:
    case Nil{}:
      %Equal.sym(Maybe<&2, Fl.St>, Fl.fold(Fl.flat(t)), Some{fe.lists_of(t)}, h) : {Fl.step(0n, _) == Some{Fl.Mid{Nil{}, t}} : Maybe<&2, Fl.St>}
      %Equal.sym(List<&2, List<&2, Nat>>, Fl.St.lists(fe.lists_of(t)), t, fe.lists_back(t)) : {Some{Fl.Mid{Nil{}, _}} == Some{Fl.Mid{Nil{}, t}} : Maybe<&2, Fl.St>}
      {==}
    case +x <> +r:
      %Equal.sym(Maybe<&2, Fl.St>, Fl.fold(Fl.one(r, Fl.flat(t))), Some{Fl.Mid{r, t}}, fe.one_fold(r, t, h)) : {Fl.step({1n+x : Nat}, _) == Some{Fl.Mid{x <> r, t}} : Maybe<&2, Fl.St>}
      {==}

def fe.fold_flat(xss: List<&2, List<&2, Nat>>) -> {Fl.fold(Fl.flat(xss)) == Some{fe.lists_of(xss)} : Maybe<&2, Fl.St>}:
  match xss:
    case Nil{}:
      {==}
    case xs <> +t:
      fe.one_fold(xs, t, fe.fold_flat(t))

# lists of lists read back from their flat list
def fe.unflat_flat(+xss: List<&2, List<&2, Nat>>) -> {Fl.unflat(Fl.flat(xss)) == Some{xss} : Maybe<&2, List<&2, List<&2, Nat>>>}:
  %Equal.sym(Maybe<&2, Fl.St>, Fl.fold(Fl.flat(xss)), Some{fe.lists_of(xss)}, fe.fold_flat(xss)) : {Fl.unflat.fin(_) == Some{xss} : Maybe<&2, List<&2, List<&2, Nat>>>}
  %Equal.sym(List<&2, List<&2, Nat>>, Fl.St.lists(fe.lists_of(xss)), xss, fe.lists_back(xss)) : {Some{_} == Some{xss} : Maybe<&2, List<&2, List<&2, Nat>>>}
  {==}
