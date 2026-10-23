# eukhe: the proof of LAW wire_nat_too_long

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base.bend as L

def wn_absurd2(-G: Type, e: {True{} == False{} : Bool}) -> G:
  L.wn_absurd(G, Equal.sym(Bool, True{}, False{}, e))

def wn_le_zero(p: Nat, h: {Nat.is_le(p, 0n) == True{} : Bool}) -> {p == 0n : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      L.wn_absurd({1n+q == 0n : Nat}, h)

# a <= 1 + b and not a <= b: a is 1 + b
def wn_le_last(a: Nat, b: Nat, h1: {Nat.is_le(a, 1n+b) == True{} : Bool}, h2: {Nat.is_le(a, b) == False{} : Bool})
  -> {a == 1n+b : Nat}:
  match a b:
    case 0n 0n:
      wn_absurd2({0n == 1n : Nat}, h2)
    case 0n 1n+q:
      wn_absurd2({0n == 1n+1n+q : Nat}, h2)
    case 1n+p 0n:
      Equal.cong(Nat, Nat, k => 1n+k, p, 0n, wn_le_zero(p, h1))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, k => 1n+k, p, 1n+q, wn_le_last(p, q, h1, h2))

def wn_f2h(b: Bool, +u: List<&2, Nat>, +e2: Nat, +d: Nat, +x: String,
  eb: {Nat.is_le(List.length(&2, Nat, e2 <> u), 14n) == b : Bool},
  hd: {L.wn_lt10(d) == True{} : Bool}, ct: {L.wn_okc(u, e2) == True{} : Bool},
  hyp: {Nat.is_le(List.length(&2, Nat, e2 <> u), 13n) == False{} : Bool},
  rec: {Nat.is_le(List.length(&2, Nat, e2 <> u), 14n) == False{} : Bool}
    -> {L.wo_first(L.wo_peek(L.wn_emit(e2 <> u, SCon{Wr.dchar(d), x}))) == Wr.Bad{} : Wr.Dec<Nat>})
  -> {L.wo_first(L.wo_peek(L.wn_emit(e2 <> u, SCon{Wr.dchar(d), x}))) == Wr.Bad{} : Wr.Dec<Nat>}:
  match b:
    case False{}:
      rec(eb)
    case True{}:
      +l14 = wn_le_last(List.length(&2, Nat, e2 <> u), 13n, eb, hyp)
      +r = L.wn_f1(u, e2, SCon{Wr.dchar(d), x}, 0n, ct,
        Equal.trans(Nat, Nat.add(List.length(&2, Nat, e2 <> u), 0n), List.length(&2, Nat, e2 <> u), 14n,
          L.wn_add_zero_r(List.length(&2, Nat, e2 <> u)), l14))
      %Equal.sym(Wr.Dec<Nat>, L.wo_first(L.wo_peek(L.wn_emit(e2 <> u, SCon{Wr.dchar(d), x}))), L.wo_go(0n, L.wo_peek(SCon{Wr.dchar(d), x}), e2 <> u), r) : {_ == Wr.Bad{} : Wr.Dec<Nat>}
      %Equal.sym(Wr.Tok, Wr.tok(Wr.dchar(d)), Wr.Dig{d}, L.wn_tok_dig(d, hd)) : {L.wo_end((_, x), e2 <> u) == Wr.Bad{} : Wr.Dec<Nat>}
      {==}

# a canonical list of more than 14 digits: the decoder refuses it
def wn_f2(t: List<&2, Nat>, +d: Nat, +x: String, +c: {L.wn_okc(t, d) == True{} : Bool})
  -> {Nat.is_le(List.length(&2, Nat, d <> t), 14n) == False{} : Bool}
  -> {L.wo_first(L.wo_peek(L.wn_emit(d <> t, x))) == Wr.Bad{} : Wr.Dec<Nat>}:
  match t:
    case Nil{}:
      h => wn_absurd2({L.wo_first(L.wo_peek(L.wn_emit([d], x))) == Wr.Bad{} : Wr.Dec<Nat>}, h)
    case Con{+e2, +u}:
      h => wn_f2h(Nat.is_le(List.length(&2, Nat, e2 <> u), 14n), u, e2, d, x, {==},
        L.wn_and_l(L.wn_lt10(d), L.wn_okc(u, e2), c), L.wn_and_r(L.wn_lt10(d), L.wn_okc(u, e2), c), h,
        wn_f2(u, e2, SCon{Wr.dchar(d), x}, L.wn_and_r(L.wn_lt10(d), L.wn_okc(u, e2), c)))

def wn_tl(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == False{} : Bool}) -> {L.wo_get_nat(Wr.put_nat(n, rest)) == Wr.Bad{} : Wr.Dec<Nat>}:
  match n:
    case 0n:
      wn_absurd2({L.wo_get_nat(Wr.put_nat(0n, rest)) == Wr.Bad{} : Wr.Dec<Nat>}, h)
    case 1n+p:
      +hl = Equal.trans(Bool, Nat.is_le(List.length(&2, Nat, L.wn_full(1n+p)), 14n), Nat.is_le(LawsBase.wire_digits(1n+p), 14n), False{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, 14n), List.length(&2, Nat, L.wn_full(1n+p)), LawsBase.wire_digits(1n+p),
          Equal.sym(Nat, LawsBase.wire_digits(1n+p), List.length(&2, Nat, L.wn_full(1n+p)), L.wn_wl(1n+p))), h)
      %Equal.sym(String, Wr.put_nat(1n+p, rest), L.wn_emit(L.wn_full(1n+p), SCon{',', rest}), L.wn_put_emit(1n+p, rest)) : {L.wo_get_nat(_) == Wr.Bad{} : Wr.Dec<Nat>}
      wn_f2(L.wn_L(1n+p, Nat.div(1n+p, 10n)), Nat.mod(1n+p, 10n), SCon{',', rest}, L.wn_cf(p))(hl)

def Wire.wire_nat_too_long(n, rest, h):
  +r = rest
  Equal.trans(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, r)), L.wo_get_nat(Wr.put_nat(n, r)), Wr.Bad{},
    L.wn_eqv(Wr.put_nat(n, r)), wn_tl(n, r, h))
