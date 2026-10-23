# eukhe: the proof of LAW wire_nat_exact

import Base
import ../../bend/wire.bend as Wr
import ../../laws/wire.bend as Wire
import ../base/bool/and.bend as LBoolAnd
import ../base/bool/misc.bend as LBoolMisc
import ../base/nat/misc.bend as LNatMisc
import ../base/string.bend as LString
import ../base/wire.bend as LWire
import ./base.bend as LA

# ---- U32.is_eq is sound (copied, renamed, from the skill's examples/sort/proof/u32_order.bend: eq_sound, Word.cmp_eq) ----

def wn_lt_eq(-G: Type, e: {LT{} == EQ{} : Cmp}) -> G:
  LBoolMisc.wn_absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), LT{}, EQ{}, e))

def wn_gt_eq(-G: Type, e: {GT{} == EQ{} : Cmp}) -> G:
  LBoolMisc.wn_absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), GT{}, EQ{}, e))

def wn_cmp_eq_fin(-p: Nat, -at: Word(p), -bt: Word(p), t: Cmp, +ab: Bool, +bb: Bool,
  et: {Word.cmp(p, at, bt) == t : Cmp},
  rec: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)},
  e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp})
  -> {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}:
  match t:
    case LT{}:
      wn_lt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case GT{}:
      wn_gt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt, rec(et))
        case False{} True{}:
          wn_lt_eq({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, e)
        case True{} False{}:
          wn_gt_eq({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, e)
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt, rec(et))

def wn_word_cmp_eq(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.cmp(n, a, b) == EQ{} : Cmp} -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          e => {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          e => wn_cmp_eq_fin(p, at, bt, Word.cmp(p, at, bt), ab, bb, {==},
            wn_word_cmp_eq(p, at, bt), e)

def wn_u32_cmp_eq(+a: U32, +b: U32, e: {U32.cmp(a, b) == EQ{} : Cmp}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, wn_word_cmp_eq(32n, x, y)(e))

def wn_sound_fin(+a: U32, +b: U32, t: Cmp, et: {U32.cmp(a, b) == t : Cmp},
  e: {Cmp.is_eq(t) == True{} : Bool}) -> {a == b : U32}:
  match t:
    case LT{}:
      LBoolMisc.wn_absurd({a == b : U32}, e)
    case EQ{}:
      wn_u32_cmp_eq(a, b, et)
    case GT{}:
      LBoolMisc.wn_absurd({a == b : U32}, e)

def wn_eq_sound(+a: U32, +b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  wn_sound_fin(a, b, U32.cmp(a, b), {==}, e)

# ---- chars and tokens ----

# the digit of a token (0 for the others)
def wn_tok_d(t: Wr.Tok) -> Nat:
  match t:
    case Wr.Dig{d}:
      d
    case Wr.Comma{}:
      0n
    case Wr.Other{}:
      0n

def wn_tok_isdig(t: Wr.Tok) -> Bool:
  match t:
    case Wr.Dig{d}:
      True{}
    case Wr.Comma{}:
      False{}
    case Wr.Other{}:
      False{}

def wn_tok_iscomma(t: Wr.Tok) -> Bool:
  match t:
    case Wr.Dig{d}:
      False{}
    case Wr.Comma{}:
      True{}
    case Wr.Other{}:
      False{}

# tok.is answered Dig{d}: the test passed, and d is the digit it tested
def wn_tokis_dig(ok: Bool, d2: Nat, comma: Bool, -d: Nat, e: {Wr.tok.is(ok, d2, comma) == Wr.Dig{d} : Wr.Tok})
  -> {ok == True{} : Bool} & {d2 == d : Nat}:
  match ok:
    case True{}:
      ({==}, Equal.cong(Wr.Tok, Nat, wn_tok_d, Wr.Dig{d2}, Wr.Dig{d}, e))
    case False{}:
      match comma:
        case True{}:
          LBoolMisc.wn_absurd({False{} == True{} : Bool} & {d2 == d : Nat}, Equal.cong(Wr.Tok, Bool, wn_tok_isdig, Wr.Comma{}, Wr.Dig{d}, e))
        case False{}:
          LBoolMisc.wn_absurd({False{} == True{} : Bool} & {d2 == d : Nat}, Equal.cong(Wr.Tok, Bool, wn_tok_isdig, Wr.Other{}, Wr.Dig{d}, e))

# tok.is answered Comma{}: the char was ','
def wn_tokis_comma(ok: Bool, d2: Nat, comma: Bool, e: {Wr.tok.is(ok, d2, comma) == Wr.Comma{} : Wr.Tok})
  -> {comma == True{} : Bool}:
  match ok:
    case True{}:
      LBoolMisc.wn_absurd({comma == True{} : Bool}, Equal.cong(Wr.Tok, Bool, wn_tok_iscomma, Wr.Dig{d2}, Wr.Comma{}, e))
    case False{}:
      match comma:
        case True{}:
          {==}
        case False{}:
          LBoolMisc.wn_absurd({False{} == True{} : Bool}, Equal.cong(Wr.Tok, Bool, wn_tok_iscomma, Wr.Other{}, Wr.Comma{}, e))

# a d below 10 is a digit, and the code 48 + d is the code of its char
def wn_code(d: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool})
  -> {Chr{U32.from_nat(Nat.add(48n, d))} == Wr.dchar(d) : Char} & {LBoolMisc.wn_lt10(d) == True{} : Bool}:
  match d:
    case 0n:
      ({==}, {==})
    case 1n:
      ({==}, {==})
    case 2n:
      ({==}, {==})
    case 3n:
      ({==}, {==})
    case 4n:
      ({==}, {==})
    case 5n:
      ({==}, {==})
    case 6n:
      ({==}, {==})
    case 7n:
      ({==}, {==})
    case 8n:
      ({==}, {==})
    case 9n:
      ({==}, {==})
    case 10n+p:
      match p:
        case 0n:
          LBoolMisc.wn_absurd({Chr{U32.from_nat(Nat.add(48n, 10n))} == Wr.dchar(10n) : Char} & {LBoolMisc.wn_lt10(10n) == True{} : Bool}, h)
        case 1n+q:
          LBoolMisc.wn_absurd({Chr{U32.from_nat(Nat.add(48n, 11n+q))} == Wr.dchar(11n+q) : Char} & {LBoolMisc.wn_lt10(11n+q) == True{} : Bool}, h)

# tok.code(x, d2) == Dig{d}: the char of code x is the digit d, below 10
def wn_tdi(+x: U32, +d2: Nat, -d: Nat, +e: {Wr.tok.code(x, d2) == Wr.Dig{d} : Wr.Tok})
  -> {Chr{x} == Wr.dchar(d) : Char} & {LBoolMisc.wn_lt10(d) == True{} : Bool}:
  +ok = Pair.fst({Bool.and(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2)))) == True{} : Bool}, {d2 == d : Nat},
    wn_tokis_dig(Bool.and(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2)))), d2, U32.is_eq(x, 44), d, e))
  +dd = Pair.snd({Bool.and(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2)))) == True{} : Bool}, {d2 == d : Nat},
    wn_tokis_dig(Bool.and(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2)))), d2, U32.is_eq(x, 44), d, e))
  +lt = LBoolAnd.wn_and_l(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2))), ok)
  +ex = wn_eq_sound(x, U32.from_nat(Nat.add(48n, d2)), LBoolAnd.wn_and_r(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2))), ok))
  %dd : {Chr{x} == Wr.dchar(_) : Char} & {LBoolMisc.wn_lt10(_) == True{} : Bool}
  %Equal.sym(U32, x, U32.from_nat(Nat.add(48n, d2)), ex) : {Chr{_} == Wr.dchar(d2) : Char} & {LBoolMisc.wn_lt10(d2) == True{} : Bool}
  wn_code(d2, lt)

def wn_tok_dig_inv(c: Char, -d: Nat, e: {Wr.tok(c) == Wr.Dig{d} : Wr.Tok}) -> {c == Wr.dchar(d) : Char} & {LBoolMisc.wn_lt10(d) == True{} : Bool}:
  match c:
    case Chr{+x}:
      wn_tdi(x, Nat.sub(U32.to_nat(x), 48n), d, e)

# tok(c) == Dig{d}: c is the char of d
def wn_tdi_c(+c: Char, -d: Nat, e: {Wr.tok(c) == Wr.Dig{d} : Wr.Tok}) -> {c == Wr.dchar(d) : Char}:
  Pair.fst({c == Wr.dchar(d) : Char}, {LBoolMisc.wn_lt10(d) == True{} : Bool}, wn_tok_dig_inv(c, d, e))

# tok(c) == Dig{d}: d is below 10
def wn_tdi_lt(+c: Char, -d: Nat, e: {Wr.tok(c) == Wr.Dig{d} : Wr.Tok}) -> {LBoolMisc.wn_lt10(d) == True{} : Bool}:
  Pair.snd({c == Wr.dchar(d) : Char}, {LBoolMisc.wn_lt10(d) == True{} : Bool}, wn_tok_dig_inv(c, d, e))

# tok(c) == Comma{}: c is ','
def wn_tok_comma_inv(c: Char, e: {Wr.tok(c) == Wr.Comma{} : Wr.Tok}) -> {c == ',' : Char}:
  match c:
    case Chr{+x}:
      +d2 = Nat.sub(U32.to_nat(x), 48n)
      Equal.cong(U32, Char, y => Chr{y}, x, 44, wn_eq_sound(x, 44,
        wn_tokis_comma(Bool.and(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2)))), d2, U32.is_eq(x, 44), e)))

# put_nat of the value of a canonical list writes that list
def wn_E(+t: List<&2, Nat>, +d: Nat, y: String, c: {LBoolMisc.wn_okc(t, d) == True{} : Bool})
  -> {Wr.put_nat(LNatMisc.wo_value(d <> t), y) == LString.wn_emit(d <> t, SCon{',', y}) : String}:
  %LA.wn_lv(t, d, c) : {Wr.put_nat(LNatMisc.wo_value(d <> t), y) == LString.wn_emit(_, SCon{',', y}) : String}
  LWire.wn_put_emit(LNatMisc.wo_value(d <> t), y)

# the encoding a decoder answer stands for
def wn_put_dec(r: Wr.Dec<Nat>) -> String:
  match r:
    case Wr.Got{v, s}:
      Wr.put_nat(v, s)
    case Wr.Bad{}:
      SNil{}

def wn_EC(ds: List<&2, Nat>, y: String, c: {LBoolMisc.wn_canon(ds) == True{} : Bool}) -> {Wr.put_nat(LNatMisc.wo_value(ds), y) == LString.wn_emit(ds, SCon{',', y}) : String}:
  match ds:
    case Nil{}:
      LBoolMisc.wn_absurd({Wr.put_nat(LNatMisc.wo_value(Nil{}), y) == LString.wn_emit(Nil{}, SCon{',', y}) : String}, c)
    case Con{+d, +t}:
      wn_E(t, d, y, c)

def wn_invh(tk: Wr.Tok, +k: Nat, +ds: List<&2, Nat>, +c: Char, +t: String, -n: Nat, -rest: String,
  cd: {LBoolMisc.wn_canon(ds) == True{} : Bool},
  h: {LWire.wo_go(k, (tk, t), ds) == Wr.Got{n, rest} : Wr.Dec<Nat>},
  +et: {Wr.tok(c) == tk : Wr.Tok},
  ih: @k2: Nat -> @ds2: List<&2, Nat> -> {LBoolMisc.wn_canon(ds2) == True{} : Bool}
    -> {LWire.wo_go(k2, LWire.wo_peek(t), ds2) == Wr.Got{n, rest} : Wr.Dec<Nat>} -> {LString.wn_emit(ds2, t) == Wr.put_nat(n, rest) : String})
  -> {LString.wn_emit(ds, SCon{c, t}) == Wr.put_nat(n, rest) : String}:
  match tk:
    case Wr.Dig{+d}:
      match k:
        case 0n:
          LA.wn_bad_got({LString.wn_emit(ds, SCon{c, t}) == Wr.put_nat(n, rest) : String}, n, rest, h)
        case 1n+j:
          match ds:
            case Nil{}:
              LBoolMisc.wn_absurd({LString.wn_emit(Nil{}, SCon{c, t}) == Wr.put_nat(n, rest) : String}, cd)
            case Con{+e, +u}:
              +r = ih(j, d <> (e <> u), LBoolAnd.wn_and_intro(LBoolMisc.wn_lt10(d), LBoolMisc.wn_okc(u, e), wn_tdi_lt(c, d, et), cd), h)
              %Equal.sym(Char, c, Wr.dchar(d), wn_tdi_c(c, d, et)) : {LString.wn_emit(e <> u, SCon{_, t}) == Wr.put_nat(n, rest) : String}
              r
    case Wr.Comma{}:
      +hg = Equal.trans(Wr.Dec<Nat>, Wr.Got{LNatMisc.wo_value(ds), t}, LWire.wo_go(k, (Wr.Comma{}, t), ds), Wr.Got{n, rest},
        Equal.sym(Wr.Dec<Nat>, LWire.wo_go(k, (Wr.Comma{}, t), ds), Wr.Got{LNatMisc.wo_value(ds), t}, LWire.wn_gc(k, ds, t)), h)
      %hg : {LString.wn_emit(ds, SCon{c, t}) == wn_put_dec(_) : String}
      %Equal.sym(Char, c, ',', wn_tok_comma_inv(c, et)) : {LString.wn_emit(ds, SCon{_, t}) == Wr.put_nat(LNatMisc.wo_value(ds), t) : String}
      Equal.sym(String, Wr.put_nat(LNatMisc.wo_value(ds), t), LString.wn_emit(ds, SCon{',', t}), wn_EC(ds, t, cd))
    case Wr.Other{}:
      LA.wn_bad_got({LString.wn_emit(ds, SCon{c, t}) == Wr.put_nat(n, rest) : String}, n, rest,
        Equal.trans(Wr.Dec<Nat>, Wr.Bad{}, LWire.wo_go(k, (Wr.Other{}, t), ds), Wr.Got{n, rest},
          Equal.sym(Wr.Dec<Nat>, LWire.wo_go(k, (Wr.Other{}, t), ds), Wr.Bad{}, LWire.wn_gother(k, ds, t)), h))

# what the decoder accepted after the digits ds (canonical, read last first)
# is exactly the encoding of its value
def wn_inv(x: String, -n: Nat, -rest: String) -> @k: Nat -> @ds: List<&2, Nat> -> {LBoolMisc.wn_canon(ds) == True{} : Bool}
  -> {LWire.wo_go(k, LWire.wo_peek(x), ds) == Wr.Got{n, rest} : Wr.Dec<Nat>} -> {LString.wn_emit(ds, x) == Wr.put_nat(n, rest) : String}:
  match x:
    case SNil{}:
      k => ds => cd => h => LA.wn_bad_got({LString.wn_emit(ds, SNil{}) == Wr.put_nat(n, rest) : String}, n, rest,
        Equal.trans(Wr.Dec<Nat>, Wr.Bad{}, LWire.wo_go(k, (Wr.Other{}, SNil{}), ds), Wr.Got{n, rest},
          Equal.sym(Wr.Dec<Nat>, LWire.wo_go(k, (Wr.Other{}, SNil{}), ds), Wr.Bad{}, LWire.wn_gother(k, ds, SNil{})), h))
    case SCon{+c, +t}:
      k => ds => cd => h => wn_invh(Wr.tok(c), k, ds, c, t, n, rest, cd, h, {==}, wn_inv(t, n, rest))

def wn_ex0h(tk: Wr.Tok, +c: Char, +c2: Char, +x2: String, -n: Nat, -rest: String,
  et: {Wr.tok(c) == Wr.Dig{0n} : Wr.Tok}, et2: {Wr.tok(c2) == tk : Wr.Tok},
  h: {LWire.wo_end((tk, x2), [0n]) == Wr.Got{n, rest} : Wr.Dec<Nat>})
  -> {SCon{c, SCon{c2, x2}} == Wr.put_nat(n, rest) : String}:
  match tk:
    case Wr.Dig{d}:
      LA.wn_bad_got({SCon{c, SCon{c2, x2}} == Wr.put_nat(n, rest) : String}, n, rest, h)
    case Wr.Comma{}:
      %h : {SCon{c, SCon{c2, x2}} == wn_put_dec(_) : String}
      %Equal.sym(Char, c, Wr.dchar(0n), wn_tdi_c(c, 0n, et)) : {SCon{_, SCon{c2, x2}} == Wr.put_nat(LNatMisc.wo_value([0n]), x2) : String}
      %Equal.sym(Char, c2, ',', wn_tok_comma_inv(c2, et2)) : {SCon{Wr.dchar(0n), SCon{_, x2}} == Wr.put_nat(LNatMisc.wo_value([0n]), x2) : String}
      {==}
    case Wr.Other{}:
      LA.wn_bad_got({SCon{c, SCon{c2, x2}} == Wr.put_nat(n, rest) : String}, n, rest, h)

def wn_ex0(x: String, +c: Char, -n: Nat, -rest: String, et: {Wr.tok(c) == Wr.Dig{0n} : Wr.Tok},
  h: {LWire.wo_end(LWire.wo_peek(x), [0n]) == Wr.Got{n, rest} : Wr.Dec<Nat>}) -> {SCon{c, x} == Wr.put_nat(n, rest) : String}:
  match x:
    case SNil{}:
      LA.wn_bad_got({SCon{c, SNil{}} == Wr.put_nat(n, rest) : String}, n, rest, h)
    case SCon{+c2, +x2}:
      wn_ex0h(Wr.tok(c2), c, c2, x2, n, rest, et, {==}, h)

def wn_exh(tk: Wr.Tok, +c: Char, +x: String, -n: Nat, -rest: String,
  h: {LWire.wo_first((tk, x)) == Wr.Got{n, rest} : Wr.Dec<Nat>}, +et: {Wr.tok(c) == tk : Wr.Tok})
  -> {SCon{c, x} == Wr.put_nat(n, rest) : String}:
  match tk:
    case Wr.Dig{+d}:
      match d:
        case 0n:
          wn_ex0(x, c, n, rest, et, h)
        case 1n+p:
          +r = wn_inv(x, n, rest)(13n, [1n+p], wn_tdi_lt(c, 1n+p, et), h)
          %Equal.sym(Char, c, Wr.dchar(1n+p), wn_tdi_c(c, 1n+p, et)) : {SCon{_, x} == Wr.put_nat(n, rest) : String}
          r
    case Wr.Comma{}:
      LA.wn_bad_got({SCon{c, x} == Wr.put_nat(n, rest) : String}, n, rest, h)
    case Wr.Other{}:
      LA.wn_bad_got({SCon{c, x} == Wr.put_nat(n, rest) : String}, n, rest, h)

def Wire.wire_nat_exact(s, n, rest, h):
  match s:
    case SNil{}:
      LA.wn_bad_got({SNil{} == Wr.put_nat(n, rest) : String}, n, rest, h)
    case SCon{+c, +x}:
      wn_exh(Wr.tok(c), c, x, n, rest,
        Equal.trans(Wr.Dec<Nat>, LWire.wo_get_nat(SCon{c, x}), Wr.get_nat(SCon{c, x}), Wr.Got{n, rest},
          Equal.sym(Wr.Dec<Nat>, Wr.get_nat(SCon{c, x}), LWire.wo_get_nat(SCon{c, x}), LWire.wn_eqv(SCon{c, x})), h), {==})
