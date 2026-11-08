# eukhe: lemmas of the METRIC line parser (bend/autoresearch/line.bend):
# each stage read forward on the text the spec spells, and inverted

import Base
import ../../../bend/autoresearch/dec.bend as D
import ../../../bend/autoresearch/line.bend as L
import ../../../spec/autoresearch/decimal.bend as SD
import ../../../spec/autoresearch/metric_line.bend as SL

# Logic
# -----

def al.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True: anything follows
def al.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : al.If(_, G)
  Unit{}

def al.MIf(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some: anything follows
def al.none_some(-A: Data, -b: A, -G: Type, e: {None{} == Some{b} : Maybe<&2, A>}) -> G:
  %e : al.MIf(A, _, G)
  Unit{}

def al.mget(-A: Data, m: Maybe<&2, A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def al.some_inj(-A: Data, -a: A, -b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => al.mget(A, m, a), Some{a}, Some{b}, e)

def al.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      al.absurd({False{} == True{} : Bool}, e)

def al.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      al.absurd({b == True{} : Bool}, e)

def al.and_tt(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      al.absurd({False{} == True{} : Bool}, ea)

def al.scon_eq(-c: Char, -x: String, -y: String, e: {x == y : String}) -> {SCon{c, x} == SCon{c, y} : String}:
  Equal.cong(String, String, s => SCon{c, s}, x, y, e)

def al.nat_eq(+x: Nat, +y: Nat, e: {Nat.is_eq(x, y) == True{} : Bool}) -> {x == y : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      al.absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      al.absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %al.nat_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

# U32.is_eq is equality (copied from proof/wire/wire_bool_exact.bend)
# ------------------------------------------------------------------

def al.lt_eq(-G: Type, e: {LT{} == EQ{} : Cmp}) -> G:
  al.absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), LT{}, EQ{}, e))

def al.gt_eq(-G: Type, e: {GT{} == EQ{} : Cmp}) -> G:
  al.absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), GT{}, EQ{}, e))

def al.cmp_eq_fin(-p: Nat, -at: Word(p), -bt: Word(p), t: Cmp, +ab: Bool, +bb: Bool,
  et: {Word.cmp(p, at, bt) == t : Cmp},
  rec: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)},
  e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp})
  -> {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}:
  match t:
    case LT{}:
      al.lt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case GT{}:
      al.gt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt, rec(et))
        case False{} True{}:
          al.lt_eq({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, e)
        case True{} False{}:
          al.gt_eq({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, e)
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt, rec(et))

def al.word_cmp_eq(+n: Nat, +a: Word(n), +b: Word(n)) ->
  {Word.cmp(n, a, b) == EQ{} : Cmp} -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          e => {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          e => al.cmp_eq_fin(p, at, bt, Word.cmp(p, at, bt), ab, bb, {==},
            al.word_cmp_eq(p, at, bt), e)

def al.cmp_eq(+a: U32, +b: U32) -> {U32.cmp(a, b) == EQ{} : Cmp} -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      e => Equal.cong(Word(32n), U32, w => U32{w}, x, y, al.word_cmp_eq(32n, x, y)(e))

def al.sound_fin(+a: U32, +b: U32, t: Cmp, et: {U32.cmp(a, b) == t : Cmp},
  e: {Cmp.is_eq(t) == True{} : Bool}) -> {a == b : U32}:
  match t:
    case LT{}:
      al.absurd({a == b : U32}, e)
    case EQ{}:
      al.cmp_eq(a, b)(et)
    case GT{}:
      al.absurd({a == b : U32}, e)

def al.eq_sound(+a: U32, +b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  al.sound_fin(a, b, U32.cmp(a, b), {==}, e)

# same_char true: the chars are equal
def al.char_eq(c: Char, k: Char, e: {L.same_char(c, k) == True{} : Bool}) -> {c == k : Char}:
  match c k:
    case Chr{+x} Chr{+y}:
      Equal.cong(U32, Char, u => Chr{u}, x, y, al.eq_sound(x, y, e))

# Chars
# -----

# F(n) is True, n is k, F(k) is False: anything follows
def al.bad(-F: Nat -> Bool, -n: Nat, -k: Nat, -G: Type, e: {n == k : Nat}, h: {F(n) == True{} : Bool}, f: {F(k) == False{} : Bool}) -> G:
  al.absurd(G, Equal.trans(Bool, False{}, F(n), True{}, Equal.sym(Bool, F(n), False{}, Equal.trans(Bool, F(n), F(k), False{}, Equal.cong(Nat, Bool, F, n, k, e), f)), h))

def al.nb(+n: Nat, h: {SL.is_name(n) == True{} : Bool}, b1: Bool, eb1: {Nat.is_eq(n, 32n) == b1 : Bool}, b2: Bool, eb2: {Nat.is_eq(n, 9n) == b2 : Bool}) -> {Bool.or(b1, b2) == False{} : Bool}:
  match b1:
    case True{}:
      al.bad(k => SL.is_name(k), n, 32n, {Bool.or(True{}, b2) == False{} : Bool}, al.nat_eq(n, 32n, eb1), h, {==})
    case False{}:
      match b2:
        case True{}:
          al.bad(k => SL.is_name(k), n, 9n, {Bool.or(False{}, True{}) == False{} : Bool}, al.nat_eq(n, 9n, eb2), h, {==})
        case False{}:
          {==}

# a name char is no blank
def al.name_not_blank(+n: Nat, h: {SL.is_name(n) == True{} : Bool}) -> {L.blank(n) == False{} : Bool}:
  al.nb(n, h, Nat.is_eq(n, 32n), {==}, Nat.is_eq(n, 9n), {==})

def al.fst(-A: Type, -B: Type, p: A & B) -> A:
  match p:
    case (a, b):
      a

def al.snd(-A: Type, -B: Type, p: A & B) -> B:
  match p:
    case (a, b):
      b

# F(c) is True, c is k, F(k) is False: anything follows
def al.badc(-F: Char -> Bool, -c: Char, -k: Char, -G: Type, e: {c == k : Char}, h: {F(c) == True{} : Bool}, f: {F(k) == False{} : Bool}) -> G:
  al.absurd(G, Equal.trans(Bool, False{}, F(c), True{}, Equal.sym(Bool, F(c), False{}, Equal.trans(Bool, F(c), F(k), False{}, Equal.cong(Char, Bool, F, c, k, e), f)), h))

# Digits
# ------

# c is the char of the digit d
def al.DigOk(c: Char, d: Nat) -> Type:
  {c == SL.char(Nat.add(48n, d)) : Char} & {Nat.is_lt(d, 10n) == True{} : Bool}

def al.digit_of(b1: Bool, b2: Bool, -d0: Nat, -d: Nat, e: {L.digit.of(Bool.and(b1, b2), d0) == Some{d} : Maybe<&2, Nat>}) -> {b1 == True{} : Bool} & ({b2 == True{} : Bool} & {d0 == d : Nat}):
  match b1:
    case False{}:
      al.none_some(Nat, d, {False{} == True{} : Bool} & ({b2 == True{} : Bool} & {d0 == d : Nat}), e)
    case True{}:
      match b2:
        case False{}:
          al.none_some(Nat, d, {True{} == True{} : Bool} & ({False{} == True{} : Bool} & {d0 == d : Nat}), e)
        case True{}:
          ({==}, ({==}, al.some_inj(Nat, d0, d, e)))

def al.digit_fin(+x: U32, +d0: Nat, -d: Nat, h: {Nat.is_lt(d0, 10n) == True{} : Bool} & ({U32.is_eq(x, U32.from_nat(Nat.add(48n, d0))) == True{} : Bool} & {d0 == d : Nat})) -> al.DigOk(Chr{x}, d):
  match h:
    case (h1, hr):
      match hr:
        case (h2, h3):
          %h3 : al.DigOk(Chr{x}, _)
          (Equal.cong(U32, Char, u => Chr{u}, x, U32.from_nat(Nat.add(48n, d0)), al.eq_sound(x, U32.from_nat(Nat.add(48n, d0)), h2)), h1)

# the digit a char reads is the char's digit
def al.digit_sound(c: Char, -d: Nat, e: {L.digit(c) == Some{d} : Maybe<&2, Nat>}) -> al.DigOk(c, d):
  match c:
    case Chr{+x}:
      +d0 = Nat.sub(U32.to_nat(x), 48n)
      al.digit_fin(x, d0, d, al.digit_of(Nat.is_lt(d0, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d0))), d0, d, e))

# the facts of the chars of the ten digits
def al.DF(d: Nat) -> Type:
  {L.digit(SL.char(Nat.add(48n, d))) == Some{d} : Maybe<&2, Nat>} & ({SL.is_trail(SL.code(SL.char(Nat.add(48n, d)))) == False{} : Bool} & {L.same_char(SL.char(Nat.add(48n, d)), '-') == False{} : Bool})

def al.dig10(d: Nat, lt: {Nat.is_lt(d, 10n) == True{} : Bool}) -> al.DF(d):
  match d:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+d0:
      match d0:
        case 0n:
          ({==}, ({==}, {==}))
        case 1n+d01:
          match d01:
            case 0n:
              ({==}, ({==}, {==}))
            case 1n+d012:
              match d012:
                case 0n:
                  ({==}, ({==}, {==}))
                case 1n+d0123:
                  match d0123:
                    case 0n:
                      ({==}, ({==}, {==}))
                    case 1n+d01234:
                      match d01234:
                        case 0n:
                          ({==}, ({==}, {==}))
                        case 1n+d012345:
                          match d012345:
                            case 0n:
                              ({==}, ({==}, {==}))
                            case 1n+d0123456:
                              match d0123456:
                                case 0n:
                                  ({==}, ({==}, {==}))
                                case 1n+d01234567:
                                  match d01234567:
                                    case 0n:
                                      ({==}, ({==}, {==}))
                                    case 1n+d012345678:
                                      match d012345678:
                                        case 0n:
                                          ({==}, ({==}, {==}))
                                        case 1n+d0123456789:
                                          match d0123456789:
                                            case 0n:
                                              al.absurd(al.DF(10n), lt)
                                            case 1n+y:
                                              al.absurd(al.DF(11n+y), lt)

def al.trail_nd_f(-c: Char, -d: Nat, h: {SL.is_trail(SL.code(c)) == True{} : Bool}, hc: {c == SL.char(Nat.add(48n, d)) : Char}, df: al.DF(d)) -> {L.digit(c) == None{} : Maybe<&2, Nat>}:
  match df:
    case (f1, fr):
      match fr:
        case (f2, f3):
          al.badc(k => SL.is_trail(SL.code(k)), c, SL.char(Nat.add(48n, d)), {L.digit(c) == None{} : Maybe<&2, Nat>}, hc, h, f2)

def al.trail_nd_s(-c: Char, +d: Nat, h: {SL.is_trail(SL.code(c)) == True{} : Bool}, ds: al.DigOk(c, d)) -> {L.digit(c) == None{} : Maybe<&2, Nat>}:
  match ds:
    case (hc, hl):
      al.trail_nd_f(c, d, h, hc, al.dig10(d, hl))

def al.trail_nd_m(c: Char, h: {SL.is_trail(SL.code(c)) == True{} : Bool}, m: Maybe<&2, Nat>, em: {L.digit(c) == m : Maybe<&2, Nat>}) -> {L.digit(c) == None{} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      em
    case Some{+d}:
      al.trail_nd_s(c, d, h, al.digit_sound(c, d, em))

# a trailing blank is no digit
def al.trail_nd(+c: Char, h: {SL.is_trail(SL.code(c)) == True{} : Bool}) -> {L.digit(c) == None{} : Maybe<&2, Nat>}:
  al.trail_nd_m(c, h, L.digit(c), {==})

def al.trail_dot_b(c: Char, h: {SL.is_trail(SL.code(c)) == True{} : Bool}, b: Bool, eb: {L.same_char(c, '.') == b : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      al.badc(k => SL.is_trail(SL.code(k)), c, '.', {True{} == False{} : Bool}, al.char_eq(c, '.', eb), h, {==})
    case False{}:
      {==}

# a trailing blank is no point
def al.trail_not_dot(+c: Char, h: {SL.is_trail(SL.code(c)) == True{} : Bool}) -> {L.same_char(c, '.') == False{} : Bool}:
  al.trail_dot_b(c, h, L.same_char(c, '.'), {==})

def al.df1(+d: Nat, lt: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {L.digit(SL.char(Nat.add(48n, d))) == Some{d} : Maybe<&2, Nat>}:
  al.fst({L.digit(SL.char(Nat.add(48n, d))) == Some{d} : Maybe<&2, Nat>}, {SL.is_trail(SL.code(SL.char(Nat.add(48n, d)))) == False{} : Bool} & {L.same_char(SL.char(Nat.add(48n, d)), '-') == False{} : Bool}, al.dig10(d, lt))

def al.df3(+d: Nat, lt: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {L.same_char(SL.char(Nat.add(48n, d)), '-') == False{} : Bool}:
  al.snd({SL.is_trail(SL.code(SL.char(Nat.add(48n, d)))) == False{} : Bool}, {L.same_char(SL.char(Nat.add(48n, d)), '-') == False{} : Bool}, al.snd({L.digit(SL.char(Nat.add(48n, d))) == Some{d} : Maybe<&2, Nat>}, {SL.is_trail(SL.code(SL.char(Nat.add(48n, d)))) == False{} : Bool} & {L.same_char(SL.char(Nat.add(48n, d)), '-') == False{} : Bool}, al.dig10(d, lt)))

# the code's printer spells digits as the spec does
def al.put_spell(ds: List<&2, Nat>, -rest: String) -> {D.put_ds(ds, rest) == SL.spell_ds(ds, rest) : String}:
  match ds:
    case Nil{}:
      {==}
    case d <> t:
      al.scon_eq(D.dchar(d), D.put_ds(t, rest), SL.spell_ds(t, rest), al.put_spell(t, rest))

# the code's trailing test is the spec's
def al.trail_eq(s: String) -> {L.trail_all(s) == SL.all_trail(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          Equal.cong(Bool, Bool, b => Bool.and(SL.is_trail(U32.to_nat(x)), b), L.trail_all(t), SL.all_trail(t), al.trail_eq(t))

# Spans, forward: a run of the class, then a char out of it
# --------------------------------------------------------

def al.span_at_ok(b: Bool, eb: {b == True{} : Bool}, -c: Char, -u: String, r: String & String, -a: String, -rest: String, er: {r == (a, rest) : String & String}) -> {L.span.at(b, c, u, r) == (SCon{c, a}, rest) : String & String}:
  match b:
    case True{}:
      Equal.cong(String & String, String & String, q => L.span.at(True{}, c, u, q), r, (a, rest), er)
    case False{}:
      al.absurd({L.span.at(False{}, c, u, r) == (SCon{c, a}, rest) : String & String}, eb)

def al.span_b_app(a: String, +rest: String, +ok: {SL.all_blank(a) == True{} : Bool}, stop: {L.span_b(rest) == (SNil{}, rest) : String & String}) -> {L.span_b(String.append(a, rest)) == (a, rest) : String & String}:
  match a:
    case SNil{}:
      stop
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          al.span_at_ok(L.blank(U32.to_nat(x)), al.and_l(SL.is_blank(U32.to_nat(x)), SL.all_blank(t), ok), Chr{x}, String.append(t, rest), L.span_b(String.append(t, rest)), t, rest, al.span_b_app(t, rest, al.and_r(SL.is_blank(U32.to_nat(x)), SL.all_blank(t), ok), stop))

def al.span_n_app(a: String, +rest: String, +ok: {SL.all_name(a) == True{} : Bool}, stop: {L.span_n(rest) == (SNil{}, rest) : String & String}) -> {L.span_n(String.append(a, rest)) == (a, rest) : String & String}:
  match a:
    case SNil{}:
      stop
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          al.span_at_ok(L.name_char(U32.to_nat(x)), al.and_l(SL.is_name(U32.to_nat(x)), SL.all_name(t), ok), Chr{x}, String.append(t, rest), L.span_n(String.append(t, rest)), t, rest, al.span_n_app(t, rest, al.and_r(SL.is_name(U32.to_nat(x)), SL.all_name(t), ok), stop))

def al.span_d_at_ok(m: Maybe<&2, Nat>, -d: Nat, em: {m == Some{d} : Maybe<&2, Nat>}, -c: Char, -u: String, r: List<&2, Nat> & String, -a: List<&2, Nat>, -rest: String, er: {r == (a, rest) : List<&2, Nat> & String}) -> {L.span_d.at(m, c, u, r) == (d <> a, rest) : List<&2, Nat> & String}:
  match m:
    case None{}:
      al.none_some(Nat, d, {L.span_d.at(None{}, c, u, r) == (d <> a, rest) : List<&2, Nat> & String}, em)
    case Some{x}:
      %al.some_inj(Nat, x, d, em) : {L.span_d.at(Some{x}, c, u, r) == (_ <> a, rest) : List<&2, Nat> & String}
      Equal.cong(List<&2, Nat> & String, List<&2, Nat> & String, q => L.span_d.at(Some{x}, c, u, q), r, (a, rest), er)

def al.span_d_app(ds: List<&2, Nat>, +rest: String, +ok: {SD.digits_ok(ds) == True{} : Bool}, stop: {L.span_d(rest) == (Nil{}, rest) : List<&2, Nat> & String}) -> {L.span_d(SL.spell_ds(ds, rest)) == (ds, rest) : List<&2, Nat> & String}:
  match ds:
    case Nil{}:
      stop
    case +d <> +t:
      al.span_d_at_ok(L.digit(SL.char(Nat.add(48n, d))), d, al.df1(d, al.and_l(Nat.is_lt(d, 10n), SD.digits_ok(t), ok)), SL.char(Nat.add(48n, d)), SL.spell_ds(t, rest), L.span_d(SL.spell_ds(t, rest)), t, rest, al.span_d_app(t, rest, al.and_r(Nat.is_lt(d, 10n), SD.digits_ok(t), ok), stop))

# Stops
# -----

# the digits stop at a trailing blank or the end
def al.stop_d_trail(tr: String, h: {SL.all_trail(tr) == True{} : Bool}) -> {L.span_d(tr) == (Nil{}, tr) : List<&2, Nat> & String}:
  match tr:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %Equal.sym(Maybe<&2, Nat>, L.digit(c), None{}, al.trail_nd(c, al.and_l(SL.is_trail(SL.code(c)), SL.all_trail(t), h))) : {L.span_d.at(_, c, t, L.span_d(t)) == (Nil{}, SCon{c, t}) : List<&2, Nat> & String}
      {==}

# the blanks stop at a name's first char
def al.stop_b_name(name: String, -rest: String, ne: {SL.nonempty(name) == True{} : Bool}, ok: {SL.all_name(name) == True{} : Bool}) -> {L.span_b(String.append(name, rest)) == (SNil{}, String.append(name, rest)) : String & String}:
  match name:
    case SNil{}:
      al.absurd({L.span_b(rest) == (SNil{}, rest) : String & String}, ne)
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          %Equal.sym(Bool, L.blank(U32.to_nat(x)), False{}, al.name_not_blank(U32.to_nat(x), al.and_l(SL.is_name(U32.to_nat(x)), SL.all_name(t), ok))) : {L.span.at(_, Chr{x}, String.append(t, rest), L.span_b(String.append(t, rest))) == (SNil{}, SCon{Chr{x}, String.append(t, rest)}) : String & String}
          {==}

# Spans, inverted: the span and the rest make the text; the span is of the class
# ------------------------------------------------------------------------------

def al.SB(u: String, q: String & String) -> Type:
  match q:
    case (a, b):
      {String.append(a, b) == u : String} & {SL.all_blank(a) == True{} : Bool}

def al.span_b_at(c: Char, -t: String, b: Bool, eb: {L.blank(L.code(c)) == b : Bool}, r: String & String, ih: al.SB(t, r)) -> al.SB(SCon{c, t}, L.span.at(b, c, t, r)):
  match c:
    case Chr{x}:
      match b:
        case True{}:
          match r:
            case (a, rest):
              match ih:
                case (e1, e2):
                  (al.scon_eq(Chr{x}, String.append(a, rest), t, e1), al.and_tt(SL.is_blank(U32.to_nat(x)), SL.all_blank(a), eb, e2))
        case False{}:
          ({==}, {==})

def al.span_b_inv(u: String) -> al.SB(u, L.span_b(u)):
  match u:
    case SNil{}:
      ({==}, {==})
    case SCon{+c, +t}:
      al.span_b_at(c, t, L.blank(L.code(c)), {==}, L.span_b(t), al.span_b_inv(t))

def al.SN(u: String, q: String & String) -> Type:
  match q:
    case (a, b):
      {String.append(a, b) == u : String} & {SL.all_name(a) == True{} : Bool}

def al.span_n_at(c: Char, -t: String, b: Bool, eb: {L.name_char(L.code(c)) == b : Bool}, r: String & String, ih: al.SN(t, r)) -> al.SN(SCon{c, t}, L.span.at(b, c, t, r)):
  match c:
    case Chr{x}:
      match b:
        case True{}:
          match r:
            case (a, rest):
              match ih:
                case (e1, e2):
                  (al.scon_eq(Chr{x}, String.append(a, rest), t, e1), al.and_tt(SL.is_name(U32.to_nat(x)), SL.all_name(a), eb, e2))
        case False{}:
          ({==}, {==})

def al.span_n_inv(u: String) -> al.SN(u, L.span_n(u)):
  match u:
    case SNil{}:
      ({==}, {==})
    case SCon{+c, +t}:
      al.span_n_at(c, t, L.name_char(L.code(c)), {==}, L.span_n(t), al.span_n_inv(t))

def al.SDg(u: String, q: List<&2, Nat> & String) -> Type:
  match q:
    case (a, b):
      {SL.spell_ds(a, b) == u : String} & {SD.digits_ok(a) == True{} : Bool}

def al.span_d_some(-c: Char, +d: Nat, h: al.DigOk(c, d), -a: List<&2, Nat>, -rest: String, -t: String, e1: {SL.spell_ds(a, rest) == t : String}, e2: {SD.digits_ok(a) == True{} : Bool}) -> {SCon{SL.char(Nat.add(48n, d)), SL.spell_ds(a, rest)} == SCon{c, t} : String} & {Bool.and(Nat.is_lt(d, 10n), SD.digits_ok(a)) == True{} : Bool}:
  match h:
    case (hc, hl):
      ((%hc : {SCon{_, SL.spell_ds(a, rest)} == SCon{c, t} : String}; al.scon_eq(c, SL.spell_ds(a, rest), t, e1)), al.and_tt(Nat.is_lt(d, 10n), SD.digits_ok(a), hl, e2))

def al.span_d_at(+c: Char, -t: String, m: Maybe<&2, Nat>, em: {L.digit(c) == m : Maybe<&2, Nat>}, r: List<&2, Nat> & String, ih: al.SDg(t, r)) -> al.SDg(SCon{c, t}, L.span_d.at(m, c, t, r)):
  match m:
    case None{}:
      ({==}, {==})
    case Some{+d}:
      match r:
        case (a, rest):
          match ih:
            case (e1, e2):
              al.span_d_some(c, d, al.digit_sound(c, d, em), a, rest, t, e1, e2)

def al.span_d_inv(u: String) -> al.SDg(u, L.span_d(u)):
  match u:
    case SNil{}:
      ({==}, {==})
    case SCon{+c, +t}:
      al.span_d_at(c, t, L.digit(c), {==}, L.span_d(t), al.span_d_inv(t))

# Lists and numbers
# -----------------

def al.lcons_eq(-x: Nat, -a: List<&2, Nat>, -b: List<&2, Nat>, e: {a == b : List<&2, Nat>}) -> {x <> a == x <> b : List<&2, Nat>}:
  Equal.cong(List<&2, Nat>, List<&2, Nat>, l => x <> l, a, b, e)

def al.succ_eq(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  Equal.cong(Nat, Nat, n => 1n+n, a, b, e)

# the code's cat is List.append
def al.cat_app(xs: List<&2, Nat>, -ys: List<&2, Nat>) -> {D.cat(xs, ys) == List.append(&2, Nat, xs, ys) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      al.lcons_eq(x, D.cat(t, ys), List.append(&2, Nat, t, ys), al.cat_app(t, ys))

# the code's len is the spec's dlen
def al.len_dlen(xs: List<&2, Nat>) -> {D.len(xs) == SL.dlen(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      al.succ_eq(D.len(t), SL.dlen(t), al.len_dlen(t))

# the code's drop is the spec's trim_lead
def al.drop_trim(xs: List<&2, Nat>) -> {L.drop(xs) == SL.trim_lead(xs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case 0n:
          al.drop_trim(t)
        case 1n+e:
          {==}

def al.app_assoc(a: List<&2, Nat>, -b: List<&2, Nat>, -c: List<&2, Nat>) -> {List.append(&2, Nat, List.append(&2, Nat, a, b), c) == List.append(&2, Nat, a, List.append(&2, Nat, b, c)) : List<&2, Nat>}:
  match a:
    case Nil{}:
      {==}
    case x <> t:
      al.lcons_eq(x, List.append(&2, Nat, List.append(&2, Nat, t, b), c), List.append(&2, Nat, t, List.append(&2, Nat, b, c)), al.app_assoc(t, b, c))

def al.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      al.succ_eq(Nat.add(m, 0n), m, al.add_zero(m))

def al.add_succ(n: Nat, -m: Nat) -> {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      al.succ_eq(Nat.add(p, 1n+m), 1n+Nat.add(p, m), al.add_succ(p, m))

def al.cmp_self(n: Nat) -> {Cmp.is_eq(Nat.cmp(n, n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      al.cmp_self(m)

# shifting by a + b is shifting by a, then by b
def al.shift_add(a: Nat, -b: Nat, x: Nat) -> {SD.shift(Nat.add(a, b), x) == SD.shift(b, SD.shift(a, x)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      al.shift_add(p, b, Nat.mul(x, 10n))

def al.shift_zero(k: Nat) -> {SD.shift(k, 0n) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      al.shift_zero(j)

# k zeros after acc shift it k places
def al.num_zeros(k: Nat, +acc: Nat) -> {SD.num.go(D.zeros(k), acc) == SD.shift(k, acc) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %al.add_zero(Nat.mul(acc, 10n)) : {SD.num.go(D.zeros(j), Nat.add(Nat.mul(acc, 10n), 0n)) == SD.shift(j, _) : Nat}
      al.num_zeros(j, Nat.add(Nat.mul(acc, 10n), 0n))

def al.num_app_zeros(xs: List<&2, Nat>, k: Nat, +acc: Nat) -> {SD.num.go(List.append(&2, Nat, xs, D.zeros(k)), acc) == SD.shift(k, SD.num.go(xs, acc)) : Nat}:
  match xs:
    case Nil{}:
      al.num_zeros(k, acc)
    case x <> t:
      al.num_app_zeros(t, k, Nat.add(Nat.mul(acc, 10n), x))

# leading zeros are worth nothing
def al.num_drop(xs: List<&2, Nat>) -> {SD.num.go(L.drop(xs), 0n) == SD.num.go(xs, 0n) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case 0n:
          al.num_drop(t)
        case 1n+e:
          {==}

# the trailing zeros strip drops
def al.tz.at(r: List<&2, Nat>, x: Nat, m: Nat) -> Nat:
  match r:
    case Nil{}:
      match x:
        case 0n:
          1n+m
        case 1n+e:
          m
    case y <> u:
      m

def al.tz(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> +t:
      al.tz.at(L.strip(t), x, al.tz(t))

def al.strip_tz_at(r: List<&2, Nat>, x: Nat, -m: Nat, -t: List<&2, Nat>, ih: {List.append(&2, Nat, r, D.zeros(m)) == t : List<&2, Nat>}) -> {List.append(&2, Nat, L.strip.at(x, r), D.zeros(al.tz.at(r, x, m))) == x <> t : List<&2, Nat>}:
  match r:
    case Nil{}:
      match x:
        case 0n:
          al.lcons_eq(0n, D.zeros(m), t, ih)
        case 1n+e:
          al.lcons_eq(1n+e, D.zeros(m), t, ih)
    case y <> u:
      al.lcons_eq(x, List.append(&2, Nat, y <> u, D.zeros(m)), t, ih)

# strip drops tz zeros
def al.strip_tz(xs: List<&2, Nat>) -> {List.append(&2, Nat, L.strip(xs), D.zeros(al.tz(xs))) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      al.strip_tz_at(L.strip(t), x, al.tz(t), t, al.strip_tz(t))

def al.dlen_zeros(k: Nat) -> {SL.dlen(D.zeros(k)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      al.succ_eq(SL.dlen(D.zeros(j)), j, al.dlen_zeros(j))

def al.dlen_app_zeros(f: List<&2, Nat>, +k: Nat) -> {SL.dlen(List.append(&2, Nat, f, D.zeros(k))) == Nat.add(k, D.len(f)) : Nat}:
  match f:
    case Nil{}:
      Equal.trans(Nat, SL.dlen(D.zeros(k)), k, Nat.add(k, 0n), al.dlen_zeros(k), Equal.sym(Nat, Nat.add(k, 0n), k, al.add_zero(k)))
    case x <> t:
      Equal.trans(Nat, 1n+SL.dlen(List.append(&2, Nat, t, D.zeros(k))), 1n+Nat.add(k, D.len(t)), Nat.add(k, 1n+D.len(t)), al.succ_eq(SL.dlen(List.append(&2, Nat, t, D.zeros(k))), Nat.add(k, D.len(t)), al.dlen_app_zeros(t, k)), Equal.sym(Nat, Nat.add(k, 1n+D.len(t)), 1n+Nat.add(k, D.len(t)), al.add_succ(k, D.len(t))))

# Reversal: the code's strip is the spec's trim_trail
# --------------------------------------------------

def al.rev_acc(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {SL.rev(xs, acc) == List.append(&2, Nat, SL.rev(xs, Nil{}), acc) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      Equal.trans(List<&2, Nat>, SL.rev(t, x <> acc), List.append(&2, Nat, SL.rev(t, Nil{}), x <> acc), List.append(&2, Nat, SL.rev(t, [x]), acc), al.rev_acc(t, x <> acc), Equal.sym(List<&2, Nat>, List.append(&2, Nat, SL.rev(t, [x]), acc), List.append(&2, Nat, SL.rev(t, Nil{}), x <> acc), Equal.trans(List<&2, Nat>, List.append(&2, Nat, SL.rev(t, [x]), acc), List.append(&2, Nat, List.append(&2, Nat, SL.rev(t, Nil{}), [x]), acc), List.append(&2, Nat, SL.rev(t, Nil{}), x <> acc), Equal.cong(List<&2, Nat>, List<&2, Nat>, l => List.append(&2, Nat, l, acc), SL.rev(t, [x]), List.append(&2, Nat, SL.rev(t, Nil{}), [x]), al.rev_acc(t, [x])), al.app_assoc(SL.rev(t, Nil{}), [x], acc))))

def al.rev_snoc(z: List<&2, Nat>, +x: Nat) -> {SL.rev(List.append(&2, Nat, z, [x]), Nil{}) == x <> SL.rev(z, Nil{}) : List<&2, Nat>}:
  match z:
    case Nil{}:
      {==}
    case +y <> +w:
      Equal.trans(List<&2, Nat>, SL.rev(List.append(&2, Nat, w, [x]), [y]), List.append(&2, Nat, SL.rev(List.append(&2, Nat, w, [x]), Nil{}), [y]), x <> SL.rev(w, [y]), al.rev_acc(List.append(&2, Nat, w, [x]), [y]), Equal.trans(List<&2, Nat>, List.append(&2, Nat, SL.rev(List.append(&2, Nat, w, [x]), Nil{}), [y]), x <> List.append(&2, Nat, SL.rev(w, Nil{}), [y]), x <> SL.rev(w, [y]), Equal.cong(List<&2, Nat>, List<&2, Nat>, l => List.append(&2, Nat, l, [y]), SL.rev(List.append(&2, Nat, w, [x]), Nil{}), x <> SL.rev(w, Nil{}), al.rev_snoc(w, x)), al.lcons_eq(x, List.append(&2, Nat, SL.rev(w, Nil{}), [y]), SL.rev(w, [y]), Equal.sym(List<&2, Nat>, SL.rev(w, [y]), List.append(&2, Nat, SL.rev(w, Nil{}), [y]), al.rev_acc(w, [y])))))

# trim_lead of a list with x after it
def al.tl.at(z: List<&2, Nat>, x: Nat) -> List<&2, Nat>:
  match z:
    case Nil{}:
      SL.trim_lead([x])
    case c <> u:
      List.append(&2, Nat, c <> u, [x])

def al.tl_snoc(a: List<&2, Nat>, -x: Nat) -> {SL.trim_lead(List.append(&2, Nat, a, [x])) == al.tl.at(SL.trim_lead(a), x) : List<&2, Nat>}:
  match a:
    case Nil{}:
      {==}
    case d <> w:
      match d:
        case 0n:
          al.tl_snoc(w, x)
        case 1n+e:
          {==}

def al.strip_at_snoc(wl: List<&2, Nat>, -c: Nat, -x: Nat) -> {L.strip.at(x, List.append(&2, Nat, wl, [c])) == x <> List.append(&2, Nat, wl, [c]) : List<&2, Nat>}:
  match wl:
    case Nil{}:
      {==}
    case y <> u:
      {==}

def al.strip_tl(z: List<&2, Nat>, x: Nat) -> {L.strip.at(x, SL.rev(z, Nil{})) == SL.rev(al.tl.at(z, x), Nil{}) : List<&2, Nat>}:
  match z:
    case Nil{}:
      match x:
        case 0n:
          {==}
        case 1n+e:
          {==}
    case +c <> +u:
      Equal.trans(List<&2, Nat>, L.strip.at(x, SL.rev(u, [c])), x <> SL.rev(u, [c]), SL.rev(List.append(&2, Nat, c <> u, [x]), Nil{}), Equal.trans(List<&2, Nat>, L.strip.at(x, SL.rev(u, [c])), L.strip.at(x, List.append(&2, Nat, SL.rev(u, Nil{}), [c])), x <> SL.rev(u, [c]), Equal.cong(List<&2, Nat>, List<&2, Nat>, r => L.strip.at(x, r), SL.rev(u, [c]), List.append(&2, Nat, SL.rev(u, Nil{}), [c]), al.rev_acc(u, [c])), Equal.trans(List<&2, Nat>, L.strip.at(x, List.append(&2, Nat, SL.rev(u, Nil{}), [c])), x <> List.append(&2, Nat, SL.rev(u, Nil{}), [c]), x <> SL.rev(u, [c]), al.strip_at_snoc(SL.rev(u, Nil{}), c, x), al.lcons_eq(x, List.append(&2, Nat, SL.rev(u, Nil{}), [c]), SL.rev(u, [c]), Equal.sym(List<&2, Nat>, SL.rev(u, [c]), List.append(&2, Nat, SL.rev(u, Nil{}), [c]), al.rev_acc(u, [c]))))), Equal.sym(List<&2, Nat>, SL.rev(List.append(&2, Nat, c <> u, [x]), Nil{}), x <> SL.rev(c <> u, Nil{}), al.rev_snoc(c <> u, x)))

# the code's strip is the spec's trim_trail
def al.strip_trim(xs: List<&2, Nat>) -> {L.strip(xs) == SL.trim_trail(xs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      Equal.trans(List<&2, Nat>, L.strip.at(x, L.strip(t)), L.strip.at(x, SL.rev(SL.trim_lead(SL.rev(t, Nil{})), Nil{})), SL.rev(SL.trim_lead(SL.rev(t, [x])), Nil{}), Equal.cong(List<&2, Nat>, List<&2, Nat>, r => L.strip.at(x, r), L.strip(t), SL.rev(SL.trim_lead(SL.rev(t, Nil{})), Nil{}), al.strip_trim(t)), Equal.trans(List<&2, Nat>, L.strip.at(x, SL.rev(SL.trim_lead(SL.rev(t, Nil{})), Nil{})), SL.rev(al.tl.at(SL.trim_lead(SL.rev(t, Nil{})), x), Nil{}), SL.rev(SL.trim_lead(SL.rev(t, [x])), Nil{}), al.strip_tl(SL.trim_lead(SL.rev(t, Nil{})), x), Equal.sym(List<&2, Nat>, SL.rev(SL.trim_lead(SL.rev(t, [x])), Nil{}), SL.rev(al.tl.at(SL.trim_lead(SL.rev(t, Nil{})), x), Nil{}), Equal.cong(List<&2, Nat>, List<&2, Nat>, l => SL.rev(l, Nil{}), SL.trim_lead(SL.rev(t, [x])), al.tl.at(SL.trim_lead(SL.rev(t, Nil{})), x), Equal.trans(List<&2, Nat>, SL.trim_lead(SL.rev(t, [x])), SL.trim_lead(List.append(&2, Nat, SL.rev(t, Nil{}), [x])), al.tl.at(SL.trim_lead(SL.rev(t, Nil{})), x), Equal.cong(List<&2, Nat>, List<&2, Nat>, l => SL.trim_lead(l), SL.rev(t, [x]), List.append(&2, Nat, SL.rev(t, Nil{}), [x]), al.rev_acc(t, [x])), al.tl_snoc(SL.rev(t, Nil{}), x))))))

# Canonical digits
# ----------------

# the first digit is not 0 (or there is none)
def al.headnz(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case h <> t:
      Nat.is_ne(h, 0n)

def al.drop_headnz(xs: List<&2, Nat>) -> {al.headnz(L.drop(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case 0n:
          al.drop_headnz(t)
        case 1n+e:
          {==}

def al.drop_digits(xs: List<&2, Nat>, h: {SD.digits_ok(xs) == True{} : Bool}) -> {SD.digits_ok(L.drop(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case x <> t:
      match x:
        case 0n:
          al.drop_digits(t, h)
        case 1n+e:
          h

def al.cat_digits(a: List<&2, Nat>, -b: List<&2, Nat>, +ha: {SD.digits_ok(a) == True{} : Bool}, hb: {SD.digits_ok(b) == True{} : Bool}) -> {SD.digits_ok(D.cat(a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case +x <> +t:
      al.and_tt(Nat.is_lt(x, 10n), SD.digits_ok(D.cat(t, b)), al.and_l(Nat.is_lt(x, 10n), SD.digits_ok(t), ha), al.cat_digits(t, b, al.and_r(Nat.is_lt(x, 10n), SD.digits_ok(t), ha), hb))

def al.strip_at_digits(r: List<&2, Nat>, +x: Nat, hx: {Nat.is_lt(x, 10n) == True{} : Bool}, hr: {SD.digits_ok(r) == True{} : Bool}) -> {SD.digits_ok(L.strip.at(x, r)) == True{} : Bool}:
  match r:
    case Nil{}:
      match x:
        case 0n:
          {==}
        case 1n+e:
          al.and_tt(Nat.is_lt(1n+e, 10n), True{}, hx, {==})
    case y <> u:
      al.and_tt(Nat.is_lt(x, 10n), SD.digits_ok(y <> u), hx, hr)

def al.strip_digits(xs: List<&2, Nat>, +h: {SD.digits_ok(xs) == True{} : Bool}) -> {SD.digits_ok(L.strip(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      al.strip_at_digits(L.strip(t), x, al.and_l(Nat.is_lt(x, 10n), SD.digits_ok(t), h), al.strip_digits(t, al.and_r(Nat.is_lt(x, 10n), SD.digits_ok(t), h)))

def al.last_cons(-x: Nat, ys: List<&2, Nat>, h: {SD.last_nz(ys) == True{} : Bool}) -> {SD.last_nz(x <> ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      al.absurd({SD.last_nz([x]) == True{} : Bool}, h)
    case y <> u:
      h

def al.cat_last(a: List<&2, Nat>, +f: List<&2, Nat>, h: {SD.last_nz(f) == True{} : Bool}) -> {SD.last_nz(D.cat(a, f)) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case x <> +t:
      al.last_cons(x, D.cat(t, f), al.cat_last(t, f, h))

def al.last_tail0(t: List<&2, Nat>, h: {SD.last_nz(0n <> t) == True{} : Bool}) -> {SD.last_nz(t) == True{} : Bool}:
  match t:
    case Nil{}:
      al.absurd({SD.last_nz(Nil{}) == True{} : Bool}, h)
    case y <> u:
      h

def al.drop_last(xs: List<&2, Nat>, h: {SD.last_nz(xs) == True{} : Bool}) -> {SD.last_nz(L.drop(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case x <> +t:
      match x:
        case 0n:
          al.drop_last(t, al.last_tail0(t, h))
        case 1n+e:
          h

# strip leaves nothing, or a last digit that is not 0
def al.SS(r: List<&2, Nat>) -> Type:
  {Bool.or(Nat.is_eq(D.len(r), 0n), SD.last_nz(r)) == True{} : Bool}

def al.strip_shape_at(r: List<&2, Nat>, x: Nat, ih: al.SS(r)) -> al.SS(L.strip.at(x, r)):
  match r:
    case Nil{}:
      match x:
        case 0n:
          {==}
        case 1n+e:
          {==}
    case y <> u:
      ih

def al.strip_shape(xs: List<&2, Nat>) -> al.SS(L.strip(xs)):
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      al.strip_shape_at(L.strip(t), x, al.strip_shape(t))

def al.or_mono(x: Bool, -y: Bool, -z: Bool, h: {Bool.or(x, y) == True{} : Bool}, g: {y == True{} : Bool} -> {z == True{} : Bool}) -> {Bool.or(x, z) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      g(h)

def al.or_false(x: Bool, h: {Bool.or(x, False{}) == True{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      h

# Prefix, inverted
# ----------------

def al.prefix_at(+pc: Char, -pt: String, +c: Char, -t: String, -r: String, b: Bool, eb: {L.same_char(c, pc) == b : Bool}, e: {L.prefix.at(b, L.prefix(pt, t)) == Some{r} : Maybe<&2, String>}, ih: {L.prefix(pt, t) == Some{r} : Maybe<&2, String>} -> {String.append(pt, r) == t : String}) -> {SCon{pc, String.append(pt, r)} == SCon{c, t} : String}:
  match b:
    case True{}:
      %al.char_eq(c, pc, eb) : {SCon{_, String.append(pt, r)} == SCon{c, t} : String}
      al.scon_eq(c, String.append(pt, r), t, ih(e))
    case False{}:
      al.none_some(String, r, {SCon{pc, String.append(pt, r)} == SCon{c, t} : String}, e)

# s less the prefix P is r: s is P, then r
def al.prefix_inv(P: String, +s: String, -r: String, e: {L.prefix(P, s) == Some{r} : Maybe<&2, String>}) -> {String.append(P, r) == s : String}:
  match P:
    case SNil{}:
      Equal.sym(String, s, r, al.some_inj(String, s, r, e))
    case SCon{+pc, +pt}:
      match s:
        case SNil{}:
          al.none_some(String, r, {SCon{pc, String.append(pt, r)} == SNil{} : String}, e)
        case SCon{+c, +t}:
          al.prefix_at(pc, pt, c, t, r, L.same_char(c, pc), {==}, e, e2 => al.prefix_inv(pt, t, r, e2))
