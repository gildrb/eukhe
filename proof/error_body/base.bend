# eukhe: lemmas shared by the proofs of area error_body: the order of
# 32-bit words (ebw.*: a code past U+FFFF, the pair U+2028/U+2029 as a
# range), the code's white space is ECMA-262's (ebc.ws), logic and Nat
# facts (ebl.*, ebn.*), appending texts (ebs.*), the code's UTF-16 units
# and prefix (ebu.*), the code's trims (ebr.*)

import Base
import ../../bend/error_body.bend as Eb
import ../../laws/error_body.bend as ErrorBody
import ../base/staging.bend as LStg

# Words
# -----

# the bits of a U32
def ebw.bits(x: U32) -> Word(32n):
  match x:
    case U32{w}:
      w

# whether every bit of w is set
def ebw.max(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Bool.and(b, ebw.max(p, t))

def ebw.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def ebw.fin_flip(c: Cmp, a: Bool, b: Bool) -> {Word.cmp.fin(a, b, ebw.flip(c)) == ebw.flip(Word.cmp.fin(b, a, c)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match a b:
        case True{} True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          {==}
    case GT{}:
      {==}

# a word's order is the flip of the order the other way
def ebw.anti(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, a, b) == ebw.flip(Word.cmp(n, b, a)) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, at, bt), ebw.flip(Word.cmp(p, bt, at)), ebw.anti(p, at, bt)) : {Word.cmp.fin(ab, bb, _) == ebw.flip(Word.cmp.fin(bb, ab, Word.cmp(p, bt, at))) : Cmp}
          ebw.fin_flip(Word.cmp(p, bt, at), ab, bb)

def ebw.lt_le_fin(c: Cmp, x0: Bool) -> {Cmp.is_lt(Word.cmp.fin(False{}, x0, c)) == Cmp.is_le(Word.cmp.fin(True{}, x0, c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match x0:
        case True{}:
          {==}
        case False{}:
          {==}
    case GT{}:
      {==}

def ebw.lt_fin_t(c: Cmp, x0: Bool) -> {Cmp.is_lt(Word.cmp.fin(True{}, x0, c)) == Cmp.is_lt(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match x0:
        case True{}:
          {==}
        case False{}:
          {==}
    case GT{}:
      {==}

def ebw.le_fin_f(c: Cmp, x0: Bool) -> {Cmp.is_le(Word.cmp.fin(False{}, x0, c)) == Cmp.is_le(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match x0:
        case True{}:
          {==}
        case False{}:
          {==}
    case GT{}:
      {==}

def ebw.lt_inc.at(a0: Bool, +p: Nat, +at: Word(p), +x0: Bool, +xt: Word(p), ih: {Cmp.is_lt(Word.cmp(p, at, xt)) == Bool.and(Bool.not(ebw.max(p, at)), Cmp.is_le(Word.cmp(p, Word.inc(p, at), xt))) : Bool}) -> {Cmp.is_lt(Word.cmp(1n+p, WCon{a0, at}, WCon{x0, xt})) == Bool.and(Bool.not(ebw.max(1n+p, WCon{a0, at})), Cmp.is_le(Word.cmp(1n+p, Word.inc(1n+p, WCon{a0, at}), WCon{x0, xt}))) : Bool}:
  match a0:
    case False{}:
      ebw.lt_le_fin(Word.cmp(p, at, xt), x0)
    case True{}:
      %Equal.sym(Bool, Cmp.is_lt(Word.cmp.fin(True{}, x0, Word.cmp(p, at, xt))), Cmp.is_lt(Word.cmp(p, at, xt)), ebw.lt_fin_t(Word.cmp(p, at, xt), x0)) : {_ == Bool.and(Bool.not(ebw.max(p, at)), Cmp.is_le(Word.cmp.fin(False{}, x0, Word.cmp(p, Word.inc(p, at), xt)))) : Bool}
      %Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(False{}, x0, Word.cmp(p, Word.inc(p, at), xt))), Cmp.is_le(Word.cmp(p, Word.inc(p, at), xt)), ebw.le_fin_f(Word.cmp(p, Word.inc(p, at), xt), x0)) : {Cmp.is_lt(Word.cmp(p, at, xt)) == Bool.and(Bool.not(ebw.max(p, at)), _) : Bool}
      ih

# a < x exactly when a + 1 <= x, unless a + 1 wraps
def ebw.lt_inc(n: Nat, a: Word(n), x: Word(n)) -> {Cmp.is_lt(Word.cmp(n, a, x)) == Bool.and(Bool.not(ebw.max(n, a)), Cmp.is_le(Word.cmp(n, Word.inc(n, a), x))) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match a x:
        case WCon{a0, +at} WCon{+x0, +xt}:
          ebw.lt_inc.at(a0, p, at, x0, xt, ebw.lt_inc(p, at, xt))

# a code past U+FFFF: 65536 <= x is 65535 < x
def ebw.astral(x: U32) -> {U32.is_le(65536, x) == U32.is_lt(65535, x) : Bool}:
  match x:
    case U32{+w}:
      Equal.sym(Bool, U32.is_lt(65535, U32{w}), U32.is_le(65536, U32{w}), ebw.lt_inc(32n, ebw.bits(65535), w))

def ebw.pair_fin(c: Cmp, x0: Bool) -> {Bool.or(Cmp.is_eq(Word.cmp.fin(x0, False{}, c)), Cmp.is_eq(Word.cmp.fin(x0, True{}, c))) == Bool.and(Cmp.is_le(Word.cmp.fin(False{}, x0, ebw.flip(c))), Cmp.is_le(Word.cmp.fin(x0, True{}, c))) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match x0:
        case True{}:
          {==}
        case False{}:
          {==}
    case GT{}:
      {==}

# the tail of the bits of a U32
def ebw.tail(x: U32) -> Word(31n):
  match x:
    case U32{w}:
      match w:
        case WCon{b, t}:
          t

# x is U+2028 or U+2029 exactly when it is in the range of the two
def ebw.pair(x: U32) -> {Bool.or(U32.is_eq(x, 8232), U32.is_eq(x, 8233)) == Bool.and(U32.is_le(8232, x), U32.is_le(x, 8233)) : Bool}:
  match x:
    case U32{w}:
      match w:
        case WCon{+x0, +xt}:
          %Equal.sym(Cmp, Word.cmp(31n, ebw.tail(8232), xt), ebw.flip(Word.cmp(31n, xt, ebw.tail(8232))), ebw.anti(31n, ebw.tail(8232), xt)) : {Bool.or(U32.is_eq(U32{WCon{x0, xt}}, 8232), U32.is_eq(U32{WCon{x0, xt}}, 8233)) == Bool.and(Cmp.is_le(Word.cmp.fin(False{}, x0, _)), U32.is_le(U32{WCon{x0, xt}}, 8233)) : Bool}
          ebw.pair_fin(Word.cmp(31n, xt, ebw.tail(8232)), x0)

# Chars
# -----

def ebc.or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ebc.ws_tail(+x: U32) -> {Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279)))))) == Bool.or(ErrorBody.sp_in(x, 8232, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279))))) : Bool}:
  +r = Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279))))
  Equal.trans(Bool, Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), r)), Bool.or(Bool.or(U32.is_eq(x, 8232), U32.is_eq(x, 8233)), r), Bool.or(ErrorBody.sp_in(x, 8232, 8233), r), ebc.or_assoc(U32.is_eq(x, 8232), U32.is_eq(x, 8233), r), Equal.cong(Bool, Bool, z => Bool.or(z, r), Bool.or(U32.is_eq(x, 8232), U32.is_eq(x, 8233)), ErrorBody.sp_in(x, 8232, 8233), ebw.pair(x)))

# the code's white space is the spec's
def ebc.ws(c: Char) -> {Eb.is_ws(c) == ErrorBody.sp_ws(c) : Bool}:
  match c:
    case Chr{+x}:
      Equal.cong(Bool, Bool, z => Bool.or(Bool.and(U32.is_le(9, x), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_le(8192, x), U32.is_le(x, 8202)), z))))), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279)))))), Bool.or(ErrorBody.sp_in(x, 8232, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), Bool.or(U32.is_eq(x, 12288), U32.is_eq(x, 65279))))), ebc.ws_tail(x))


# Logic
# -----

def ebl.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LStg.stg.absurdF({False{} == True{} : Bool}, h)

def ebl.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LStg.stg.absurdF({b == True{} : Bool}, h)

def ebl.not_t(a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LStg.stg.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# Nat
# ---

def ebn.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, ebn.add_zero(p))

def ebn.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), ebn.add_succ(p, b))

def ebn.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), ebn.add_assoc(p, b, c))

def ebn.le0(b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a <= a + b
def ebn.le_add(a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      ebn.le0(b)
    case 1n+p:
      ebn.le_add(p, b)

# n + z <= x: n <= x
def ebn.le_add_l(n: Nat, +z: Nat, x: Nat, e: {Nat.is_le(Nat.add(n, z), x) == True{} : Bool}) -> {Nat.is_le(n, x) == True{} : Bool}:
  match n x:
    case 0n y:
      ebn.le0(y)
    case 1n+p 0n:
      LStg.stg.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      ebn.le_add_l(p, z, q, e)

# n + z <= x: z <= x - n
def ebn.le_sub(n: Nat, +z: Nat, x: Nat, e: {Nat.is_le(Nat.add(n, z), x) == True{} : Bool}) -> {Nat.is_le(z, Nat.sub(x, n)) == True{} : Bool}:
  match n x:
    case 0n 0n:
      e
    case 0n 1n+q:
      e
    case 1n+p 0n:
      LStg.stg.absurdF({Nat.is_le(z, Nat.sub(0n, 1n+p)) == True{} : Bool}, e)
    case 1n+p 1n+q:
      ebn.le_sub(p, z, q, e)

# n <= x and x < n + y: x - n < y
def ebn.lt_sub(n: Nat, x: Nat, +y: Nat, le: {Nat.is_le(n, x) == True{} : Bool}, lt: {Nat.is_lt(x, Nat.add(n, y)) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(x, n), y) == True{} : Bool}:
  match n x:
    case 0n 0n:
      lt
    case 0n 1n+q:
      lt
    case 1n+p 0n:
      LStg.stg.absurdF({Nat.is_lt(Nat.sub(0n, 1n+p), y) == True{} : Bool}, le)
    case 1n+p 1n+q:
      ebn.lt_sub(p, q, y, le, lt)

# x < a and a <= b: x < b
def ebn.lt_le(x: Nat, a: Nat, b: Nat, h1: {Nat.is_lt(x, a) == True{} : Bool}, h2: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(x, b) == True{} : Bool}:
  match x a b:
    case 0n 0n w:
      LStg.stg.absurdF({Nat.is_lt(0n, w) == True{} : Bool}, h1)
    case 0n 1n+p 0n:
      LStg.stg.absurdF({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
    case 0n 1n+p 1n+q:
      {==}
    case 1n+r 0n w:
      LStg.stg.absurdF({Nat.is_lt(1n+r, w) == True{} : Bool}, h1)
    case 1n+r 1n+p 0n:
      LStg.stg.absurdF({Nat.is_lt(1n+r, 0n) == True{} : Bool}, h2)
    case 1n+r 1n+p 1n+q:
      ebn.lt_le(r, p, q, h1, h2)

# x < y: not y <= x
def ebn.lt_not_le(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_le(y, x) == False{} : Bool}:
  match x y:
    case 0n 0n:
      LStg.stg.absurdF({Nat.is_le(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LStg.stg.absurdF({Nat.is_le(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      ebn.lt_not_le(p, q, h)

# Texts
# -----

def ebs.app_nil(a: String) -> {String.append(a, SNil{}) == a : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, z => SCon{h, z}, String.append(t, SNil{}), t, ebs.app_nil(t))

def ebs.app_assoc(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, z => SCon{h, z}, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), ebs.app_assoc(t, b, c))

# `<q> (<s>): ` then m is `<q> (<s>): <m>`
def ebs.lead(+q: String, +s: String, +m: String) -> {String.concat([q, " (", s, "): ", m]) == String.append(String.concat([q, " (", s, "): "]), m) : String}:
  +b = String.append(" (", String.append(s, "): "))
  %Equal.sym(String, String.append(String.append(q, b), m), String.append(q, String.append(b, m)), ebs.app_assoc(q, b, m)) : {String.concat([q, " (", s, "): ", m]) == _ : String}
  %Equal.sym(String, String.append(String.append(s, "): "), m), String.append(s, String.append("): ", m)), ebs.app_assoc(s, "): ", m)) : {String.concat([q, " (", s, "): ", m]) == String.append(q, String.append(" (", _)) : String}
  %Equal.sym(String, String.append(m, SNil{}), m, ebs.app_nil(m)) : {String.append(q, String.append(" (", String.append(s, String.append("): ", _)))) == String.append(q, String.append(" (", String.append(s, String.append("): ", m)))) : String}
  {==}

# `<q> (<s>)`, then `: `, then x is `<q> (<s>): <x>`
def ebs.label(+q: String, +s: String, +x: String) -> {String.concat([q, " (", s, "): ", x]) == String.concat([String.concat([q, " (", s, ")"]), ": ", x]) : String}:
  +b = String.append(" (", String.append(s, ")"))
  +c = String.append(": ", String.append(x, SNil{}))
  %Equal.sym(String, String.append(String.append(q, b), c), String.append(q, String.append(b, c)), ebs.app_assoc(q, b, c)) : {String.concat([q, " (", s, "): ", x]) == _ : String}
  %Equal.sym(String, String.append(String.append(s, ")"), c), String.append(s, String.append(")", c)), ebs.app_assoc(s, ")", c)) : {String.concat([q, " (", s, "): ", x]) == String.append(q, String.append(" (", _)) : String}
  {==}

# UTF-16 units
# ------------

def ebu.step(a: Bool, l: Nat, -p: Nat, -u: Nat, ih: {u == Nat.add(l, p) : Nat}) -> {Nat.add(Eb.units1.at(a), u) == 1n+Nat.add(l, ErrorBody.sp_pairs.at(a, p)) : Nat}:
  match a:
    case True{}:
      %Equal.sym(Nat, u, Nat.add(l, p), ih) : {Nat.add(2n, _) == 1n+Nat.add(l, 1n+p) : Nat}
      %Equal.sym(Nat, Nat.add(l, 1n+p), 1n+Nat.add(l, p), ebn.add_succ(l, p)) : {Nat.add(2n, Nat.add(l, p)) == 1n+_ : Nat}
      {==}
    case False{}:
      %Equal.sym(Nat, u, Nat.add(l, p), ih) : {Nat.add(1n, _) == 1n+Nat.add(l, p) : Nat}
      {==}

# the code's UTF-16 units of a text are its chars and its chars past U+FFFF
def ebu.units(s: String) -> {Eb.units(s) == ErrorBody.sp_units(s) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          %Equal.sym(Bool, U32.is_le(65536, x), U32.is_lt(65535, x), ebw.astral(x)) : {Nat.add(Eb.units1.at(_), Eb.units(t)) == ErrorBody.sp_units(SCon{Chr{x}, t}) : Nat}
          ebu.step(U32.is_lt(65535, x), String.length(t), ErrorBody.sp_pairs(t), Eb.units(t), ebu.units(t))

# the code's units of kept, c, rest are those of kept, c and of rest
def ebu.snoc(kept: String, +c: Char, +rest: String) -> {Eb.units(String.append(kept, SCon{c, rest})) == Nat.add(Eb.units(String.append(kept, SCon{c, SNil{}})), Eb.units(rest)) : Nat}:
  match kept:
    case SNil{}:
      %Equal.sym(Nat, Nat.add(Eb.units1(c), 0n), Eb.units1(c), ebn.add_zero(Eb.units1(c))) : {Nat.add(Eb.units1(c), Eb.units(rest)) == Nat.add(_, Eb.units(rest)) : Nat}
      {==}
    case SCon{+k, ks}:
      %Equal.sym(Nat, Eb.units(String.append(ks, SCon{c, rest})), Nat.add(Eb.units(String.append(ks, SCon{c, SNil{}})), Eb.units(rest)), ebu.snoc(ks, c, rest)) : {Nat.add(Eb.units1(k), _) == Nat.add(Nat.add(Eb.units1(k), Eb.units(String.append(ks, SCon{c, SNil{}}))), Eb.units(rest)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(Eb.units1(k), Eb.units(String.append(ks, SCon{c, SNil{}}))), Eb.units(rest)), Nat.add(Eb.units1(k), Nat.add(Eb.units(String.append(ks, SCon{c, SNil{}})), Eb.units(rest))), ebn.add_assoc(Eb.units1(k), Eb.units(String.append(ks, SCon{c, SNil{}})), Eb.units(rest)))

# the code's prefix of kept, c, rest within room units is kept, when kept
# fits and kept then c does not
def ebu.prefix(kept: String, +c: Char, -rest: String, +room: Nat, +hk: {Nat.is_le(Eb.units(kept), room) == True{} : Bool}, hc: {Nat.is_lt(room, Eb.units(String.append(kept, SCon{c, SNil{}}))) == True{} : Bool}) -> {Eb.prefix(String.append(kept, SCon{c, rest}), room) == kept : String}:
  match kept:
    case SNil{}:
      +hc2 = Equal.trans(Bool, Nat.is_lt(room, Eb.units1(c)), Nat.is_lt(room, Nat.add(Eb.units1(c), 0n)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(room, z), Eb.units1(c), Nat.add(Eb.units1(c), 0n), Equal.sym(Nat, Nat.add(Eb.units1(c), 0n), Eb.units1(c), ebn.add_zero(Eb.units1(c)))), hc)
      %Equal.sym(Bool, Nat.is_le(Eb.units1(c), room), False{}, ebn.lt_not_le(room, Eb.units1(c), hc2)) : {Eb.when(_, u => SCon{c, Eb.prefix(rest, Nat.sub(room, Eb.units1(c)))}, SNil{}) == SNil{} : String}
      {==}
    case SCon{+k, +ks}:
      +n = Eb.units1(k)
      +le = ebn.le_add_l(n, Eb.units(ks), room, hk)
      %Equal.sym(Bool, Nat.is_le(n, room), True{}, le) : {Eb.when(_, u => SCon{k, Eb.prefix(String.append(ks, SCon{c, rest}), Nat.sub(room, n))}, SNil{}) == SCon{k, ks} : String}
      Equal.cong(String, String, z => SCon{k, z}, Eb.prefix(String.append(ks, SCon{c, rest}), Nat.sub(room, n)), ks, ebu.prefix(ks, c, rest, Nat.sub(room, n), ebn.le_sub(n, Eb.units(ks), room, hk), ebn.lt_sub(n, room, Eb.units(String.append(ks, SCon{c, SNil{}})), le, hc)))

# Trims
# -----

# white space only: the code trims its start to nothing
def ebr.start_ws(x: String, +hx: {ErrorBody.sp_all_ws(x) == True{} : Bool}) -> {Eb.trim_start(x) == SNil{} : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      +hc = ebl.and_l(ErrorBody.sp_ws(c), ErrorBody.sp_all_ws(u), hx)
      +hu = ebl.and_r(ErrorBody.sp_ws(c), ErrorBody.sp_all_ws(u), hx)
      %Equal.sym(Bool, Eb.is_ws(c), ErrorBody.sp_ws(c), ebc.ws(c)) : {Eb.when(_, v => Eb.trim_start(u), SCon{c, u}) == SNil{} : String}
      %Equal.sym(Bool, ErrorBody.sp_ws(c), True{}, hc) : {Eb.when(_, v => Eb.trim_start(u), SCon{c, u}) == SNil{} : String}
      ebr.start_ws(u, hu)

# white space p before t: the code trims the start of p then t as of t
def ebr.start(p: String, -t: String, +hp: {ErrorBody.sp_all_ws(p) == True{} : Bool}) -> {Eb.trim_start(String.append(p, t)) == Eb.trim_start(t) : String}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      +hc = ebl.and_l(ErrorBody.sp_ws(c), ErrorBody.sp_all_ws(u), hp)
      +hu = ebl.and_r(ErrorBody.sp_ws(c), ErrorBody.sp_all_ws(u), hp)
      %Equal.sym(Bool, Eb.is_ws(c), ErrorBody.sp_ws(c), ebc.ws(c)) : {Eb.when(_, v => Eb.trim_start(String.append(u, t)), SCon{c, String.append(u, t)}) == Eb.trim_start(t) : String}
      %Equal.sym(Bool, ErrorBody.sp_ws(c), True{}, hc) : {Eb.when(_, v => Eb.trim_start(String.append(u, t)), SCon{c, String.append(u, t)}) == Eb.trim_start(t) : String}
      ebr.start(u, t, hu)

# a text opening with no white space: the code keeps its start
def ebr.start_keep(+c: Char, +u: String, h: {ErrorBody.sp_ws(c) == False{} : Bool}) -> {Eb.trim_start(SCon{c, u}) == SCon{c, u} : String}:
  %Equal.sym(Bool, Eb.is_ws(c), ErrorBody.sp_ws(c), ebc.ws(c)) : {Eb.when(_, v => Eb.trim_start(u), SCon{c, u}) == SCon{c, u} : String}
  %Equal.sym(Bool, ErrorBody.sp_ws(c), False{}, h) : {Eb.when(_, v => Eb.trim_start(u), SCon{c, u}) == SCon{c, u} : String}
  {==}

# white space only: the code trims its end to nothing
def ebr.end_ws(q: String, +hq: {ErrorBody.sp_all_ws(q) == True{} : Bool}) -> {Eb.trim_end(q) == SNil{} : String}:
  match q:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      +hc = ebl.and_l(ErrorBody.sp_ws(c), ErrorBody.sp_all_ws(u), hq)
      +hu = ebl.and_r(ErrorBody.sp_ws(c), ErrorBody.sp_all_ws(u), hq)
      %Equal.sym(String, Eb.trim_end(u), SNil{}, ebr.end_ws(u, hu)) : {Eb.trim_end.at(c, _) == SNil{} : String}
      %Equal.sym(Bool, Eb.is_ws(c), ErrorBody.sp_ws(c), ebc.ws(c)) : {Eb.trim_end.last(c, _) == SNil{} : String}
      %Equal.sym(Bool, ErrorBody.sp_ws(c), True{}, hc) : {Eb.trim_end.last(c, _) == SNil{} : String}
      {==}

# c then u, its last char no white space, then white space q: the code
# trims the end to c then u
def ebr.end_keep(u: String, +c: Char, +q: String, hl: {ErrorBody.sp_ends_ws(u, c) == False{} : Bool}, hq: {ErrorBody.sp_all_ws(q) == True{} : Bool}) -> {Eb.trim_end(String.append(SCon{c, u}, q)) == SCon{c, u} : String}:
  match u:
    case SNil{}:
      %Equal.sym(String, Eb.trim_end(q), SNil{}, ebr.end_ws(q, hq)) : {Eb.trim_end.at(c, _) == SCon{c, SNil{}} : String}
      %Equal.sym(Bool, Eb.is_ws(c), ErrorBody.sp_ws(c), ebc.ws(c)) : {Eb.trim_end.last(c, _) == SCon{c, SNil{}} : String}
      %Equal.sym(Bool, ErrorBody.sp_ws(c), False{}, hl) : {Eb.trim_end.last(c, _) == SCon{c, SNil{}} : String}
      {==}
    case SCon{+d, +w}:
      %Equal.sym(String, Eb.trim_end(String.append(SCon{d, w}, q)), SCon{d, w}, ebr.end_keep(w, d, q, hl, hq)) : {Eb.trim_end.at(c, _) == SCon{c, SCon{d, w}} : String}
      {==}
