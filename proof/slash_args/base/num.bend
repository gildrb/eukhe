# eukhe: lemmas of area slash_args: a numeral's value (sa_number) against
# the code's text tests, for LAW slash_args_digits_value. Two words compare
# as their values (san.wcmp), so two digits compare as their values
# (san.dig); a numeral of digits is below ten to its length (san.bound);
# of one length, two numerals compare in text order as in value order
# (san.same); a shorter one is the smaller when the longer leads with a
# digit other than `0` (san.short). No bound is ever computed: the values
# meet only through these lemmas.

import Base
import ../../../laws/slash_args/model.bend as SlashArgs
import ../../base/staging.bend as LStg
import ../base.bend as LA

# Logic
# -----

def san.eq_lt(-G: Type, e: {EQ{} == LT{} : Cmp}) -> G:
  LStg.stg.absurd(G, Equal.cong(Cmp, Bool, z => Cmp.is_eq(z), EQ{}, LT{}, e))

def san.gt_lt(-G: Type, e: {GT{} == LT{} : Cmp}) -> G:
  LStg.stg.absurdF(G, Equal.cong(Cmp, Bool, z => Cmp.is_lt(z), GT{}, LT{}, e))

def san.and_l(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LStg.stg.absurdF({False{} == True{} : Bool}, e)

def san.and_r(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LStg.stg.absurdF({b == True{} : Bool}, e)

# c, then d on a tie
def san.then(c: Cmp, d: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      d
    case GT{}:
      GT{}

# Naturals
# --------

def san.assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), san.assoc(p, b, c))

def san.add0(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, san.add0(p))

def san.add_s(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), san.add_s(p, b))

# the same p added on the left keeps the order
def san.addl(p: Nat, -a: Nat, -b: Nat) -> {Nat.cmp(Nat.add(p, a), Nat.add(p, b)) == Nat.cmp(a, b) : Cmp}:
  match p:
    case 0n:
      {==}
    case 1n++q:
      san.addl(q, a, b)

# below p, below p + z
def san.ltadd(v: Nat, p: Nat, -z: Nat, h: {Nat.cmp(v, p) == LT{} : Cmp}) -> {Nat.cmp(v, Nat.add(p, z)) == LT{} : Cmp}:
  match v:
    case 0n:
      match p:
        case 0n:
          san.eq_lt({Nat.cmp(0n, Nat.add(0n, z)) == LT{} : Cmp}, h)
        case 1n++q:
          {==}
    case 1n++u:
      match p:
        case 0n:
          san.gt_lt({Nat.cmp(1n+u, Nat.add(0n, z)) == LT{} : Cmp}, h)
        case 1n++q:
          san.ltadd(u, q, z, h)

def san.flip(a: Nat, b: Nat, h: {Nat.cmp(a, b) == LT{} : Cmp}) -> {Nat.cmp(b, a) == GT{} : Cmp}:
  match a:
    case 0n:
      match b:
        case 0n:
          san.eq_lt({Nat.cmp(0n, 0n) == GT{} : Cmp}, h)
        case 1n++q:
          {==}
    case 1n++p:
      match b:
        case 0n:
          san.gt_lt({Nat.cmp(0n, 1n+p) == GT{} : Cmp}, h)
        case 1n++q:
          san.flip(p, q, h)

def san.unflip(a: Nat, b: Nat, h: {Nat.cmp(a, b) == GT{} : Cmp}) -> {Nat.cmp(b, a) == LT{} : Cmp}:
  match a:
    case 0n:
      match b:
        case 0n:
          LA.sab.gt_eq({Nat.cmp(0n, 0n) == LT{} : Cmp}, Equal.sym(Cmp, EQ{}, GT{}, h))
        case 1n++q:
          san.gt_lt({Nat.cmp(1n+q, 0n) == LT{} : Cmp}, Equal.sym(Cmp, LT{}, GT{}, h))
    case 1n++p:
      match b:
        case 0n:
          {==}
        case 1n++q:
          san.unflip(p, q, h)

def san.cmp_eq(a: Nat, b: Nat, h: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n++q:
          LA.sab.lt_eq({0n == 1n+q : Nat}, h)
    case 1n++p:
      match b:
        case 0n:
          LA.sab.gt_eq({1n+p == 0n : Nat}, h)
        case 1n++q:
          Equal.cong(Nat, Nat, z => 1n+z, p, q, san.cmp_eq(p, q, h))

# m below n + 1: m at most n
def san.lt_succ_le(m: Nat, n: Nat, h: {Nat.cmp(m, 1n+n) == LT{} : Cmp}) -> {Cmp.is_le(Nat.cmp(m, n)) == True{} : Bool}:
  match m:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n++q:
          {==}
    case 1n++p:
      match p:
        case 0n:
          match n:
            case 0n:
              san.eq_lt({Cmp.is_le(Nat.cmp(1n, 0n)) == True{} : Bool}, h)
            case 1n++q:
              match q:
                case 0n:
                  {==}
                case 1n++r:
                  {==}
        case 1n++r:
          match n:
            case 0n:
              san.gt_lt({Cmp.is_le(Nat.cmp(2n+r, 0n)) == True{} : Bool}, h)
            case 1n++q:
              san.lt_succ_le(1n+r, q, h)

# m at most n: n - m + m is n
def san.sub_add(m: Nat, n: Nat, h: {Cmp.is_le(Nat.cmp(m, n)) == True{} : Bool}) -> {Nat.add(Nat.sub(n, m), m) == n : Nat}:
  match m:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n++q:
          san.add0(1n+q)
    case 1n++p:
      match n:
        case 0n:
          LStg.stg.absurdF({Nat.add(Nat.sub(0n, 1n+p), 1n+p) == 0n : Nat}, h)
        case 1n++q:
          Equal.trans(Nat, Nat.add(Nat.sub(q, p), 1n+p), 1n+Nat.add(Nat.sub(q, p), p), 1n+q, san.add_s(Nat.sub(q, p), p), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.sub(q, p), p), q, san.sub_add(p, q, h)))

# Powers of ten
# -------------

def san.pow_pos(n: Nat) -> {Nat.cmp(0n, Nat.pow(10n, n)) == LT{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      san.ltadd(0n, Nat.pow(10n, m), Nat.mul(9n, Nat.pow(10n, m)), san.pow_pos(m))

def san.lt_mul10(x: Nat, +p: Nat, h: {Nat.cmp(x, p) == LT{} : Cmp}) -> {Nat.cmp(x, Nat.mul(10n, p)) == LT{} : Cmp}:
  san.ltadd(x, p, Nat.mul(9n, p), h)

# below 10^m: below 10^(d+m)
def san.pow_up(d: Nat, +x: Nat, +m: Nat, h: {Nat.cmp(x, Nat.pow(10n, m)) == LT{} : Cmp}) -> {Nat.cmp(x, Nat.pow(10n, Nat.add(d, m))) == LT{} : Cmp}:
  match d:
    case 0n:
      h
    case 1n++e:
      san.lt_mul10(x, Nat.pow(10n, Nat.add(e, m)), san.pow_up(e, x, m, h))

# x * P + v against y * P + w, v and w below P: x against y, then v
# against w
def san.lex(x: Nat, y: Nat, +p: Nat, +v: Nat, +w: Nat, +hv: {Nat.cmp(v, p) == LT{} : Cmp}, +hw: {Nat.cmp(w, p) == LT{} : Cmp}) -> {Nat.cmp(Nat.add(Nat.mul(x, p), v), Nat.add(Nat.mul(y, p), w)) == san.then(Nat.cmp(x, y), Nat.cmp(v, w)) : Cmp}:
  match x:
    case 0n:
      match y:
        case 0n:
          {==}
        case 1n++b:
          Equal.trans(Cmp, Nat.cmp(v, Nat.add(Nat.add(p, Nat.mul(b, p)), w)), Nat.cmp(v, Nat.add(p, Nat.add(Nat.mul(b, p), w))), LT{}, Equal.cong(Nat, Cmp, z => Nat.cmp(v, z), Nat.add(Nat.add(p, Nat.mul(b, p)), w), Nat.add(p, Nat.add(Nat.mul(b, p), w)), san.assoc(p, Nat.mul(b, p), w)), san.ltadd(v, p, Nat.add(Nat.mul(b, p), w), hv))
    case 1n++a:
      match y:
        case 0n:
          Equal.trans(Cmp, Nat.cmp(Nat.add(Nat.add(p, Nat.mul(a, p)), v), w), Nat.cmp(Nat.add(p, Nat.add(Nat.mul(a, p), v)), w), GT{}, Equal.cong(Nat, Cmp, z => Nat.cmp(z, w), Nat.add(Nat.add(p, Nat.mul(a, p)), v), Nat.add(p, Nat.add(Nat.mul(a, p), v)), san.assoc(p, Nat.mul(a, p), v)), san.flip(w, Nat.add(p, Nat.add(Nat.mul(a, p), v)), san.ltadd(w, p, Nat.add(Nat.mul(a, p), v), hw)))
        case 1n++b:
        %Equal.sym(Nat, Nat.add(Nat.add(p, Nat.mul(a, p)), v), Nat.add(p, Nat.add(Nat.mul(a, p), v)), san.assoc(p, Nat.mul(a, p), v)) : {Nat.cmp(_, Nat.add(Nat.add(p, Nat.mul(b, p)), w)) == san.then(Nat.cmp(a, b), Nat.cmp(v, w)) : Cmp}
        %Equal.sym(Nat, Nat.add(Nat.add(p, Nat.mul(b, p)), w), Nat.add(p, Nat.add(Nat.mul(b, p), w)), san.assoc(p, Nat.mul(b, p), w)) : {Nat.cmp(Nat.add(p, Nat.add(Nat.mul(a, p), v)), _) == san.then(Nat.cmp(a, b), Nat.cmp(v, w)) : Cmp}
        Equal.trans(Cmp, Nat.cmp(Nat.add(p, Nat.add(Nat.mul(a, p), v)), Nat.add(p, Nat.add(Nat.mul(b, p), w))), Nat.cmp(Nat.add(Nat.mul(a, p), v), Nat.add(Nat.mul(b, p), w)), san.then(Nat.cmp(a, b), Nat.cmp(v, w)), san.addl(p, Nat.add(Nat.mul(a, p), v), Nat.add(Nat.mul(b, p), w)), san.lex(a, b, p, v, w, hv, hw))

# a lead digit d above 0: v below P is below d * P + w
def san.lead_lt(d: Nat, +v: Nat, +p: Nat, +w: Nat, hd: {Nat.cmp(0n, d) == LT{} : Cmp}, hv: {Nat.cmp(v, p) == LT{} : Cmp}) -> {Nat.cmp(v, Nat.add(Nat.mul(d, p), w)) == LT{} : Cmp}:
  match d:
    case 0n:
      san.eq_lt({Nat.cmp(v, Nat.add(Nat.mul(0n, p), w)) == LT{} : Cmp}, hd)
    case 1n++e:
      Equal.trans(Cmp, Nat.cmp(v, Nat.add(Nat.add(p, Nat.mul(e, p)), w)), Nat.cmp(v, Nat.add(p, Nat.add(Nat.mul(e, p), w))), LT{}, Equal.cong(Nat, Cmp, z => Nat.cmp(v, z), Nat.add(Nat.add(p, Nat.mul(e, p)), w), Nat.add(p, Nat.add(Nat.mul(e, p), w)), san.assoc(p, Nat.mul(e, p), w)), san.ltadd(v, p, Nat.add(Nat.mul(e, p), w), hv))

# Words and digits
# ----------------

def san.B(b: Bool, x: Nat) -> Nat:
  match b:
    case False{}:
      Nat.double(x)
    case True{}:
      1n+Nat.double(x)

def san.wb(b: Bool, -p: Nat, -t: Word(p)) -> {Word.to_nat(1n+p, WCon{b, t}) == san.B(b, Word.to_nat(p, t)) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# the higher bits decide, the low bit on a tie
def san.step(x: Nat, y: Nat, a: Bool, b: Bool) -> {Nat.cmp(san.B(a, x), san.B(b, y)) == Word.cmp.fin(a, b, Nat.cmp(x, y)) : Cmp}:
  match x y:
    case 0n 0n:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 0n 1n+q:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 0n:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n++p 1n++q:
      match a b:
        case False{} False{}:
          san.step(p, q, False{}, False{})
        case False{} True{}:
          san.step(p, q, False{}, True{})
        case True{} False{}:
          san.step(p, q, True{}, False{})
        case True{} True{}:
          san.step(p, q, True{}, True{})

# two words compare as their values
def san.wcmp(+n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), san.wcmp(p, at, bt)) : {Word.cmp.fin(ab, bb, _) == Nat.cmp(Word.to_nat(1n+p, WCon{ab, at}), Word.to_nat(1n+p, WCon{bb, bt})) : Cmp}
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{ab, at}), san.B(ab, Word.to_nat(p, at)), san.wb(ab, p, at)) : {Word.cmp.fin(ab, bb, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))) == Nat.cmp(_, Word.to_nat(1n+p, WCon{bb, bt})) : Cmp}
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{bb, bt}), san.B(bb, Word.to_nat(p, bt)), san.wb(bb, p, bt)) : {Word.cmp.fin(ab, bb, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))) == Nat.cmp(san.B(ab, Word.to_nat(p, at)), _) : Cmp}
          Equal.sym(Cmp, Nat.cmp(san.B(ab, Word.to_nat(p, at)), san.B(bb, Word.to_nat(p, bt))), Word.cmp.fin(ab, bb, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))), san.step(Word.to_nat(p, at), Word.to_nat(p, bt), ab, bb))

def san.ucmp(+x: U32, +y: U32) -> {U32.cmp(x, y) == Nat.cmp(U32.to_nat(x), U32.to_nat(y)) : Cmp}:
  match x y:
    case U32{+a} U32{+b}:
      san.wcmp(32n, a, b)

def san.le_lt(a: Nat, b: Nat, h: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}) -> {Nat.cmp(a, 1n+b) == LT{} : Cmp}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      match b:
        case 0n:
          LStg.stg.absurdF({Nat.cmp(1n+p, 1n) == LT{} : Cmp}, h)
        case 1n++q:
          san.le_lt(p, q, h)

# n at most k + 9: n - k below 10
def san.dlt(k: Nat, n: Nat, h: {Cmp.is_le(Nat.cmp(n, Nat.add(k, 9n))) == True{} : Bool}) -> {Nat.cmp(Nat.sub(n, k), 10n) == LT{} : Cmp}:
  match k:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n++m:
          san.le_lt(m, 8n, h)
    case 1n++j:
      match n:
        case 0n:
          {==}
        case 1n++m:
          san.dlt(j, m, h)

# n at least k and not k: n - k above 0
def san.dpos(k: Nat, n: Nat, hge: {Cmp.is_ge(Nat.cmp(n, k)) == True{} : Bool}, hne: {Cmp.is_eq(Nat.cmp(n, k)) == False{} : Bool}) -> {Nat.cmp(0n, Nat.sub(n, k)) == LT{} : Cmp}:
  match k:
    case 0n:
      match n:
        case 0n:
          LStg.stg.absurd({Nat.cmp(0n, Nat.sub(0n, 0n)) == LT{} : Cmp}, hne)
        case 1n++m:
          {==}
    case 1n++j:
      match n:
        case 0n:
          LStg.stg.absurdF({Nat.cmp(0n, Nat.sub(0n, 1n+j)) == LT{} : Cmp}, hge)
        case 1n++m:
          san.dpos(j, m, hge, hne)

# a and b at least k: a - k against b - k is a against b
def san.csub(k: Nat, a: Nat, b: Nat, ha: {Cmp.is_ge(Nat.cmp(a, k)) == True{} : Bool}, hb: {Cmp.is_ge(Nat.cmp(b, k)) == True{} : Bool}) -> {Nat.cmp(Nat.sub(a, k), Nat.sub(b, k)) == Nat.cmp(a, b) : Cmp}:
  match k:
    case 0n:
      match a:
        case 0n:
          match b:
            case 0n:
              {==}
            case 1n++q:
              {==}
        case 1n++p:
          match b:
            case 0n:
              {==}
            case 1n++q:
              {==}
    case 1n++j:
      match a:
        case 0n:
          LStg.stg.absurdF({Nat.cmp(Nat.sub(0n, 1n+j), Nat.sub(b, 1n+j)) == Nat.cmp(0n, b) : Cmp}, ha)
        case 1n++p:
          match b:
            case 0n:
              LStg.stg.absurdF({Nat.cmp(Nat.sub(1n+p, 1n+j), Nat.sub(0n, 1n+j)) == Nat.cmp(1n+p, 0n) : Cmp}, hb)
            case 1n++q:
              san.csub(j, p, q, ha, hb)

# a digit's code at least that of `0`, as values
def san.ge48(+x: U32, h: {U32.is_ge(x, 48) == True{} : Bool}) -> {Cmp.is_ge(Nat.cmp(U32.to_nat(x), 48n)) == True{} : Bool}:
  Equal.trans(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(x), U32.to_nat(48))), Cmp.is_ge(U32.cmp(x, 48)), True{}, Equal.cong(Cmp, Bool, z => Cmp.is_ge(z), Nat.cmp(U32.to_nat(x), U32.to_nat(48)), U32.cmp(x, 48), Equal.sym(Cmp, U32.cmp(x, 48), Nat.cmp(U32.to_nat(x), U32.to_nat(48)), san.ucmp(x, 48))), h)

# an ASCII digit's value is below 10
def san.d10(c: Char, h: {Char.is_digit(c) == True{} : Bool}) -> {Nat.cmp(SlashArgs.sa_dval(c), 10n) == LT{} : Cmp}:
  match c:
    case Chr{+x}:
      san.dlt(48n, U32.to_nat(x), Equal.trans(Bool, Cmp.is_le(Nat.cmp(U32.to_nat(x), U32.to_nat(57))), Cmp.is_le(U32.cmp(x, 57)), True{}, Equal.cong(Cmp, Bool, z => Cmp.is_le(z), Nat.cmp(U32.to_nat(x), U32.to_nat(57)), U32.cmp(x, 57), Equal.sym(Cmp, U32.cmp(x, 57), Nat.cmp(U32.to_nat(x), U32.to_nat(57)), san.ucmp(x, 57))), san.and_r(U32.is_ge(x, 48), U32.is_le(x, 57), h)))

# an ASCII digit other than `0` has a value above 0
def san.d0(c: Char, +h: {Bool.and(Char.is_digit(c), Bool.not(Char.is_eq(c, '0'))) == True{} : Bool}) -> {Nat.cmp(0n, SlashArgs.sa_dval(c)) == LT{} : Cmp}:
  match c:
    case Chr{+x}:
      +hd = san.and_l(Char.is_digit(Chr{x}), Bool.not(Char.is_eq(Chr{x}, '0')), h)
      +hz = LA.sab.not_t(Char.is_eq(Chr{x}, '0'), san.and_r(Char.is_digit(Chr{x}), Bool.not(Char.is_eq(Chr{x}, '0')), h))
      san.dpos(48n, U32.to_nat(x), san.ge48(x, san.and_l(U32.is_ge(x, 48), U32.is_le(x, 57), hd)), Equal.trans(Bool, Cmp.is_eq(Nat.cmp(U32.to_nat(x), U32.to_nat(48))), Cmp.is_eq(U32.cmp(x, 48)), False{}, Equal.cong(Cmp, Bool, z => Cmp.is_eq(z), Nat.cmp(U32.to_nat(x), U32.to_nat(48)), U32.cmp(x, 48), Equal.sym(Cmp, U32.cmp(x, 48), Nat.cmp(U32.to_nat(x), U32.to_nat(48)), san.ucmp(x, 48))), hz))

# two ASCII digits compare as their values
def san.dig(+x: U32, +y: U32, hx: {Char.is_digit(Chr{x}) == True{} : Bool}, hy: {Char.is_digit(Chr{y}) == True{} : Bool}) -> {U32.cmp(x, y) == Nat.cmp(SlashArgs.sa_dval(Chr{x}), SlashArgs.sa_dval(Chr{y})) : Cmp}:
  Equal.trans(Cmp, U32.cmp(x, y), Nat.cmp(U32.to_nat(x), U32.to_nat(y)), Nat.cmp(Nat.sub(U32.to_nat(x), 48n), Nat.sub(U32.to_nat(y), 48n)), san.ucmp(x, y), Equal.sym(Cmp, Nat.cmp(Nat.sub(U32.to_nat(x), 48n), Nat.sub(U32.to_nat(y), 48n)), Nat.cmp(U32.to_nat(x), U32.to_nat(y)), san.csub(48n, U32.to_nat(x), U32.to_nat(y), san.ge48(x, san.and_l(U32.is_ge(x, 48), U32.is_le(x, 57), hx)), san.ge48(y, san.and_l(U32.is_ge(y, 48), U32.is_le(y, 57), hy)))))

# Numerals
# --------

# a numeral of digits is below ten to its length
def san.bound(s: String, +h: {SlashArgs.sa_digits(s) == True{} : Bool}) -> {Nat.cmp(SlashArgs.sa_number(s), Nat.pow(10n, String.length(s))) == LT{} : Cmp}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      +p = Nat.pow(10n, String.length(u))
      +d = SlashArgs.sa_dval(c)
      +v = SlashArgs.sa_number(u)
      +hc = san.and_l(Char.is_digit(c), SlashArgs.sa_digits(u), h)
      +hu = san.and_r(Char.is_digit(c), SlashArgs.sa_digits(u), h)
      Equal.trans(Cmp, Nat.cmp(Nat.add(Nat.mul(d, p), v), Nat.mul(10n, p)), Nat.cmp(Nat.add(Nat.mul(d, p), v), Nat.add(Nat.mul(10n, p), 0n)), LT{}, Equal.cong(Nat, Cmp, z => Nat.cmp(Nat.add(Nat.mul(d, p), v), z), Nat.mul(10n, p), Nat.add(Nat.mul(10n, p), 0n), Equal.sym(Nat, Nat.add(Nat.mul(10n, p), 0n), Nat.mul(10n, p), san.add0(Nat.mul(10n, p)))), Equal.trans(Cmp, Nat.cmp(Nat.add(Nat.mul(d, p), v), Nat.add(Nat.mul(10n, p), 0n)), san.then(Nat.cmp(d, 10n), Nat.cmp(v, 0n)), LT{}, san.lex(d, 10n, p, v, 0n, san.bound(u, hu), san.pow_pos(String.length(u))), Equal.cong(Cmp, Cmp, z => san.then(z, Nat.cmp(v, 0n)), Nat.cmp(d, 10n), LT{}, san.d10(c, hc))))

# past a decided char, text order keeps its answer
def san.ord_ne(k: Cmp, t: String, u: String, h: {Cmp.is_eq(k) == False{} : Bool}) -> {String.order.go(t, u, k) == k : Cmp}:
  match k:
    case EQ{}:
      LStg.stg.absurd({String.order.go(t, u, EQ{}) == EQ{} : Cmp}, h)
    case LT{}:
      match t:
        case SNil{}:
          match u:
            case SNil{}:
              {==}
            case SCon{x, r}:
              match x:
                case Chr{y}:
                  {==}
        case SCon{x, r}:
          match x:
            case Chr{y}:
              match u:
                case SNil{}:
                  {==}
                case SCon{x2, r2}:
                  match x2:
                    case Chr{y2}:
                      {==}
    case GT{}:
      match t:
        case SNil{}:
          match u:
            case SNil{}:
              {==}
            case SCon{x, r}:
              match x:
                case Chr{y}:
                  {==}
        case SCon{x, r}:
          match x:
            case Chr{y}:
              match u:
                case SNil{}:
                  {==}
                case SCon{x2, r2}:
                  match x2:
                    case Chr{y2}:
                      {==}

def san.then_ord(k: Cmp, t: String, u: String) -> {san.then(k, String.order.go(t, u, EQ{})) == String.order.go(t, u, k) : Cmp}:
  match k:
    case LT{}:
      Equal.sym(Cmp, String.order.go(t, u, LT{}), LT{}, san.ord_ne(LT{}, t, u, {==}))
    case EQ{}:
      {==}
    case GT{}:
      Equal.sym(Cmp, String.order.go(t, u, GT{}), GT{}, san.ord_ne(GT{}, t, u, {==}))

def san.same.rest(+x: U32, +y: U32, +t: String, +u: String, hx: {Char.is_digit(Chr{x}) == True{} : Bool}, hy: {Char.is_digit(Chr{y}) == True{} : Bool}, ih: {Nat.cmp(SlashArgs.sa_number(t), SlashArgs.sa_number(u)) == String.order.go(t, u, EQ{}) : Cmp}) -> {san.then(Nat.cmp(SlashArgs.sa_dval(Chr{x}), SlashArgs.sa_dval(Chr{y})), Nat.cmp(SlashArgs.sa_number(t), SlashArgs.sa_number(u))) == String.order.go(t, u, U32.cmp(x, y)) : Cmp}:
  %Equal.sym(Cmp, Nat.cmp(SlashArgs.sa_number(t), SlashArgs.sa_number(u)), String.order.go(t, u, EQ{}), ih) : {san.then(Nat.cmp(SlashArgs.sa_dval(Chr{x}), SlashArgs.sa_dval(Chr{y})), _) == String.order.go(t, u, U32.cmp(x, y)) : Cmp}
  %san.dig(x, y, hx, hy) : {san.then(_, String.order.go(t, u, EQ{})) == String.order.go(t, u, U32.cmp(x, y)) : Cmp}
  san.then_ord(U32.cmp(x, y), t, u)

def san.same.cc(+x: U32, +t: String, +y: U32, +u: String, hx: {Char.is_digit(Chr{x}) == True{} : Bool}, hy: {Char.is_digit(Chr{y}) == True{} : Bool}, bt: {Nat.cmp(SlashArgs.sa_number(t), Nat.pow(10n, String.length(t))) == LT{} : Cmp}, bu: {Nat.cmp(SlashArgs.sa_number(u), Nat.pow(10n, String.length(u))) == LT{} : Cmp}, el: {String.length(t) == String.length(u) : Nat}, ih: {Nat.cmp(SlashArgs.sa_number(t), SlashArgs.sa_number(u)) == String.order.go(t, u, EQ{}) : Cmp}) -> {Nat.cmp(SlashArgs.sa_number(SCon{Chr{x}, t}), SlashArgs.sa_number(SCon{Chr{y}, u})) == String.order.go(t, u, U32.cmp(x, y)) : Cmp}:
  +p = Nat.pow(10n, String.length(t))
  +dx = SlashArgs.sa_dval(Chr{x})
  +dy = SlashArgs.sa_dval(Chr{y})
  +vt = SlashArgs.sa_number(t)
  +vu = SlashArgs.sa_number(u)
  +ep = Equal.cong(Nat, Nat, z => Nat.pow(10n, z), String.length(t), String.length(u), el)
  %ep : {Nat.cmp(Nat.add(Nat.mul(dx, p), vt), Nat.add(Nat.mul(dy, _), vu)) == String.order.go(t, u, U32.cmp(x, y)) : Cmp}
  Equal.trans(Cmp, Nat.cmp(Nat.add(Nat.mul(dx, p), vt), Nat.add(Nat.mul(dy, p), vu)), san.then(Nat.cmp(dx, dy), Nat.cmp(vt, vu)), String.order.go(t, u, U32.cmp(x, y)), san.lex(dx, dy, p, vt, vu, bt, Equal.trans(Cmp, Nat.cmp(vu, p), Nat.cmp(vu, Nat.pow(10n, String.length(u))), LT{}, Equal.cong(Nat, Cmp, z => Nat.cmp(vu, z), p, Nat.pow(10n, String.length(u)), ep), bu)), san.same.rest(x, y, t, u, hx, hy, ih))

def san.same.cs(c: Char, +t: String, c2: Char, +u: String, hx: {Char.is_digit(c) == True{} : Bool}, hy: {Char.is_digit(c2) == True{} : Bool}, bt: {Nat.cmp(SlashArgs.sa_number(t), Nat.pow(10n, String.length(t))) == LT{} : Cmp}, bu: {Nat.cmp(SlashArgs.sa_number(u), Nat.pow(10n, String.length(u))) == LT{} : Cmp}, el: {String.length(t) == String.length(u) : Nat}, ih: {Nat.cmp(SlashArgs.sa_number(t), SlashArgs.sa_number(u)) == String.order.go(t, u, EQ{}) : Cmp}) -> {Nat.cmp(SlashArgs.sa_number(SCon{c, t}), SlashArgs.sa_number(SCon{c2, u})) == String.order.go(SCon{c, t}, SCon{c2, u}, EQ{}) : Cmp}:
  match c:
    case Chr{+x}:
      match c2:
        case Chr{+y}:
          san.same.cc(x, t, y, u, hx, hy, bt, bu, el, ih)

# two numerals of digits of one length compare in value order as in text
# order
def san.same(a: String, b: String, +ha: {SlashArgs.sa_digits(a) == True{} : Bool}, +hb: {SlashArgs.sa_digits(b) == True{} : Bool}, +hl: {Nat.cmp(String.length(a), String.length(b)) == EQ{} : Cmp}) -> {Nat.cmp(SlashArgs.sa_number(a), SlashArgs.sa_number(b)) == String.order.go(a, b, EQ{}) : Cmp}:
  match a:
    case SNil{}:
      match b:
        case SNil{}:
          {==}
        case SCon{c, u}:
          LA.sab.lt_eq({Nat.cmp(SlashArgs.sa_number(SNil{}), SlashArgs.sa_number(SCon{c, u})) == String.order.go(SNil{}, SCon{c, u}, EQ{}) : Cmp}, hl)
    case SCon{+c, +t}:
      match b:
        case SNil{}:
          LA.sab.gt_eq({Nat.cmp(SlashArgs.sa_number(SCon{c, t}), SlashArgs.sa_number(SNil{})) == String.order.go(SCon{c, t}, SNil{}, EQ{}) : Cmp}, hl)
        case SCon{+c2, +u}:
          san.same.cs(c, t, c2, u, san.and_l(Char.is_digit(c), SlashArgs.sa_digits(t), ha), san.and_l(Char.is_digit(c2), SlashArgs.sa_digits(u), hb), san.bound(t, san.and_r(Char.is_digit(c), SlashArgs.sa_digits(t), ha)), san.bound(u, san.and_r(Char.is_digit(c2), SlashArgs.sa_digits(u), hb)), san.cmp_eq(String.length(t), String.length(u), hl), san.same(t, u, san.and_r(Char.is_digit(c), SlashArgs.sa_digits(t), ha), san.and_r(Char.is_digit(c2), SlashArgs.sa_digits(u), hb), hl))

# a numeral a of digits shorter than c then u, c a digit other than `0`,
# is the smaller
def san.short(+a: String, +c: Char, +u: String, +ha: {SlashArgs.sa_digits(a) == True{} : Bool}, hc: {Bool.and(Char.is_digit(c), Bool.not(Char.is_eq(c, '0'))) == True{} : Bool}, hl: {Nat.cmp(String.length(a), 1n+String.length(u)) == LT{} : Cmp}) -> {Nat.cmp(SlashArgs.sa_number(a), SlashArgs.sa_number(SCon{c, u})) == LT{} : Cmp}:
  +la = String.length(a)
  +lu = String.length(u)
  +va = SlashArgs.sa_number(a)
  +le = san.lt_succ_le(la, lu, hl)
  +h1 = Equal.trans(Cmp, Nat.cmp(va, Nat.pow(10n, lu)), Nat.cmp(va, Nat.pow(10n, Nat.add(Nat.sub(lu, la), la))), LT{}, Equal.cong(Nat, Cmp, z => Nat.cmp(va, Nat.pow(10n, z)), lu, Nat.add(Nat.sub(lu, la), la), Equal.sym(Nat, Nat.add(Nat.sub(lu, la), la), lu, san.sub_add(la, lu, le))), san.pow_up(Nat.sub(lu, la), va, la, san.bound(a, ha)))
  san.lead_lt(SlashArgs.sa_dval(c), va, Nat.pow(10n, lu), SlashArgs.sa_number(u), san.d0(c, hc), h1)

def san.fit.lt(+d: Char, +t: String, +m: Char, +mt: String, +hs: {SlashArgs.sa_digits(SCon{d, t}) == True{} : Bool}, +hml: {Bool.and(Char.is_digit(m), Bool.not(Char.is_eq(m, '0'))) == True{} : Bool}, +e: {Nat.cmp(String.length(SCon{d, t}), String.length(SCon{m, mt})) == LT{} : Cmp}) -> {Bool.or(Nat.is_lt(String.length(SCon{d, t}), String.length(SCon{m, mt})), Bool.and(Nat.is_eq(String.length(SCon{d, t}), String.length(SCon{m, mt})), String.is_le(SCon{d, t}, SCon{m, mt}))) == Nat.is_le(SlashArgs.sa_number(SCon{d, t}), SlashArgs.sa_number(SCon{m, mt})) : Bool}:
  %Equal.sym(Cmp, Nat.cmp(String.length(SCon{d, t}), String.length(SCon{m, mt})), LT{}, e) : {Bool.or(Cmp.is_lt(_), Bool.and(Cmp.is_eq(_), String.is_le(SCon{d, t}, SCon{m, mt}))) == Nat.is_le(SlashArgs.sa_number(SCon{d, t}), SlashArgs.sa_number(SCon{m, mt})) : Bool}
  %Equal.sym(Cmp, Nat.cmp(SlashArgs.sa_number(SCon{d, t}), SlashArgs.sa_number(SCon{m, mt})), LT{}, san.short(SCon{d, t}, m, mt, hs, hml, e)) : {True{} == Cmp.is_le(_) : Bool}
  {==}

def san.fit.gt(+d: Char, +t: String, +m: Char, +mt: String, +hsl: {Bool.and(Char.is_digit(d), Bool.not(Char.is_eq(d, '0'))) == True{} : Bool}, +hm: {SlashArgs.sa_digits(SCon{m, mt}) == True{} : Bool}, +e: {Nat.cmp(String.length(SCon{d, t}), String.length(SCon{m, mt})) == GT{} : Cmp}) -> {Bool.or(Nat.is_lt(String.length(SCon{d, t}), String.length(SCon{m, mt})), Bool.and(Nat.is_eq(String.length(SCon{d, t}), String.length(SCon{m, mt})), String.is_le(SCon{d, t}, SCon{m, mt}))) == Nat.is_le(SlashArgs.sa_number(SCon{d, t}), SlashArgs.sa_number(SCon{m, mt})) : Bool}:
  %Equal.sym(Cmp, Nat.cmp(String.length(SCon{d, t}), String.length(SCon{m, mt})), GT{}, e) : {Bool.or(Cmp.is_lt(_), Bool.and(Cmp.is_eq(_), String.is_le(SCon{d, t}, SCon{m, mt}))) == Nat.is_le(SlashArgs.sa_number(SCon{d, t}), SlashArgs.sa_number(SCon{m, mt})) : Bool}
  %Equal.sym(Cmp, Nat.cmp(SlashArgs.sa_number(SCon{d, t}), SlashArgs.sa_number(SCon{m, mt})), GT{}, san.flip(SlashArgs.sa_number(SCon{m, mt}), SlashArgs.sa_number(SCon{d, t}), san.short(SCon{m, mt}, d, t, hm, hsl, san.unflip(String.length(SCon{d, t}), String.length(SCon{m, mt}), e)))) : {False{} == Cmp.is_le(_) : Bool}
  {==}

def san.fit.eq(+d: Char, +t: String, +m: Char, +mt: String, +hs: {SlashArgs.sa_digits(SCon{d, t}) == True{} : Bool}, +hm: {SlashArgs.sa_digits(SCon{m, mt}) == True{} : Bool}, +e: {Nat.cmp(String.length(SCon{d, t}), String.length(SCon{m, mt})) == EQ{} : Cmp}) -> {Bool.or(Nat.is_lt(String.length(SCon{d, t}), String.length(SCon{m, mt})), Bool.and(Nat.is_eq(String.length(SCon{d, t}), String.length(SCon{m, mt})), String.is_le(SCon{d, t}, SCon{m, mt}))) == Nat.is_le(SlashArgs.sa_number(SCon{d, t}), SlashArgs.sa_number(SCon{m, mt})) : Bool}:
  %Equal.sym(Cmp, Nat.cmp(String.length(SCon{d, t}), String.length(SCon{m, mt})), EQ{}, e) : {Bool.or(Cmp.is_lt(_), Bool.and(Cmp.is_eq(_), String.is_le(SCon{d, t}, SCon{m, mt}))) == Nat.is_le(SlashArgs.sa_number(SCon{d, t}), SlashArgs.sa_number(SCon{m, mt})) : Bool}
  %Equal.sym(Cmp, Nat.cmp(SlashArgs.sa_number(SCon{d, t}), SlashArgs.sa_number(SCon{m, mt})), String.order.go(SCon{d, t}, SCon{m, mt}, EQ{}), san.same(SCon{d, t}, SCon{m, mt}, hs, hm, e)) : {Cmp.is_le(String.order.go(SCon{d, t}, SCon{m, mt}, EQ{})) == Cmp.is_le(_) : Bool}
  {==}

def san.fit.at(k: Cmp, +d: Char, +t: String, +m: Char, +mt: String, +hs: {SlashArgs.sa_digits(SCon{d, t}) == True{} : Bool}, +hsl: {Bool.and(Char.is_digit(d), Bool.not(Char.is_eq(d, '0'))) == True{} : Bool}, +hm: {SlashArgs.sa_digits(SCon{m, mt}) == True{} : Bool}, +hml: {Bool.and(Char.is_digit(m), Bool.not(Char.is_eq(m, '0'))) == True{} : Bool}, e: {Nat.cmp(String.length(SCon{d, t}), String.length(SCon{m, mt})) == k : Cmp}) -> {Bool.or(Nat.is_lt(String.length(SCon{d, t}), String.length(SCon{m, mt})), Bool.and(Nat.is_eq(String.length(SCon{d, t}), String.length(SCon{m, mt})), String.is_le(SCon{d, t}, SCon{m, mt}))) == Nat.is_le(SlashArgs.sa_number(SCon{d, t}), SlashArgs.sa_number(SCon{m, mt})) : Bool}:
  match k:
    case LT{}:
      san.fit.lt(d, t, m, mt, hs, hml, e)
    case EQ{}:
      san.fit.eq(d, t, m, mt, hs, hm, e)
    case GT{}:
      san.fit.gt(d, t, m, mt, hsl, hm, e)

# the code's test of the numeral s against the bound numeral m (fewer
# digits, or as many and at most m in text order) is the order of their
# values
def san.fit(+d: Char, +t: String, +m: Char, +mt: String, +hs: {SlashArgs.sa_digits(SCon{d, t}) == True{} : Bool}, +hsl: {Bool.and(Char.is_digit(d), Bool.not(Char.is_eq(d, '0'))) == True{} : Bool}, +hm: {SlashArgs.sa_digits(SCon{m, mt}) == True{} : Bool}, +hml: {Bool.and(Char.is_digit(m), Bool.not(Char.is_eq(m, '0'))) == True{} : Bool}) -> {Bool.or(Nat.is_lt(String.length(SCon{d, t}), String.length(SCon{m, mt})), Bool.and(Nat.is_eq(String.length(SCon{d, t}), String.length(SCon{m, mt})), String.is_le(SCon{d, t}, SCon{m, mt}))) == Nat.is_le(SlashArgs.sa_number(SCon{d, t}), SlashArgs.sa_number(SCon{m, mt})) : Bool}:
  san.fit.at(Nat.cmp(String.length(SCon{d, t}), String.length(SCon{m, mt})), d, t, m, mt, hs, hsl, hm, hml, {==})
