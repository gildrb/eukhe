# eukhe: lemmas of the reserve proofs of area budget (bend/budget.bend
# reserve, pick, lack, need, allows, held, fund against
# spec/budget/ledger.bend): the code's lack is the spec's fits
# (br.lack_ok, br.tight_fits), the offer picked is the first that fits
# (br.pick_ok), what every answer of a reservation says of its request
# (br.res, br.res_is), and each law of a reservation from it

import Base
import ../../../bend/budget.bend as B
import ../../../spec/budget/ledger.bend as S
import ./amt.bend as BA

# Logic
# -----

def br.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False == True proves anything
def br.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : br.IfT(_, G)
  Unit{}

def br.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def br.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      br.absurd({b == True{} : Bool}, h)

def br.and_t(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# five that hold: all hold
def br.and5(-b1: Bool, -b2: Bool, -b3: Bool, -b4: Bool, -b5: Bool, e1: {b1 == True{} : Bool}, e2: {b2 == True{} : Bool}, e3: {b3 == True{} : Bool}, e4: {b4 == True{} : Bool}, e5: {b5 == True{} : Bool}) -> {Bool.and(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5)))) == True{} : Bool}:
  br.and_t(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5))), e1, br.and_t(b2, Bool.and(b3, Bool.and(b4, b5)), e2, br.and_t(b3, Bool.and(b4, b5), e3, br.and_t(b4, b5, e4, e5))))

# all five hold: each holds
def br.p1(+b1: Bool, -b2: Bool, -b3: Bool, -b4: Bool, -b5: Bool, e: {Bool.and(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5)))) == True{} : Bool}) -> {b1 == True{} : Bool}:
  br.and_l(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5))), e)

def br.p2(+b1: Bool, +b2: Bool, -b3: Bool, -b4: Bool, -b5: Bool, e: {Bool.and(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5)))) == True{} : Bool}) -> {b2 == True{} : Bool}:
  br.and_l(b2, Bool.and(b3, Bool.and(b4, b5)), br.and_r(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5))), e))

def br.p3(+b1: Bool, +b2: Bool, +b3: Bool, -b4: Bool, -b5: Bool, e: {Bool.and(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5)))) == True{} : Bool}) -> {b3 == True{} : Bool}:
  br.and_l(b3, Bool.and(b4, b5), br.and_r(b2, Bool.and(b3, Bool.and(b4, b5)), br.and_r(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5))), e)))

def br.p4(+b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, -b5: Bool, e: {Bool.and(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5)))) == True{} : Bool}) -> {b4 == True{} : Bool}:
  br.and_l(b4, b5, br.and_r(b3, Bool.and(b4, b5), br.and_r(b2, Bool.and(b3, Bool.and(b4, b5)), br.and_r(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5))), e))))

def br.p5(+b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, -b5: Bool, e: {Bool.and(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5)))) == True{} : Bool}) -> {b5 == True{} : Bool}:
  br.and_r(b4, b5, br.and_r(b3, Bool.and(b4, b5), br.and_r(b2, Bool.and(b3, Bool.and(b4, b5)), br.and_r(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5))), e))))

# the one of five that dimension d names
def br.sel(d: B.Dim, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool) -> Bool:
  match d:
    case B.Cost{}:
      b1
    case B.Tok{}:
      b2
    case B.Time{}:
      b3
    case B.Calls{}:
      b4
    case B.Reqs{}:
      b5

# an offer that does not fit, then offers of which none fits: none fits
def br.nf_cons(a: Bool, -r: Bool, ea: {a == False{} : Bool}, er: {r == True{} : Bool}) -> {Bool.and(Bool.not(a), r) == True{} : Bool}:
  match a:
    case True{}:
      Equal.sym(Bool, True{}, False{}, ea)
    case False{}:
      er

# one offer that fits: not none fits
def br.nf_single(-b: Bool, e: {b == True{} : Bool}) -> {Bool.and(Bool.not(b), True{}) == False{} : Bool}:
  %Equal.sym(Bool, b, True{}, e) : {Bool.and(Bool.not(_), True{}) == False{} : Bool}
  {==}

def br.not_false(-b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

# Nat
# ---

def br.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, br.add_zero(p))

def br.add_zero_r(n: Nat) -> {n == Nat.add(n, 0n) : Nat}:
  Equal.sym(Nat, Nat.add(n, 0n), n, br.add_zero(n))

def br.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), br.add_succ(p, b))

def br.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), br.add_assoc(p, b, c))

def br.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      br.add_zero_r(b)
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, b), Nat.add(b, p), br.add_comm(p, b)), Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), br.add_succ(b, p)))

def br.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def br.le_refl(x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      br.le_refl(p)

# a <= b: a <= b + 1
def br.le_step(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      br.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      br.le_step(p, q, e)

# a <= w: a <= f + w
def br.le_add(f: Nat, +a: Nat, +w: Nat, e: {Nat.is_le(a, w) == True{} : Bool}) -> {Nat.is_le(a, Nat.add(f, w)) == True{} : Bool}:
  match f:
    case 0n:
      e
    case 1n++g:
      br.le_step(a, Nat.add(g, w), br.le_add(g, a, w, e))

def br.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n q r:
      br.le_zero(r)
    case 1n+p 0n r:
      br.absurd({Nat.is_le(1n+p, r) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      br.absurd({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      br.le_trans(p, q, r, ab, bc)

# b <= b + k
def br.le_self(b: Nat, k: Nat) -> {Nat.is_le(b, Nat.add(b, k)) == True{} : Bool}:
  match b:
    case 0n:
      br.le_zero(k)
    case 1n+p:
      br.le_self(p, k)

# a <= b: a + c <= b + c
def br.mono_l(a: Nat, b: Nat, +c: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  match a b:
    case 0n q:
      br.le_add(q, c, c, br.le_refl(c))
    case 1n+p 0n:
      br.absurd({Nat.is_le(Nat.add(1n+p, c), c) == True{} : Bool}, e)
    case 1n+p 1n+q:
      br.mono_l(p, q, c, e)

# b <= c: a + b <= a + c
def br.mono_r(a: Nat, +b: Nat, +c: Nat, e: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      e
    case 1n+p:
      br.mono_r(p, b, c, e)

# what is left and what was taken add up: (f - c) + c = f when c + k <= f
def br.take(c: Nat, -k: Nat, f: Nat, e: {Nat.is_le(Nat.add(c, k), f) == True{} : Bool}) -> {Nat.add(Nat.sub(f, c), c) == f : Nat}:
  match c f:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(q, 0n), q, br.add_zero(q))
    case 1n+p 0n:
      br.absurd({Nat.add(Nat.sub(0n, 1n+p), 1n+p) == 0n : Nat}, e)
    case 1n++p 1n++q:
      Equal.trans(Nat, Nat.add(Nat.sub(q, p), 1n+p), 1n+Nat.add(Nat.sub(q, p), p), 1n+q, br.add_succ(Nat.sub(q, p), p), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.sub(q, p), p), q, br.take(p, k, q, e)))

# c + y <= f: y <= f - c
def br.le_sub(c: Nat, f: Nat, +y: Nat, e: {Nat.is_le(Nat.add(c, y), f) == True{} : Bool}) -> {Nat.is_le(y, Nat.sub(f, c)) == True{} : Bool}:
  match c f:
    case 0n 0n:
      e
    case 0n 1n+q:
      e
    case 1n+p 0n:
      br.absurd({Nat.is_le(y, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      br.le_sub(p, q, y, e)

# x <= k: x + b <= b + k
def br.mono_lc(+x: Nat, +k: Nat, +b: Nat, e: {Nat.is_le(x, k) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, b), Nat.add(b, k)) == True{} : Bool}:
  %br.add_comm(k, b) : {Nat.is_le(Nat.add(x, b), _) == True{} : Bool}
  br.mono_l(x, k, b, e)

# x <= k and c + (b + k) <= f: x + (b + 0) <= f - c
def br.kept_final(+c: Nat, +f: Nat, +x: Nat, +b: Nat, +k: Nat, e1: {Nat.is_le(x, k) == True{} : Bool}, e2: {Nat.is_le(Nat.add(c, Nat.add(b, k)), f) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, Nat.add(b, 0n)), Nat.sub(f, c)) == True{} : Bool}:
  %br.add_zero_r(b) : {Nat.is_le(Nat.add(x, _), Nat.sub(f, c)) == True{} : Bool}
  br.le_trans(Nat.add(x, b), Nat.add(b, k), Nat.sub(f, c), br.mono_lc(x, k, b, e1), br.le_sub(c, f, Nat.add(b, k), e2))

# x <= b and c + (b + k) <= f: x + 0 <= f - c
def br.kept_base(+c: Nat, +f: Nat, +x: Nat, +b: Nat, +k: Nat, e1: {Nat.is_le(x, b) == True{} : Bool}, e2: {Nat.is_le(Nat.add(c, Nat.add(b, k)), f) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, 0n), Nat.sub(f, c)) == True{} : Bool}:
  %br.add_zero_r(x) : {Nat.is_le(_, Nat.sub(f, c)) == True{} : Bool}
  br.le_trans(x, Nat.add(b, k), Nat.sub(f, c), br.le_trans(x, b, Nat.add(b, k), e1, br.le_self(b, k)), br.le_sub(c, f, Nat.add(b, k), e2))

# n + (c + (b + k)) <= u: (n + c) + (k + b) <= u
def br.final_mid(+n: Nat, +c: Nat, +b: Nat, +k: Nat, +u: Nat, w: {Nat.is_le(Nat.add(n, Nat.add(c, Nat.add(b, k))), u) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.add(n, c), Nat.add(k, b)), u) == True{} : Bool}:
  %br.add_comm(b, k) : {Nat.is_le(Nat.add(Nat.add(n, c), _), u) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(n, c), Nat.add(b, k)), Nat.add(n, Nat.add(c, Nat.add(b, k))), br.add_assoc(n, c, Nat.add(b, k))) : {Nat.is_le(_, u) == True{} : Bool}
  w

# asked by n + c, a final answer of f within k, after work of c that
# ended with b and k by u, ends with b by u
def br.final_t(+n: Nat, +n2: Nat, +c: Nat, +f: Nat, +b: Nat, +k: Nat, +u: Nat, soon: {Nat.is_le(n2, Nat.add(n, c)) == True{} : Bool}, fk: {Nat.is_le(f, k) == True{} : Bool}, w: {Nat.is_le(Nat.add(n, Nat.add(c, Nat.add(b, k))), u) == True{} : Bool}) -> {Nat.is_le(Nat.add(n2, Nat.add(f, Nat.add(b, 0n))), u) == True{} : Bool}:
  %br.add_zero_r(b) : {Nat.is_le(Nat.add(n2, Nat.add(f, _)), u) == True{} : Bool}
  br.le_trans(Nat.add(n2, Nat.add(f, b)), Nat.add(Nat.add(n, c), Nat.add(f, b)), u, br.mono_l(n2, Nat.add(n, c), Nat.add(f, b), soon), br.le_trans(Nat.add(Nat.add(n, c), Nat.add(f, b)), Nat.add(Nat.add(n, c), Nat.add(k, b)), u, br.mono_r(Nat.add(n, c), Nat.add(f, b), Nat.add(k, b), br.mono_l(f, k, b, fk)), br.final_mid(n, c, b, k, u, w)))

def br.base_t(+n2: Nat, +f: Nat, +u: Nat, e: {Nat.is_le(Nat.add(n2, f), u) == True{} : Bool}) -> {Nat.is_le(Nat.add(n2, Nat.add(f, 0n)), u) == True{} : Bool}:
  %br.add_zero_r(f) : {Nat.is_le(Nat.add(n2, _), u) == True{} : Bool}
  e

def br.sub_zero(x: Nat) -> {x == Nat.sub(x, 0n) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (x + o) - o = x
def br.add_sub(+x: Nat, o: Nat) -> {x == Nat.sub(Nat.add(x, o), o) : Nat}:
  match o:
    case 0n:
      %br.sub_zero(Nat.add(x, 0n)) : {x == _ : Nat}
      br.add_zero_r(x)
    case 1n+q:
      %Equal.sym(Nat, Nat.add(x, 1n+q), 1n+Nat.add(x, q), br.add_succ(x, q)) : {x == Nat.sub(_, 1n+q) : Nat}
      br.add_sub(x, q)

# x <= f + ((x + o) - o): funding x and the overrun o frees at least x
def br.le_fund(+x: Nat, +f: Nat, o: Nat) -> {Nat.is_le(x, Nat.add(f, Nat.sub(Nat.add(x, o), o))) == True{} : Bool}:
  %br.add_sub(x, o) : {Nat.is_le(x, Nat.add(f, _)) == True{} : Bool}
  br.le_add(f, x, x, br.le_refl(x))

# n <= u + (n - u): a deadline moved by what n is past it reaches n
def br.le_top(n: Nat, u: Nat) -> {Nat.is_le(n, Nat.add(u, Nat.sub(n, u))) == True{} : Bool}:
  match n u:
    case 0n q:
      br.le_zero(Nat.add(q, 0n))
    case 1n+p 0n:
      br.le_refl(1n+p)
    case 1n+p 1n+q:
      br.le_top(p, q)

# Amounts
# -------

# x, y and z together in dimension d
def br.at3(+d: B.Dim, +x: B.Amt, +y: B.Amt, +z: B.Amt) -> {S.at(d, B.add4(B.add4(x, y), z)) == Nat.add(S.at(d, x), Nat.add(S.at(d, y), S.at(d, z))) : Nat}:
  Equal.trans(Nat, S.at(d, B.add4(B.add4(x, y), z)), Nat.add(S.at(d, B.add4(x, y)), S.at(d, z)), Nat.add(S.at(d, x), Nat.add(S.at(d, y), S.at(d, z))), BA.ba.at_add4(d, B.add4(x, y), z), Equal.trans(Nat, Nat.add(S.at(d, B.add4(x, y)), S.at(d, z)), Nat.add(Nat.add(S.at(d, x), S.at(d, y)), S.at(d, z)), Nat.add(S.at(d, x), Nat.add(S.at(d, y), S.at(d, z))), Equal.cong(Nat, Nat, w => Nat.add(w, S.at(d, z)), S.at(d, B.add4(x, y)), Nat.add(S.at(d, x), S.at(d, y)), BA.ba.at_add4(d, x, y)), br.add_assoc(S.at(d, x), S.at(d, y), S.at(d, z))))

# y is y and nothing, in dimension d
def br.at_nothing(+d: B.Dim, +y: Nat) -> {y == Nat.add(y, S.at(d, B.zero())) : Nat}:
  Equal.trans(Nat, y, Nat.add(y, 0n), Nat.add(y, S.at(d, B.zero())), br.add_zero_r(y), Equal.cong(Nat, Nat, w => Nat.add(y, w), 0n, S.at(d, B.zero()), Equal.sym(Nat, S.at(d, B.zero()), 0n, BA.ba.at_zero(d))))

# x and y together in dimension d, with nothing kept
def br.at2z(+d: B.Dim, +x: B.Amt, +y: B.Amt) -> {S.at(d, B.add4(x, y)) == Nat.add(S.at(d, x), Nat.add(S.at(d, y), S.at(d, B.zero()))) : Nat}:
  Equal.trans(Nat, S.at(d, B.add4(x, y)), Nat.add(S.at(d, x), S.at(d, y)), Nat.add(S.at(d, x), Nat.add(S.at(d, y), S.at(d, B.zero()))), BA.ba.at_add4(d, x, y), Equal.cong(Nat, Nat, w => Nat.add(S.at(d, x), w), S.at(d, y), Nat.add(S.at(d, y), S.at(d, B.zero())), br.at_nothing(d, S.at(d, y))))

# what a reservation of c must find free in spent dimension d
def br.nd(u: B.Use, +d: B.Dim, base: B.Ask, keep: B.Ask, c: B.Ask) -> Nat:
  Nat.add(S.at(d, S.amt(c)), Nat.add(S.at(d, S.amt(base)), S.at(d, S.amt(S.keep_of(u, keep)))))

# the code's need is the spec's, in each dimension
def br.need_at(u: B.Use, c: B.Ask, base: B.Ask, keep: B.Ask, +d: B.Dim) -> {S.at(d, S.amt(B.need(u, base, keep, c))) == br.nd(u, d, base, keep, c) : Nat}:
  match u:
    case B.Work{}:
      match c:
        case B.Ask{cx, cm}:
          match base:
            case B.Ask{bx, bm}:
              match keep:
                case B.Ask{kx, km}:
                  br.at3(d, cx, bx, kx)
    case B.Final{}:
      match c:
        case B.Ask{cx, cm}:
          match base:
            case B.Ask{bx, bm}:
              br.at2z(d, cx, bx)

# the code's need is the spec's, in duration
def br.need_ms(u: B.Use, c: B.Ask, base: B.Ask, keep: B.Ask) -> {S.ms(B.need(u, base, keep, c)) == Nat.add(S.ms(c), Nat.add(S.ms(base), S.ms(S.keep_of(u, keep)))) : Nat}:
  match u:
    case B.Work{}:
      match c:
        case B.Ask{cx, cm}:
          match base:
            case B.Ask{bx, bm}:
              match keep:
                case B.Ask{kx, km}:
                  br.add_assoc(cm, bm, km)
    case B.Final{}:
      match c:
        case B.Ask{cx, cm}:
          match base:
            case B.Ask{bx, +bm}:
              Equal.cong(Nat, Nat, w => Nat.add(cm, w), bm, Nat.add(bm, 0n), br.add_zero_r(bm))

# the first dimension of five that is short
def br.lk(b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool) -> Maybe<&2, B.Dim>:
  B.lack.at(b1, B.Cost{}, B.lack.at(b2, B.Tok{}, B.lack.at(b3, B.Time{}, B.lack.at(b4, B.Calls{}, B.lack.at(b5, B.Reqs{}, None{})))))

def br.lack_at(n: B.Ask, f: B.Amt, -now: Nat, -un: Nat) -> {br.lk(Nat.is_le(S.at(B.Cost{}, S.amt(n)), S.at(B.Cost{}, f)), Nat.is_le(S.at(B.Tok{}, S.amt(n)), S.at(B.Tok{}, f)), Nat.is_le(Nat.add(now, S.ms(n)), un), Nat.is_le(S.at(B.Calls{}, S.amt(n)), S.at(B.Calls{}, f)), Nat.is_le(S.at(B.Reqs{}, S.amt(n)), S.at(B.Reqs{}, f))) == B.lack(n, f, now, un) : Maybe<&2, B.Dim>}:
  match n:
    case B.Ask{x, m}:
      match x:
        case B.Amt{nc, nk, nn, nr}:
          match f:
            case B.Amt{fc, fk, fn, fr}:
              {==}

# the code's lack, by the spec's tests
def br.lack_lk(+u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +un: Nat) -> {br.lk(S.fits_in(u, base, keep, c, f, B.Cost{}), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{})) == B.lack(B.need(u, base, keep, c), f, now, un) : Maybe<&2, B.Dim>}:
  %br.need_at(u, c, base, keep, B.Cost{}) : {br.lk(Nat.is_le(_, S.at(B.Cost{}, f)), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{})) == B.lack(B.need(u, base, keep, c), f, now, un) : Maybe<&2, B.Dim>}
  %br.need_at(u, c, base, keep, B.Tok{}) : {br.lk(Nat.is_le(S.at(B.Cost{}, S.amt(B.need(u, base, keep, c))), S.at(B.Cost{}, f)), Nat.is_le(_, S.at(B.Tok{}, f)), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{})) == B.lack(B.need(u, base, keep, c), f, now, un) : Maybe<&2, B.Dim>}
  %br.need_ms(u, c, base, keep) : {br.lk(Nat.is_le(S.at(B.Cost{}, S.amt(B.need(u, base, keep, c))), S.at(B.Cost{}, f)), Nat.is_le(S.at(B.Tok{}, S.amt(B.need(u, base, keep, c))), S.at(B.Tok{}, f)), Nat.is_le(Nat.add(now, _), un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{})) == B.lack(B.need(u, base, keep, c), f, now, un) : Maybe<&2, B.Dim>}
  %br.need_at(u, c, base, keep, B.Calls{}) : {br.lk(Nat.is_le(S.at(B.Cost{}, S.amt(B.need(u, base, keep, c))), S.at(B.Cost{}, f)), Nat.is_le(S.at(B.Tok{}, S.amt(B.need(u, base, keep, c))), S.at(B.Tok{}, f)), Nat.is_le(Nat.add(now, S.ms(B.need(u, base, keep, c))), un), Nat.is_le(_, S.at(B.Calls{}, f)), S.fits_in(u, base, keep, c, f, B.Reqs{})) == B.lack(B.need(u, base, keep, c), f, now, un) : Maybe<&2, B.Dim>}
  %br.need_at(u, c, base, keep, B.Reqs{}) : {br.lk(Nat.is_le(S.at(B.Cost{}, S.amt(B.need(u, base, keep, c))), S.at(B.Cost{}, f)), Nat.is_le(S.at(B.Tok{}, S.amt(B.need(u, base, keep, c))), S.at(B.Tok{}, f)), Nat.is_le(Nat.add(now, S.ms(B.need(u, base, keep, c))), un), Nat.is_le(S.at(B.Calls{}, S.amt(B.need(u, base, keep, c))), S.at(B.Calls{}, f)), Nat.is_le(_, S.at(B.Reqs{}, f))) == B.lack(B.need(u, base, keep, c), f, now, un) : Maybe<&2, B.Dim>}
  br.lack_at(B.need(u, base, keep, c), f, now, un)

# Fitting
# -------

# what a lack l says of five tests: none short, or not all hold and the
# one of the named dimension fails
def br.LkOk(l: Maybe<&2, B.Dim>, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool) -> Type:
  match l:
    case None{}:
      {Bool.and(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5)))) == True{} : Bool}
    case Some{d}:
      {Bool.and(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5)))) == False{} : Bool} & {br.sel(d, b1, b2, b3, b4, b5) == False{} : Bool}

def br.lk_ok(b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool) -> br.LkOk(br.lk(b1, b2, b3, b4, b5), b1, b2, b3, b4, b5):
  match b1:
    case False{}:
      ({==}, {==})
    case True{}:
      match b2:
        case False{}:
          ({==}, {==})
        case True{}:
          match b3:
            case False{}:
              ({==}, {==})
            case True{}:
              match b4:
                case False{}:
                  ({==}, {==})
                case True{}:
                  match b5:
                    case False{}:
                      ({==}, {==})
                    case True{}:
                      {==}

def br.tight_lk(b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool) -> {B.tight.of(br.lk(b1, b2, b3, b4, b5)) == Bool.not(Bool.and(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5))))) : Bool}:
  match b1:
    case False{}:
      {==}
    case True{}:
      match b2:
        case False{}:
          {==}
        case True{}:
          match b3:
            case False{}:
              {==}
            case True{}:
              match b4:
                case False{}:
                  {==}
                case True{}:
                  match b5:
                    case False{}:
                      {==}
                    case True{}:
                      {==}

# what a lack l says of the offer c against f free at now by un: c fits,
# or it does not and the named dimension is short
def br.LackOk(l: Maybe<&2, B.Dim>, +u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +un: Nat) -> Type:
  br.LkOk(l, S.fits_in(u, base, keep, c, f, B.Cost{}), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{}))

# the code's lack is the spec's fits
def br.lack_ok(+u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +un: Nat) -> br.LackOk(B.lack(B.need(u, base, keep, c), f, now, un), u, base, keep, c, f, now, un):
  %br.lack_lk(u, base, keep, c, f, now, un) : br.LackOk(_, u, base, keep, c, f, now, un)
  br.lk_ok(S.fits_in(u, base, keep, c, f, B.Cost{}), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{}))

# an ask is tight exactly when it does not fit
def br.tight_fits(+u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +un: Nat) -> {B.tight.of(B.lack(B.need(u, base, keep, c), f, now, un)) == Bool.not(S.fits(u, base, keep, c, f, now, un)) : Bool}:
  %br.lack_lk(u, base, keep, c, f, now, un) : {B.tight.of(_) == Bool.not(S.fits(u, base, keep, c, f, now, un)) : Bool}
  br.tight_lk(S.fits_in(u, base, keep, c, f, B.Cost{}), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{}))

# the spec's short dimension is the one the tests name failing
def br.sel_short(d: B.Dim, +u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +un: Nat) -> {S.short_in(u, base, keep, c, f, now, un, d) == Bool.not(br.sel(d, S.fits_in(u, base, keep, c, f, B.Cost{}), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{}))) : Bool}:
  match d:
    case B.Cost{}:
      {==}
    case B.Tok{}:
      {==}
    case B.Time{}:
      {==}
    case B.Calls{}:
      {==}
    case B.Reqs{}:
      {==}

def br.short_of(+d: B.Dim, +u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, ns: {br.sel(d, S.fits_in(u, base, keep, c, f, B.Cost{}), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{})) == False{} : Bool}) -> {S.short_in(u, base, keep, c, f, now, un, d) == True{} : Bool}:
  Equal.trans(Bool, S.short_in(u, base, keep, c, f, now, un, d), Bool.not(br.sel(d, S.fits_in(u, base, keep, c, f, B.Cost{}), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{}))), True{}, br.sel_short(d, u, base, keep, c, f, now, un), br.not_false(br.sel(d, S.fits_in(u, base, keep, c, f, B.Cost{}), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{})), ns))

# an ask that fits, fits in each dimension
def br.fits_at(d: B.Dim, +u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, e: {S.fits(u, base, keep, c, f, now, un) == True{} : Bool}) -> {S.fits_in(u, base, keep, c, f, d) == True{} : Bool}:
  match d:
    case B.Cost{}:
      br.p1(S.fits_in(u, base, keep, c, f, B.Cost{}), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{}), e)
    case B.Tok{}:
      br.p2(S.fits_in(u, base, keep, c, f, B.Cost{}), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{}), e)
    case B.Time{}:
      {==}
    case B.Calls{}:
      br.p4(S.fits_in(u, base, keep, c, f, B.Cost{}), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{}), e)
    case B.Reqs{}:
      br.p5(S.fits_in(u, base, keep, c, f, B.Cost{}), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{}), e)

# an ask that fits ends on time
def br.on_time_of(+u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, e: {S.fits(u, base, keep, c, f, now, un) == True{} : Bool}) -> {S.on_time(u, base, keep, c, now, un) == True{} : Bool}:
  br.p3(S.fits_in(u, base, keep, c, f, B.Cost{}), S.fits_in(u, base, keep, c, f, B.Tok{}), S.on_time(u, base, keep, c, now, un), S.fits_in(u, base, keep, c, f, B.Calls{}), S.fits_in(u, base, keep, c, f, B.Reqs{}), e)

# an ask within another is within it in each dimension
def br.le_at(d: B.Dim, +x: B.Ask, +k: B.Ask, e: {S.le(x, k) == True{} : Bool}) -> {Nat.is_le(S.at(d, S.amt(x)), S.at(d, S.amt(k))) == True{} : Bool}:
  match d:
    case B.Cost{}:
      br.p1(Nat.is_le(S.at(B.Cost{}, S.amt(x)), S.at(B.Cost{}, S.amt(k))), Nat.is_le(S.at(B.Tok{}, S.amt(x)), S.at(B.Tok{}, S.amt(k))), Nat.is_le(S.at(B.Calls{}, S.amt(x)), S.at(B.Calls{}, S.amt(k))), Nat.is_le(S.at(B.Reqs{}, S.amt(x)), S.at(B.Reqs{}, S.amt(k))), Nat.is_le(S.ms(x), S.ms(k)), e)
    case B.Tok{}:
      br.p2(Nat.is_le(S.at(B.Cost{}, S.amt(x)), S.at(B.Cost{}, S.amt(k))), Nat.is_le(S.at(B.Tok{}, S.amt(x)), S.at(B.Tok{}, S.amt(k))), Nat.is_le(S.at(B.Calls{}, S.amt(x)), S.at(B.Calls{}, S.amt(k))), Nat.is_le(S.at(B.Reqs{}, S.amt(x)), S.at(B.Reqs{}, S.amt(k))), Nat.is_le(S.ms(x), S.ms(k)), e)
    case B.Time{}:
      {==}
    case B.Calls{}:
      br.p3(Nat.is_le(S.at(B.Cost{}, S.amt(x)), S.at(B.Cost{}, S.amt(k))), Nat.is_le(S.at(B.Tok{}, S.amt(x)), S.at(B.Tok{}, S.amt(k))), Nat.is_le(S.at(B.Calls{}, S.amt(x)), S.at(B.Calls{}, S.amt(k))), Nat.is_le(S.at(B.Reqs{}, S.amt(x)), S.at(B.Reqs{}, S.amt(k))), Nat.is_le(S.ms(x), S.ms(k)), e)
    case B.Reqs{}:
      br.p4(Nat.is_le(S.at(B.Cost{}, S.amt(x)), S.at(B.Cost{}, S.amt(k))), Nat.is_le(S.at(B.Tok{}, S.amt(x)), S.at(B.Tok{}, S.amt(k))), Nat.is_le(S.at(B.Calls{}, S.amt(x)), S.at(B.Calls{}, S.amt(k))), Nat.is_le(S.at(B.Reqs{}, S.amt(x)), S.at(B.Reqs{}, S.amt(k))), Nat.is_le(S.ms(x), S.ms(k)), e)

# an ask within another is within it in duration
def br.le_ms(+x: B.Ask, +k: B.Ask, e: {S.le(x, k) == True{} : Bool}) -> {Nat.is_le(S.ms(x), S.ms(k)) == True{} : Bool}:
  br.p5(Nat.is_le(S.at(B.Cost{}, S.amt(x)), S.at(B.Cost{}, S.amt(k))), Nat.is_le(S.at(B.Tok{}, S.amt(x)), S.at(B.Tok{}, S.amt(k))), Nat.is_le(S.at(B.Calls{}, S.amt(x)), S.at(B.Calls{}, S.amt(k))), Nat.is_le(S.at(B.Reqs{}, S.amt(x)), S.at(B.Reqs{}, S.amt(k))), Nat.is_le(S.ms(x), S.ms(k)), e)

# what a grant of c leaves of f, and c, add up to f in dimension d
def br.left(+d: B.Dim, +f: B.Amt, +c: B.Amt, -k: Nat, e: {Nat.is_le(Nat.add(S.at(d, c), k), S.at(d, f)) == True{} : Bool}) -> {Nat.add(S.at(d, B.sub4(f, c)), S.at(d, c)) == S.at(d, f) : Nat}:
  %Equal.sym(Nat, S.at(d, B.sub4(f, c)), Nat.sub(S.at(d, f), S.at(d, c)), BA.ba.at_sub4(d, f, c)) : {Nat.add(_, S.at(d, c)) == S.at(d, f) : Nat}
  br.take(S.at(d, c), k, S.at(d, f), e)

# a final answer x within the reserve fits what granted work c left of f,
# in spent dimension d
def br.final_in(+d: B.Dim, +base: B.Ask, -k2: B.Ask, +x: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, e1: {S.le(x, keep) == True{} : Bool}, e2: {S.fits(B.Work{}, base, keep, c, f, now, un) == True{} : Bool}) -> {S.fits_in(B.Final{}, base, k2, x, B.sub4(f, S.amt(c)), d) == True{} : Bool}:
  %Equal.sym(Nat, S.at(d, B.sub4(f, S.amt(c))), Nat.sub(S.at(d, f), S.at(d, S.amt(c))), BA.ba.at_sub4(d, f, S.amt(c))) : {Nat.is_le(Nat.add(S.at(d, S.amt(x)), Nat.add(S.at(d, S.amt(base)), S.at(d, B.zero()))), _) == True{} : Bool}
  %Equal.sym(Nat, S.at(d, B.zero()), 0n, BA.ba.at_zero(d)) : {Nat.is_le(Nat.add(S.at(d, S.amt(x)), Nat.add(S.at(d, S.amt(base)), _)), Nat.sub(S.at(d, f), S.at(d, S.amt(c)))) == True{} : Bool}
  br.kept_final(S.at(d, S.amt(c)), S.at(d, f), S.at(d, S.amt(x)), S.at(d, S.amt(base)), S.at(d, S.amt(keep)), br.le_at(d, x, keep, e1), br.fits_at(d, B.Work{}, base, keep, c, f, now, un, e2))

# a final answer x within the reserve, asked by the time granted work c
# ends, ends on time
def br.final_time(+base: B.Ask, -k2: B.Ask, +x: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +now2: Nat, +un: Nat, e1: {S.le(x, keep) == True{} : Bool}, e2: {S.fits(B.Work{}, base, keep, c, f, now, un) == True{} : Bool}, soon: {Nat.is_le(now2, Nat.add(now, S.ms(c))) == True{} : Bool}) -> {S.on_time(B.Final{}, base, k2, x, now2, un) == True{} : Bool}:
  br.final_t(now, now2, S.ms(c), S.ms(x), S.ms(base), S.ms(keep), un, soon, br.le_ms(x, keep, e1), br.on_time_of(B.Work{}, base, keep, c, f, now, un, e2))

# a final answer x within the reserve, asked by the time granted work c
# ends, fits what that work left
def br.final_fits(+base: B.Ask, -k2: B.Ask, +x: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +now2: Nat, +un: Nat, +e1: {S.le(x, keep) == True{} : Bool}, +e2: {S.fits(B.Work{}, base, keep, c, f, now, un) == True{} : Bool}, soon: {Nat.is_le(now2, Nat.add(now, S.ms(c))) == True{} : Bool}) -> {S.fits(B.Final{}, base, k2, x, B.sub4(f, S.amt(c)), now2, un) == True{} : Bool}:
  br.and5(S.fits_in(B.Final{}, base, k2, x, B.sub4(f, S.amt(c)), B.Cost{}), S.fits_in(B.Final{}, base, k2, x, B.sub4(f, S.amt(c)), B.Tok{}), S.on_time(B.Final{}, base, k2, x, now2, un), S.fits_in(B.Final{}, base, k2, x, B.sub4(f, S.amt(c)), B.Calls{}), S.fits_in(B.Final{}, base, k2, x, B.sub4(f, S.amt(c)), B.Reqs{}), br.final_in(B.Cost{}, base, k2, x, keep, c, f, now, un, e1, e2), br.final_in(B.Tok{}, base, k2, x, keep, c, f, now, un, e1, e2), br.final_time(base, k2, x, keep, c, f, now, now2, un, e1, e2, soon), br.final_in(B.Calls{}, base, k2, x, keep, c, f, now, un, e1, e2), br.final_in(B.Reqs{}, base, k2, x, keep, c, f, now, un, e1, e2))

# a final answer x within the reserves above fits, with no reserve, what
# any grant of c left of f, in spent dimension d
def br.base_in(+d: B.Dim, +u: B.Use, +base: B.Ask, +keep: B.Ask, -k2: B.Ask, +x: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, e1: {S.le(x, base) == True{} : Bool}, e2: {S.fits(u, base, keep, c, f, now, un) == True{} : Bool}) -> {S.fits_in(B.Final{}, S.nothing(), k2, x, B.sub4(f, S.amt(c)), d) == True{} : Bool}:
  %Equal.sym(Nat, S.at(d, B.sub4(f, S.amt(c))), Nat.sub(S.at(d, f), S.at(d, S.amt(c))), BA.ba.at_sub4(d, f, S.amt(c))) : {Nat.is_le(Nat.add(S.at(d, S.amt(x)), Nat.add(S.at(d, B.zero()), S.at(d, B.zero()))), _) == True{} : Bool}
  %Equal.sym(Nat, S.at(d, B.zero()), 0n, BA.ba.at_zero(d)) : {Nat.is_le(Nat.add(S.at(d, S.amt(x)), Nat.add(_, _)), Nat.sub(S.at(d, f), S.at(d, S.amt(c)))) == True{} : Bool}
  br.kept_base(S.at(d, S.amt(c)), S.at(d, f), S.at(d, S.amt(x)), S.at(d, S.amt(base)), S.at(d, S.amt(S.keep_of(u, keep))), br.le_at(d, x, base, e1), br.fits_at(d, u, base, keep, c, f, now, un, e2))

# a final answer x within the reserves above, on time by un, fits with no
# reserve what any grant of c left of f
def br.base_fits(+u: B.Use, +base: B.Ask, +keep: B.Ask, -k2: B.Ask, +x: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +now2: Nat, +un: Nat, +e1: {S.le(x, base) == True{} : Bool}, +e2: {S.fits(u, base, keep, c, f, now, un) == True{} : Bool}, et: {Nat.is_le(Nat.add(now2, S.ms(x)), un) == True{} : Bool}) -> {S.fits(B.Final{}, S.nothing(), k2, x, B.sub4(f, S.amt(c)), now2, un) == True{} : Bool}:
  br.and5(S.fits_in(B.Final{}, S.nothing(), k2, x, B.sub4(f, S.amt(c)), B.Cost{}), S.fits_in(B.Final{}, S.nothing(), k2, x, B.sub4(f, S.amt(c)), B.Tok{}), S.on_time(B.Final{}, S.nothing(), k2, x, now2, un), S.fits_in(B.Final{}, S.nothing(), k2, x, B.sub4(f, S.amt(c)), B.Calls{}), S.fits_in(B.Final{}, S.nothing(), k2, x, B.sub4(f, S.amt(c)), B.Reqs{}), br.base_in(B.Cost{}, u, base, keep, k2, x, c, f, now, un, e1, e2), br.base_in(B.Tok{}, u, base, keep, k2, x, c, f, now, un, e1, e2), br.base_t(now2, S.ms(x), un, et), br.base_in(B.Calls{}, u, base, keep, k2, x, c, f, now, un, e1, e2), br.base_in(B.Reqs{}, u, base, keep, k2, x, c, f, now, un, e1, e2))

# The pick
# --------

# the pick one place later
def br.bump(p: B.Pick) -> B.Pick:
  match p:
    case B.Fit{j, x}:
      B.Fit{1n+j, x}
    case B.NoFit{d}:
      B.NoFit{d}

def br.one_bump(l: Maybe<&2, B.Dim>, -i: Nat, -c: B.Ask) -> {br.bump(B.pick.one(l, i, c)) == B.pick.one(l, 1n+i, c) : B.Pick}:
  match l:
    case None{}:
      {==}
    case Some{d}:
      {==}

def br.or_bump(l: Maybe<&2, B.Dim>, -i: Nat, -c: B.Ask, -r: B.Pick, -r2: B.Pick, e: {br.bump(r) == r2 : B.Pick}) -> {br.bump(B.pick.or(l, i, c, r)) == B.pick.or(l, 1n+i, c, r2) : B.Pick}:
  match l:
    case None{}:
      {==}
    case Some{d}:
      e

# the pick from place 1+i is the pick from place i, one place later
def br.pick_bump(less: List<&2, B.Ask>, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +c: B.Ask, +i: Nat) -> {br.bump(B.pick(less, u, base, keep, f, now, un, c, i)) == B.pick(less, u, base, keep, f, now, un, c, 1n+i) : B.Pick}:
  match less:
    case Nil{}:
      br.one_bump(B.lack(B.need(u, base, keep, c), f, now, un), i, c)
    case Con{+h, +t}:
      br.or_bump(B.lack(B.need(u, base, keep, c), f, now, un), i, c, B.pick(t, u, base, keep, f, now, un, h, 1n+i), B.pick(t, u, base, keep, f, now, un, h, 2n+i), br.pick_bump(t, u, base, keep, f, now, un, h, 1n+i))

# what a pick p among the offers c and then less says: the offer at its
# place, none before it fits and it fits; or none fits and the last is
# short in the named dimension
def br.PickOk(p: B.Pick, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +c: B.Ask, +less: List<&2, B.Ask>) -> Type:
  match p:
    case B.Fit{+j, +x}:
      {S.nth(j, c <> less) == Some{x} : Maybe<&2, B.Ask>} & {S.none_fit(u, base, keep, S.before(j, c <> less), f, now, un) == True{} : Bool} & {S.fits(u, base, keep, x, f, now, un) == True{} : Bool}
    case B.NoFit{+d}:
      {S.none_fit(u, base, keep, c <> less, f, now, un) == True{} : Bool} & {S.short_in(u, base, keep, S.last(less, c), f, now, un, d) == True{} : Bool}

def br.one_ok(l: Maybe<&2, B.Dim>, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +c: B.Ask, lo: br.LackOk(l, u, base, keep, c, f, now, un)) -> br.PickOk(B.pick.one(l, 0n, c), u, base, keep, f, now, un, c, Nil{}):
  match l:
    case None{}:
      ({==}, ({==}, lo))
    case Some{+d}:
      (nf, ns) = lo
      (br.nf_cons(S.fits(u, base, keep, c, f, now, un), True{}, nf, {==}), br.short_of(d, u, base, keep, c, f, now, un, ns))

# c does not fit: the pick among h and then t, one place later, is the
# pick among c, h and then t
def br.bump_ok(r: B.Pick, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +c: B.Ask, +h: B.Ask, +t: List<&2, B.Ask>, nf: {S.fits(u, base, keep, c, f, now, un) == False{} : Bool}, ro: br.PickOk(r, u, base, keep, f, now, un, h, t)) -> br.PickOk(br.bump(r), u, base, keep, f, now, un, c, h <> t):
  match r:
    case B.Fit{+j, +x}:
      (rn, (rb, rf)) = ro
      (rn, (br.nf_cons(S.fits(u, base, keep, c, f, now, un), S.none_fit(u, base, keep, S.before(j, h <> t), f, now, un), nf, rb), rf))
    case B.NoFit{+d}:
      (ra, rl) = ro
      (br.nf_cons(S.fits(u, base, keep, c, f, now, un), S.none_fit(u, base, keep, h <> t, f, now, un), nf, ra), rl)

def br.or_ok(l: Maybe<&2, B.Dim>, r: B.Pick, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +c: B.Ask, +h: B.Ask, +t: List<&2, B.Ask>, lo: br.LackOk(l, u, base, keep, c, f, now, un), ro: br.PickOk(r, u, base, keep, f, now, un, h, t)) -> br.PickOk(B.pick.or(l, 0n, c, br.bump(r)), u, base, keep, f, now, un, c, h <> t):
  match l:
    case None{}:
      ({==}, ({==}, lo))
    case Some{d}:
      (nf, ns) = lo
      br.bump_ok(r, u, base, keep, f, now, un, c, h, t, nf, ro)

# the pick is the first offer that fits, or none fits
def br.pick_ok(less: List<&2, B.Ask>, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +c: B.Ask) -> br.PickOk(B.pick(less, u, base, keep, f, now, un, c, 0n), u, base, keep, f, now, un, c, less):
  match less:
    case Nil{}:
      br.one_ok(B.lack(B.need(u, base, keep, c), f, now, un), u, base, keep, f, now, un, c, br.lack_ok(u, base, keep, c, f, now, un))
    case Con{+h, +t}:
      %br.pick_bump(t, u, base, keep, f, now, un, h, 0n) : br.PickOk(B.pick.or(B.lack(B.need(u, base, keep, c), f, now, un), 0n, c, _), u, base, keep, f, now, un, c, h <> t)
      br.or_ok(B.lack(B.need(u, base, keep, c), f, now, un), B.pick(t, u, base, keep, f, now, un, h, 0n), u, base, keep, f, now, un, c, h, t, br.lack_ok(u, base, keep, c, f, now, un), br.pick_ok(t, u, base, keep, f, now, un, h))

# Phases and holds
# ----------------

# the code's admission is the spec's
def br.allows_eq(p: B.Phase, u: B.Use) -> {B.allows(p, u) == S.allows(p, u) : Bool}:
  match p u:
    case B.Working{} B.Work{}:
      {==}
    case B.Working{} B.Final{}:
      {==}
    case B.WrapUp{} B.Work{}:
      {==}
    case B.WrapUp{} B.Final{}:
      {==}
    case B.Exhausted{} B.Work{}:
      {==}
    case B.Exhausted{} B.Final{}:
      {==}

def br.allows_is(+p: B.Phase, +u: B.Use, -b: Bool, e: {S.allows(p, u) == b : Bool}) -> {b == B.allows(p, u) : Bool}:
  Equal.sym(Bool, B.allows(p, u), b, Equal.trans(Bool, B.allows(p, u), S.allows(p, u), b, br.allows_eq(p, u), e))

def br.after_eq(u: B.Use) -> {B.after(u) == S.after(u) : B.Phase}:
  match u:
    case B.Work{}:
      {==}
    case B.Final{}:
      {==}

def br.is_or(a: Bool, -x: Bool, -y: Bool, e: {x == y : Bool}) -> {B.held.is(a, x) == Bool.or(a, y) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# the code's held is the spec's has
def br.held_eq(hs: List<&2, B.Hold>, +id: Nat) -> {B.held(id, hs) == S.has(id, hs) : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      match h:
        case B.Hold{hid, amt}:
          br.is_or(Nat.is_eq(hid, id), B.held(id, t), S.has(id, t), br.held_eq(t, id))

def br.held_is(+id: Nat, +hs: List<&2, B.Hold>, -b: Bool, e: {S.has(id, hs) == b : Bool}) -> {b == B.held(id, hs) : Bool}:
  Equal.sym(Bool, B.held(id, hs), b, Equal.trans(Bool, B.held(id, hs), S.has(id, hs), b, br.held_eq(hs, id), e))

# The answer to a reservation
# ---------------------------

# what a refusal for w in phase p2 says of the request
def br.ResNo(w: B.Why, +p2: B.Phase, +u: B.Use, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +f: B.Amt, +now: Nat, +un: Nat) -> Type:
  match w:
    case B.Short{+d}:
      {S.none_fit(u, base, keep, want <> less, f, now, un) == True{} : Bool} & {S.short_in(u, base, keep, S.last(less, want), f, now, un, d) == True{} : Bool} & {p2 == S.after(u) : B.Phase}
    case B.Held{}:
      Unit
    case B.Stopped{}:
      Unit

# what the answer g says of the request for want and then less, under id
# at now, on the account of free f, spent s, lent l, overrun o, holds h,
# deadline un
def br.Res(g: B.Grant, +u: B.Use, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +f: B.Amt, +s: B.Amt, +l: B.Amt, +o: B.Amt, +h: List<&2, B.Hold>, +un: Nat) -> Type:
  match g:
    case B.Granted{+i, +c, +a2, +t}:
      {S.nth(i, want <> less) == Some{c} : Maybe<&2, B.Ask>} & {S.none_fit(u, base, keep, S.before(i, want <> less), f, now, un) == True{} : Bool} & {S.fits(u, base, keep, c, f, now, un) == True{} : Bool} & {B.Acct{B.sub4(f, S.amt(c)), s, l, o, B.Hold{id, S.amt(c)} <> h, un} == a2 : B.Acct} & {t == Bool.not(S.fits(u, base, keep, c, B.sub4(f, S.amt(c)), Nat.add(now, S.ms(c)), un)) : Bool}
    case B.Refused{w, +p2}:
      br.ResNo(w, p2, u, base, keep, want, less, f, now, un)

def br.res_fit(x: B.Ask, +j: Nat, +u: B.Use, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +f: B.Amt, +s: B.Amt, +l: B.Amt, +o: B.Amt, +h: List<&2, B.Hold>, +un: Nat, po: br.PickOk(B.Fit{j, x}, u, base, keep, f, now, un, want, less)) -> br.Res(B.reserve.pick(B.Fit{j, x}, u, id, now, base, keep, f, s, l, o, h, un), u, id, now, base, keep, want, less, f, s, l, o, h, un):
  match x:
    case B.Ask{+xa, +xm}:
      (pn, (pb, pf)) = po
      (pn, (pb, (pf, ({==}, br.tight_fits(u, base, keep, B.Ask{xa, xm}, B.sub4(f, xa), Nat.add(now, xm), un)))))

def br.res_pick(p: B.Pick, +u: B.Use, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +f: B.Amt, +s: B.Amt, +l: B.Amt, +o: B.Amt, +h: List<&2, B.Hold>, +un: Nat, po: br.PickOk(p, u, base, keep, f, now, un, want, less)) -> br.Res(B.reserve.pick(p, u, id, now, base, keep, f, s, l, o, h, un), u, id, now, base, keep, want, less, f, s, l, o, h, un):
  match p:
    case B.Fit{+j, +x}:
      br.res_fit(x, j, u, id, now, base, keep, want, less, f, s, l, o, h, un, po)
    case B.NoFit{+d}:
      (pa, pl) = po
      (pa, (pl, br.after_eq(u)))

def br.res_held(hd: Bool, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +f: B.Amt, +s: B.Amt, +l: B.Amt, +o: B.Amt, +h: List<&2, B.Hold>, +un: Nat) -> br.Res(B.reserve.held(hd, u, p, id, now, base, keep, want, less, f, s, l, o, h, un), u, id, now, base, keep, want, less, f, s, l, o, h, un):
  match hd:
    case True{}:
      Unit{}
    case False{}:
      br.res_pick(B.pick(less, u, base, keep, f, now, un, want, 0n), u, id, now, base, keep, want, less, f, s, l, o, h, un, br.pick_ok(less, u, base, keep, f, now, un, want))

def br.res_open(okb: Bool, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +f: B.Amt, +s: B.Amt, +l: B.Amt, +o: B.Amt, +h: List<&2, B.Hold>, +un: Nat) -> br.Res(B.reserve.open(okb, u, p, id, now, base, keep, want, less, f, s, l, o, h, un), u, id, now, base, keep, want, less, f, s, l, o, h, un):
  match okb:
    case True{}:
      br.res_held(B.held(id, h), u, p, id, now, base, keep, want, less, f, s, l, o, h, un)
    case False{}:
      Unit{}

# what the answer g says of the request on the account a
def br.ResA(g: B.Grant, +u: B.Use, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct) -> Type:
  br.Res(g, u, id, now, base, keep, want, less, S.free(a), S.spent(a), S.lent(a), S.over(a), S.holds(a), S.until(a))

# every answer of a reservation says it
def br.res(+u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, a: B.Acct) -> br.ResA(B.reserve(u, p, id, now, base, keep, want, less, a), u, id, now, base, keep, want, less, a):
  match a:
    case B.Acct{+f, +s, +l, +o, +h, +un}:
      br.res_open(B.allows(p, u), u, p, id, now, base, keep, want, less, f, s, l, o, h, un)

# a reservation answered g: g says it
def br.res_is(+u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, -g: B.Grant, e: {B.reserve(u, p, id, now, base, keep, want, less, a) == g : B.Grant}) -> br.ResA(g, u, id, now, base, keep, want, less, a):
  %e : br.ResA(_, u, id, now, base, keep, want, less, a)
  br.res(u, p, id, now, base, keep, want, less, a)

# The laws
# --------

# budget_grant_within
def br.within(+u: B.Use, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +i: Nat, +c: B.Ask, +a2: B.Acct, +t: Bool, +d: B.Dim, r: br.ResA(B.Granted{i, c, a2, t}, u, id, now, base, keep, want, less, a)) -> {Nat.add(S.at(d, S.free(a2)), S.at(d, S.amt(c))) == S.at(d, S.free(a)) : Nat} & {S.fits_in(u, base, keep, c, S.free(a), d) == True{} : Bool}:
  (rn, (rb, (rf, (ra, rt)))) = r
  +ef = rf
  %ra : {Nat.add(S.at(d, S.free(_)), S.at(d, S.amt(c))) == S.at(d, S.free(a)) : Nat} & {S.fits_in(u, base, keep, c, S.free(a), d) == True{} : Bool}
  (br.left(d, S.free(a), S.amt(c), Nat.add(S.at(d, S.amt(base)), S.at(d, S.amt(S.keep_of(u, keep)))), br.fits_at(d, u, base, keep, c, S.free(a), now, S.until(a), ef)), br.fits_at(d, u, base, keep, c, S.free(a), now, S.until(a), ef))

# budget_grant_on_time
def br.in_time(+u: B.Use, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +i: Nat, +c: B.Ask, +a2: B.Acct, +t: Bool, r: br.ResA(B.Granted{i, c, a2, t}, u, id, now, base, keep, want, less, a)) -> {S.on_time(u, base, keep, c, now, S.until(a)) == True{} : Bool} & {S.until(a2) == S.until(a) : Nat}:
  (rn, (rb, (rf, (ra, rt)))) = r
  %ra : {S.on_time(u, base, keep, c, now, S.until(a)) == True{} : Bool} & {S.until(_) == S.until(a) : Nat}
  (br.on_time_of(u, base, keep, c, S.free(a), now, S.until(a), rf), {==})

# budget_refuse_when_none_fits

# whether the offer m, if any, fits
def br.mfits(m: Maybe<&2, B.Ask>, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{z}:
      S.fits(u, base, keep, z, f, now, un)

def br.not_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      br.absurd({True{} == False{} : Bool}, e)
    case False{}:
      {==}

# none of xs fits: the offer at any place does not fit
def br.nf_m(j: Nat, xs: List<&2, B.Ask>, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, nf: {S.none_fit(u, base, keep, xs, f, now, un) == True{} : Bool}) -> {br.mfits(S.nth(j, xs), u, base, keep, f, now, un) == False{} : Bool}:
  match j:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{+y, +t}:
          br.not_true(S.fits(u, base, keep, y, f, now, un), br.and_l(Bool.not(S.fits(u, base, keep, y, f, now, un)), S.none_fit(u, base, keep, t, f, now, un), nf))
    case 1n+k:
      match xs:
        case Nil{}:
          {==}
        case Con{+y, +t}:
          br.nf_m(k, t, u, base, keep, f, now, un, br.and_r(Bool.not(S.fits(u, base, keep, y, f, now, un)), S.none_fit(u, base, keep, t, f, now, un), nf))

def br.nf_nth(+j: Nat, +xs: List<&2, B.Ask>, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, -x: B.Ask, e: {S.nth(j, xs) == Some{x} : Maybe<&2, B.Ask>}, nf: {S.none_fit(u, base, keep, xs, f, now, un) == True{} : Bool}) -> {S.fits(u, base, keep, x, f, now, un) == False{} : Bool}:
  %e : {br.mfits(_, u, base, keep, f, now, un) == False{} : Bool}
  br.nf_m(j, xs, u, base, keep, f, now, un, nf)

def br.none_pick(p: B.Pick, +u: B.Use, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +f: B.Amt, +s: B.Amt, +l: B.Amt, +o: B.Amt, +h: List<&2, B.Hold>, +un: Nat, po: br.PickOk(p, u, base, keep, f, now, un, want, less), none: {S.none_fit(u, base, keep, want <> less, f, now, un) == True{} : Bool}) -> {S.short_to(B.reserve.pick(p, u, id, now, base, keep, f, s, l, o, h, un)) == Some{S.after(u)} : Maybe<&2, B.Phase>}:
  match p:
    case B.Fit{+j, +x}:
      (pn, (pb, pf)) = po
      br.absurd({S.short_to(B.reserve.pick(B.Fit{j, x}, u, id, now, base, keep, f, s, l, o, h, un)) == Some{S.after(u)} : Maybe<&2, B.Phase>}, Equal.trans(Bool, False{}, S.fits(u, base, keep, x, f, now, un), True{}, Equal.sym(Bool, S.fits(u, base, keep, x, f, now, un), False{}, br.nf_nth(j, want <> less, u, base, keep, f, now, un, x, pn, none)), pf))
    case B.NoFit{d}:
      Equal.cong(B.Phase, Maybe<&2, B.Phase>, z => Some{z}, B.after(u), S.after(u), br.after_eq(u))

def br.none_short(a: B.Acct, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, ok: {S.allows(p, u) == True{} : Bool}, fresh: {S.has(id, S.holds(a)) == False{} : Bool}, none: {S.none_fit(u, base, keep, want <> less, S.free(a), now, S.until(a)) == True{} : Bool}) -> {S.short_to(B.reserve(u, p, id, now, base, keep, want, less, a)) == Some{S.after(u)} : Maybe<&2, B.Phase>}:
  match a:
    case B.Acct{+f, +s, +l, +o, +h, +un}:
      %br.allows_is(p, u, True{}, ok) : {S.short_to(B.reserve.open(_, u, p, id, now, base, keep, want, less, f, s, l, o, h, un)) == Some{S.after(u)} : Maybe<&2, B.Phase>}
      %br.held_is(id, h, False{}, fresh) : {S.short_to(B.reserve.held(_, u, p, id, now, base, keep, want, less, f, s, l, o, h, un)) == Some{S.after(u)} : Maybe<&2, B.Phase>}
      br.none_pick(B.pick(less, u, base, keep, f, now, un, want, 0n), u, id, now, base, keep, want, less, f, s, l, o, h, un, br.pick_ok(less, u, base, keep, f, now, un, want), none)

# budget_grant_holds
def br.holds(+u: B.Use, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +i: Nat, +c: B.Ask, +a2: B.Acct, +t: Bool, r: br.ResA(B.Granted{i, c, a2, t}, u, id, now, base, keep, want, less, a)) -> {S.holds(a2) == B.Hold{id, S.amt(c)} <> S.holds(a) : List<&2, B.Hold>} & {S.spent(a2) == S.spent(a) : B.Amt} & {S.lent(a2) == S.lent(a) : B.Amt} & {S.over(a2) == S.over(a) : B.Amt}:
  (rn, (rb, (rf, (ra, rt)))) = r
  %ra : {S.holds(_) == B.Hold{id, S.amt(c)} <> S.holds(a) : List<&2, B.Hold>} & {S.spent(_) == S.spent(a) : B.Amt} & {S.lent(_) == S.lent(a) : B.Amt} & {S.over(_) == S.over(a) : B.Amt}
  ({==}, ({==}, ({==}, {==})))

# budget_grant_first
def br.first(+u: B.Use, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +i: Nat, +c: B.Ask, +a2: B.Acct, +t: Bool, r: br.ResA(B.Granted{i, c, a2, t}, u, id, now, base, keep, want, less, a)) -> {S.nth(i, want <> less) == Some{c} : Maybe<&2, B.Ask>} & {S.none_fit(u, base, keep, S.before(i, want <> less), S.free(a), now, S.until(a)) == True{} : Bool}:
  (rn, (rb, (rf, (ra, rt)))) = r
  (rn, rb)

# budget_tight_exact
def br.tight(+u: B.Use, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +i: Nat, +c: B.Ask, +a2: B.Acct, +t: Bool, r: br.ResA(B.Granted{i, c, a2, t}, u, id, now, base, keep, want, less, a)) -> {t == Bool.not(S.fits(u, base, keep, c, S.free(a2), Nat.add(now, S.ms(c)), S.until(a2))) : Bool}:
  (rn, (rb, (rf, (ra, rt)))) = r
  %ra : {t == Bool.not(S.fits(u, base, keep, c, S.free(_), Nat.add(now, S.ms(c)), S.until(_))) : Bool}
  rt

# a fit offer is granted
def br.fit_granted(x: B.Ask, -j: Nat, -u: B.Use, -id: Nat, -now: Nat, -base: B.Ask, -keep: B.Ask, -f: B.Amt, -s: B.Amt, -l: B.Amt, -o: B.Amt, -h: List<&2, B.Hold>, -un: Nat) -> {S.granted(B.reserve.pick(B.Fit{j, x}, u, id, now, base, keep, f, s, l, o, h, un)) == True{} : Bool}:
  match x:
    case B.Ask{xa, xm}:
      {==}

def br.granted_pick(p: B.Pick, +u: B.Use, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +f: B.Amt, +s: B.Amt, +l: B.Amt, +o: B.Amt, +h: List<&2, B.Hold>, +un: Nat, po: br.PickOk(p, u, base, keep, f, now, un, want, less), some: {S.none_fit(u, base, keep, want <> less, f, now, un) == False{} : Bool}) -> {S.granted(B.reserve.pick(p, u, id, now, base, keep, f, s, l, o, h, un)) == True{} : Bool}:
  match p:
    case B.Fit{j, x}:
      br.fit_granted(x, j, u, id, now, base, keep, f, s, l, o, h, un)
    case B.NoFit{d}:
      (pa, pl) = po
      Equal.trans(Bool, False{}, S.none_fit(u, base, keep, want <> less, f, now, un), True{}, Equal.sym(Bool, S.none_fit(u, base, keep, want <> less, f, now, un), False{}, some), pa)

# budget_grant_when_fits
def br.when_fits(a: B.Acct, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, ok: {S.allows(p, u) == True{} : Bool}, fresh: {S.has(id, S.holds(a)) == False{} : Bool}, some: {S.none_fit(u, base, keep, want <> less, S.free(a), now, S.until(a)) == False{} : Bool}) -> {S.granted(B.reserve(u, p, id, now, base, keep, want, less, a)) == True{} : Bool}:
  match a:
    case B.Acct{+f, +s, +l, +o, +h, +un}:
      %br.allows_is(p, u, True{}, ok) : {S.granted(B.reserve.open(_, u, p, id, now, base, keep, want, less, f, s, l, o, h, un)) == True{} : Bool}
      %br.held_is(id, h, False{}, fresh) : {S.granted(B.reserve.held(_, u, p, id, now, base, keep, want, less, f, s, l, o, h, un)) == True{} : Bool}
      br.granted_pick(B.pick(less, u, base, keep, f, now, un, want, 0n), u, id, now, base, keep, want, less, f, s, l, o, h, un, br.pick_ok(less, u, base, keep, f, now, un, want), some)

# budget_refuse_stopped
def br.stopped(a: B.Acct, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, no: {S.allows(p, u) == False{} : Bool}) -> {B.reserve(u, p, id, now, base, keep, want, less, a) == B.Refused{B.Stopped{}, p} : B.Grant}:
  match a:
    case B.Acct{+f, +s, +l, +o, +h, +un}:
      %br.allows_is(p, u, False{}, no) : {B.reserve.open(_, u, p, id, now, base, keep, want, less, f, s, l, o, h, un) == B.Refused{B.Stopped{}, p} : B.Grant}
      {==}

# budget_refuse_held
def br.dup(a: B.Acct, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, ok: {S.allows(p, u) == True{} : Bool}, dup: {S.has(id, S.holds(a)) == True{} : Bool}) -> {B.reserve(u, p, id, now, base, keep, want, less, a) == B.Refused{B.Held{}, p} : B.Grant}:
  match a:
    case B.Acct{+f, +s, +l, +o, +h, +un}:
      %br.allows_is(p, u, True{}, ok) : {B.reserve.open(_, u, p, id, now, base, keep, want, less, f, s, l, o, h, un) == B.Refused{B.Held{}, p} : B.Grant}
      %br.held_is(id, h, True{}, dup) : {B.reserve.held(_, u, p, id, now, base, keep, want, less, f, s, l, o, h, un) == B.Refused{B.Held{}, p} : B.Grant}
      {==}

# a final answer x that fits the account a1 is granted on a2 = a1
def br.final_some(-a1: B.Acct, -a2: B.Acct, -base: B.Ask, -k2: B.Ask, -x: B.Ask, -now2: Nat, e: {a1 == a2 : B.Acct}, h: {S.fits(B.Final{}, base, k2, x, S.free(a1), now2, S.until(a1)) == True{} : Bool}) -> {S.none_fit(B.Final{}, base, k2, x <> Nil{}, S.free(a2), now2, S.until(a2)) == False{} : Bool}:
  %e : {S.none_fit(B.Final{}, base, k2, x <> Nil{}, S.free(_), now2, S.until(_)) == False{} : Bool}
  br.nf_single(S.fits(B.Final{}, base, k2, x, S.free(a1), now2, S.until(a1)), h)

# budget_final_reserve_kept
def br.final_kept(+id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +i: Nat, +c: B.Ask, +a2: B.Acct, +t: Bool, +x: B.Ask, +p2: B.Phase, +id2: Nat, +now2: Nat, +k2: B.Ask, r: br.ResA(B.Granted{i, c, a2, t}, B.Work{}, id, now, base, keep, want, less, a), within: {S.le(x, keep) == True{} : Bool}, ok: {S.allows(p2, B.Final{}) == True{} : Bool}, fresh: {S.has(id2, S.holds(a2)) == False{} : Bool}, soon: {Nat.is_le(now2, Nat.add(now, S.ms(c))) == True{} : Bool}) -> {S.granted(B.reserve(B.Final{}, p2, id2, now2, base, k2, x, Nil{}, a2)) == True{} : Bool}:
  (rn, (rb, (rf, (ra, rt)))) = r
  br.when_fits(a2, B.Final{}, p2, id2, now2, base, k2, x, Nil{}, ok, fresh, br.final_some(B.Acct{B.sub4(S.free(a), S.amt(c)), S.spent(a), S.lent(a), S.over(a), B.Hold{id, S.amt(c)} <> S.holds(a), S.until(a)}, a2, base, k2, x, now2, ra, br.final_fits(base, k2, x, keep, c, S.free(a), now, now2, S.until(a), within, rf, soon)))

# budget_base_kept
def br.base_kept(+u: B.Use, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +i: Nat, +c: B.Ask, +a2: B.Acct, +t: Bool, +x: B.Ask, +p2: B.Phase, +id2: Nat, +now2: Nat, +k2: B.Ask, r: br.ResA(B.Granted{i, c, a2, t}, u, id, now, base, keep, want, less, a), within: {S.le(x, base) == True{} : Bool}, ok: {S.allows(p2, B.Final{}) == True{} : Bool}, fresh: {S.has(id2, S.holds(a2)) == False{} : Bool}, ontime: {Nat.is_le(Nat.add(now2, S.ms(x)), S.until(a)) == True{} : Bool}) -> {S.granted(B.reserve(B.Final{}, p2, id2, now2, S.nothing(), k2, x, Nil{}, a2)) == True{} : Bool}:
  (rn, (rb, (rf, (ra, rt)))) = r
  br.when_fits(a2, B.Final{}, p2, id2, now2, S.nothing(), k2, x, Nil{}, ok, fresh, br.final_some(B.Acct{B.sub4(S.free(a), S.amt(c)), S.spent(a), S.lent(a), S.over(a), B.Hold{id, S.amt(c)} <> S.holds(a), S.until(a)}, a2, S.nothing(), k2, x, now2, ra, br.base_fits(u, base, keep, k2, x, c, S.free(a), now, now2, S.until(a), within, rf, ontime)))

# Funding
# -------

# what budget_fund_resumes funds: the ask with the reserves and the
# overrun, and the time past the deadline it needs
def br.fund_ask(+c: B.Ask, +base: B.Ask, +keep: B.Ask, +a: B.Acct, now: Nat) -> B.Ask:
  B.Ask{S.amt(S.plus(S.plus(S.plus(c, base), keep), B.Ask{S.over(a), 0n})), Nat.sub(Nat.add(now, S.ms(S.plus(S.plus(c, base), keep))), S.until(a))}

# in one spent dimension, the ask c with reserves b and k, funded with
# them and the overrun o on f free
def br.fund_b(+c: Nat, +b: Nat, +k: Nat, f: Nat, +o: Nat) -> Bool:
  Nat.is_le(Nat.add(c, Nat.add(b, k)), Nat.add(f, Nat.sub(Nat.add(Nat.add(Nat.add(c, b), k), o), o)))

def br.fund_le(+c: Nat, +b: Nat, +k: Nat, +f: Nat, +o: Nat) -> {br.fund_b(c, b, k, f, o) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(c, b), k), Nat.add(c, Nat.add(b, k)), br.add_assoc(c, b, k)) : {Nat.is_le(Nat.add(c, Nat.add(b, k)), Nat.add(f, Nat.sub(Nat.add(_, o), o))) == True{} : Bool}
  br.le_fund(Nat.add(c, Nat.add(b, k)), f, o)

# in duration, the ask c with reserves b and k at n, the deadline u moved
# by what they need past it
def br.fund_t(+n: Nat, +c: Nat, +b: Nat, +k: Nat, +u: Nat) -> Bool:
  Nat.is_le(Nat.add(n, Nat.add(c, Nat.add(b, k))), Nat.add(u, Nat.sub(Nat.add(n, Nat.add(Nat.add(c, b), k)), u)))

def br.fund_time(+n: Nat, +c: Nat, +b: Nat, +k: Nat, +u: Nat) -> {br.fund_t(n, c, b, k, u) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(c, b), k), Nat.add(c, Nat.add(b, k)), br.add_assoc(c, b, k)) : {Nat.is_le(Nat.add(n, Nat.add(c, Nat.add(b, k))), Nat.add(u, Nat.sub(Nat.add(n, _), u))) == True{} : Bool}
  br.le_top(Nat.add(n, Nat.add(c, Nat.add(b, k))), u)

# budget_fund_resumes
def br.resumes(c: B.Ask, base: B.Ask, keep: B.Ask, a: B.Acct, +id: Nat, +now: Nat, fresh: {S.has(id, S.holds(a)) == False{} : Bool}) -> {S.granted(B.reserve(B.Work{}, B.Working{}, id, now, base, keep, c, Nil{}, B.fund(br.fund_ask(c, base, keep, a, now), a))) == True{} : Bool}:
  match c:
    case B.Ask{cx, +cm}:
      match cx:
        case B.Amt{+c1, +c2, +c3, +c4}:
          match base:
            case B.Ask{bx, +bm}:
              match bx:
                case B.Amt{+b1, +b2, +b3, +b4}:
                  match keep:
                    case B.Ask{kx, +km}:
                      match kx:
                        case B.Amt{+k1, +k2, +k3, +k4}:
                          match a:
                            case B.Acct{fx, +s, +l, ox, +hs, +u}:
                              match fx:
                                case B.Amt{+f1, +f2, +f3, +f4}:
                                  match ox:
                                    case B.Amt{+o1, +o2, +o3, +o4}:
                                      +cA = {B.Ask{B.Amt{c1, c2, c3, c4}, cm} : B.Ask}
                                      +bA = {B.Ask{B.Amt{b1, b2, b3, b4}, bm} : B.Ask}
                                      +kA = {B.Ask{B.Amt{k1, k2, k3, k4}, km} : B.Ask}
                                      +aA = {B.Acct{B.Amt{f1, f2, f3, f4}, s, l, B.Amt{o1, o2, o3, o4}, hs, u} : B.Acct}
                                      +fa = {B.fund(br.fund_ask(cA, bA, kA, aA, now), aA) : B.Acct}
                                      br.when_fits(fa, B.Work{}, B.Working{}, id, now, bA, kA, cA, Nil{}, {==}, fresh, br.nf_single(S.fits(B.Work{}, bA, kA, cA, S.free(fa), now, S.until(fa)), br.and5(br.fund_b(c1, b1, k1, f1, o1), br.fund_b(c2, b2, k2, f2, o2), br.fund_t(now, cm, bm, km, u), br.fund_b(c3, b3, k3, f3, o3), br.fund_b(c4, b4, k4, f4, o4), br.fund_le(c1, b1, k1, f1, o1), br.fund_le(c2, b2, k2, f2, o2), br.fund_time(now, cm, bm, km, u), br.fund_le(c3, b3, k3, f3, o3), br.fund_le(c4, b4, k4, f4, o4))))
