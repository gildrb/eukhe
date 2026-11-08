# eukhe: the long division of bend/autoresearch/stats.bend (div) for the
# proof of LAW confidence_exact: its quotient is floor(a / b), at most the
# cap

import Base
import ../../../../bend/autoresearch/dec.bend as ArD
import ../../../../bend/autoresearch/line.bend as ArL
import ../../../../bend/autoresearch/stats.bend as ArT
import ../../../../spec/autoresearch/decimal.bend as SD
import ./nat.bend as CN
import ../../../../spec/autoresearch/stats.bend as SS
import ./big.bend as CB

def ac.or_r(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# B <= R or R < B
def ac.le_or_lt(B: Nat, R: Nat) -> {Bool.or(Nat.is_le(B, R), Nat.is_lt(R, B)) == True{} : Bool}:
  match B R:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      {==}
    case 1n++p 0n:
      {==}
    case 1n++p 1n++q:
      ac.le_or_lt(p, q)

# what one quotient digit and its remainder keep: q B + r stays, the
# remainder is below B when r was below (1 + f) B, at most f more, digits
def ac.DD(p: Nat & List<&2, Nat>, +q: Nat, +f: Nat, +R: Nat, +B: Nat) -> Type:
  (+q2, +r2) = p
  {Nat.add(Nat.mul(q2, B), ArT.big.val(r2)) == Nat.add(Nat.mul(q, B), R) : Nat} & ({Bool.or(Nat.is_le(Nat.mul(1n+f, B), R), Nat.is_lt(ArT.big.val(r2), B)) == True{} : Bool} & ({Nat.is_le(q2, Nat.add(q, f)) == True{} : Bool} & {SD.digits_ok(r2) == True{} : Bool}))

# r against b: below is r < B
def ac.below(+r: List<&2, Nat>, +b: List<&2, Nat>, +hr: {SD.digits_ok(r) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}) -> {Cmp.is_lt(ArT.big.cmp(r, b, EQ{})) == Nat.is_lt(ArT.big.val(r), ArT.big.val(b)) : Bool}:
  +c = Nat.cmp(ArT.big.val(r), ArT.big.val(b))
  %Equal.sym(Cmp, ArT.big.cmp(r, b, EQ{}), ArD.then(c, EQ{}), CB.ac.cmp_val(r, b, EQ{}, hr, hb)) : {Cmp.is_lt(_) == Nat.is_lt(ArT.big.val(r), ArT.big.val(b)) : Bool}
  %Equal.sym(Cmp, ArD.then(c, EQ{}), c, CB.ac.then_eq(c)) : {Cmp.is_lt(_) == Nat.is_lt(ArT.big.val(r), ArT.big.val(b)) : Bool}
  {==}

def ac.dd_at(less: Bool, +r: List<&2, Nat>, +b: List<&2, Nat>, +q: Nat, +g: Nat, more: Nat & List<&2, Nat>, +hless: {Cmp.is_lt(ArT.big.cmp(r, b, EQ{})) == less : Bool}, +hr: {SD.digits_ok(r) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}, ih: ac.DD(more, 1n+q, g, ArT.big.val(ArT.big.sub(r, b, 0n)), ArT.big.val(b))) -> ac.DD(ArT.div.digit.at(less, r, q, more), q, 1n+g, ArT.big.val(r), ArT.big.val(b)):
  match less:
    case True{}:
      +R = ArT.big.val(r)
      +B = ArT.big.val(b)
      +hl = Equal.trans(Bool, Nat.is_lt(R, B), Cmp.is_lt(ArT.big.cmp(r, b, EQ{})), True{}, Equal.sym(Bool, Cmp.is_lt(ArT.big.cmp(r, b, EQ{})), Nat.is_lt(R, B), ac.below(r, b, hr, hb)), hless)
      ({==}, (ac.or_r(Nat.is_le(Nat.mul(2n+g, B), R), Nat.is_lt(R, B), hl), (CN.ac.le_add(q, 1n+g), hr)))
    case False{}:
      (q2, r2) = more
      (i1, rest1) = ih
      (l1, rest2) = rest1
      (q1, k1) = rest2
      +R = ArT.big.val(r)
      +B = ArT.big.val(b)
      +hl = Equal.trans(Bool, Nat.is_lt(R, B), Cmp.is_lt(ArT.big.cmp(r, b, EQ{})), False{}, Equal.sym(Bool, Cmp.is_lt(ArT.big.cmp(r, b, EQ{})), Nat.is_lt(R, B), ac.below(r, b, hr, hb)), hless)
      +Vs = ArT.big.val(ArT.big.sub(r, b, 0n))
      +qB = Nat.mul(q, B)
      +hle = {%Equal.sym(Nat, Nat.add(B, 0n), B, CN.ac.add_zero(B)) : {Nat.is_le(_, R) == True{} : Bool}; CN.ac.le_of_not_lt(R, B, hl) : {Nat.is_le(Nat.add(B, 0n), R) == True{} : Bool}}
      +vs = CB.ac.val_sub(r, b, 0n, hr, hb, {==}, hle)
      +di = {%vs : {Nat.add(Nat.add(B, qB), Vs) == Nat.add(qB, _) : Nat}; %Equal.sym(Nat, Nat.add(B, 0n), B, CN.ac.add_zero(B)) : {Nat.add(Nat.add(B, qB), Vs) == Nat.add(qB, Nat.add(Vs, _)) : Nat}; %CN.ac.add_comm(B, Vs) : {Nat.add(Nat.add(B, qB), Vs) == Nat.add(qB, _) : Nat}; %CN.ac.add_assoc(qB, B, Vs) : {Nat.add(Nat.add(B, qB), Vs) == _ : Nat}; %CN.ac.add_comm(B, qB) : {Nat.add(Nat.add(B, qB), Vs) == Nat.add(_, Vs) : Nat}; {==} : {Nat.add(Nat.add(B, qB), Vs) == Nat.add(qB, R) : Nat}}
      +M1 = Nat.mul(1n+g, B)
      +dl = {%vs : {Bool.or(Nat.is_le(Nat.add(B, M1), _), Nat.is_lt(ArT.big.val(r2), B)) == True{} : Bool}; %Equal.sym(Nat, Nat.add(B, 0n), B, CN.ac.add_zero(B)) : {Bool.or(Nat.is_le(Nat.add(B, M1), Nat.add(Vs, _)), Nat.is_lt(ArT.big.val(r2), B)) == True{} : Bool}; %CN.ac.add_comm(B, Vs) : {Bool.or(Nat.is_le(Nat.add(B, M1), _), Nat.is_lt(ArT.big.val(r2), B)) == True{} : Bool}; %Equal.sym(Bool, Nat.is_le(Nat.add(B, M1), Nat.add(B, Vs)), Nat.is_le(M1, Vs), CN.ac.le_cancel(B, M1, Vs)) : {Bool.or(_, Nat.is_lt(ArT.big.val(r2), B)) == True{} : Bool}; l1 : {Bool.or(Nat.is_le(Nat.add(B, M1), R), Nat.is_lt(ArT.big.val(r2), B)) == True{} : Bool}}
      +dq = {%Equal.sym(Nat, Nat.add(q, 1n+g), 1n+Nat.add(q, g), CN.ac.add_succ(q, g)) : {Nat.is_le(q2, _) == True{} : Bool}; q1 : {Nat.is_le(q2, Nat.add(q, 1n+g)) == True{} : Bool}}
      (Equal.trans(Nat, Nat.add(Nat.mul(q2, B), ArT.big.val(r2)), Nat.add(Nat.add(B, qB), Vs), Nat.add(qB, R), i1, di), (dl, (dq, k1)))

# div.digit
def ac.dd(f: Nat, +r: List<&2, Nat>, +b: List<&2, Nat>, +q: Nat, +hr: {SD.digits_ok(r) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}) -> ac.DD(ArT.div.digit(f, r, b, q), q, f, ArT.big.val(r), ArT.big.val(b)):
  match f:
    case 0n:
      +R = ArT.big.val(r)
      +B = ArT.big.val(b)
      ({==}, ({%Equal.sym(Nat, Nat.add(B, 0n), B, CN.ac.add_zero(B)) : {Bool.or(Nat.is_le(_, R), Nat.is_lt(R, B)) == True{} : Bool}; ac.le_or_lt(B, R) : {Bool.or(Nat.is_le(Nat.add(B, 0n), R), Nat.is_lt(R, B)) == True{} : Bool}}, (CN.ac.le_add(q, 0n), hr)))
    case 1n++g:
      +r2 = ArT.big.sub(r, b, 0n)
      ac.dd_at(Cmp.is_lt(ArT.big.cmp(r, b, EQ{})), r, b, q, g, ArT.div.digit(g, r2, b, 1n+q), {==}, hr, hb, ac.dd(g, r2, b, 1n+q, CB.ac.dok_sub(r, b, 0n, hr), hb))

# Long division
# -------------

# the remainder the long division leaves
def ac.drem(ds: List<&2, Nat>, qr: Nat & List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      (q, r) = qr
      r
    case d <> t:
      (q, r) = qr
      ac.drem(t, ArT.div.digit(9n, d <> r, b, 0n), b)

# what has been divided so far: quotient digits q <> qs, remainder r
def ac.cur(qr: Nat & List<&2, Nat>, +qs: List<&2, Nat>, +B: Nat) -> Nat:
  (q, r) = qr
  Nat.add(Nat.mul(ArT.big.val(q <> qs), B), ArT.big.val(r))

# a quotient digit and a remainder below the divisor
def ac.QR(qr: Nat & List<&2, Nat>, +b: List<&2, Nat>) -> Type:
  (q, r) = qr
  {Nat.is_le(q, 9n) == True{} : Bool} & ({SD.digits_ok(r) == True{} : Bool} & {Nat.is_lt(ArT.big.val(r), ArT.big.val(b)) == True{} : Bool})

# the long division divides: quotient B + remainder is what was left to
# divide, the remainder below B, the quotient digits
def ac.G(ds: List<&2, Nat>, qr: Nat & List<&2, Nat>, +b: List<&2, Nat>, +qs: List<&2, Nat>) -> Type:
  {Nat.add(Nat.mul(ArT.big.val(ArT.div.go(ds, qr, b, qs)), ArT.big.val(b)), ArT.big.val(ac.drem(ds, qr, b))) == SD.num.go(ds, ac.cur(qr, qs, ArT.big.val(b))) : Nat} & ({Nat.is_lt(ArT.big.val(ac.drem(ds, qr, b)), ArT.big.val(b)) == True{} : Bool} & {SD.digits_ok(ArT.div.go(ds, qr, b, qs)) == True{} : Bool})

# a digit below 10 B
def ac.lt_10B(+d: Nat, +R: Nat, +B: Nat, +hd: {Nat.is_lt(d, 10n) == True{} : Bool}, +hl: {Nat.is_lt(R, B) == True{} : Bool}) -> {Nat.is_le(Nat.mul(10n, B), Nat.add(d, Nat.mul(R, 10n))) == False{} : Bool}:
  +MR = Nat.mul(R, 10n)
  +h1 = CN.ac.mul10_mono(1n+R, B, {%CN.ac.lt_le_succ(R, B) : {_ == True{} : Bool}; hl : {Nat.is_le(1n+R, B) == True{} : Bool}})
  +h2 = {%CN.ac.add_comm(MR, d) : {Nat.is_lt(_, Nat.add(10n, MR)) == True{} : Bool}; %CN.ac.add_comm(MR, 10n) : {Nat.is_lt(Nat.add(MR, d), _) == True{} : Bool}; %Equal.sym(Bool, Nat.is_lt(Nat.add(MR, d), Nat.add(MR, 10n)), Nat.is_lt(d, 10n), CN.ac.lt_cancel(MR, d, 10n)) : {_ == True{} : Bool}; hd : {Nat.is_lt(Nat.add(d, MR), Nat.add(10n, MR)) == True{} : Bool}}
  +h3 = CN.ac.lt_le_trans(Nat.add(d, MR), Nat.add(10n, MR), Nat.mul(B, 10n), h2, h1)
  %CN.ac.mul_comm(B, 10n) : {Nat.is_le(_, Nat.add(d, MR)) == False{} : Bool}
  CN.ac.lt_not_le(Nat.add(d, MR), Nat.mul(B, 10n), h3)

def ac.qr_next(p: Nat & List<&2, Nat>, +d: Nat, +r: List<&2, Nat>, +b: List<&2, Nat>, +hd: {Nat.is_lt(d, 10n) == True{} : Bool}, +hl: {Nat.is_lt(ArT.big.val(r), ArT.big.val(b)) == True{} : Bool}, dd: ac.DD(p, 0n, 9n, ArT.big.val(d <> r), ArT.big.val(b))) -> ac.QR(p, b):
  (+q2, +r2) = p
  (i1, rest1) = dd
  (l1, rest2) = rest1
  (dq, dk) = rest2
  +B = ArT.big.val(b)
  +R = ArT.big.val(r)
  +big = ac.lt_10B(d, R, B, hd, hl)
  +hl2 = {%big : {Bool.or(_, Nat.is_lt(ArT.big.val(r2), B)) == True{} : Bool}; l1 : {Bool.or(False{}, Nat.is_lt(ArT.big.val(r2), B)) == True{} : Bool}}
  (dq, (dk, hl2))

def ac.cur_next(p: Nat & List<&2, Nat>, +q: Nat, +r: List<&2, Nat>, +qs: List<&2, Nat>, +d: Nat, +b: List<&2, Nat>, dd: ac.DD(p, 0n, 9n, ArT.big.val(d <> r), ArT.big.val(b))) -> {ac.cur(p, q <> qs, ArT.big.val(b)) == Nat.add(Nat.mul(ac.cur((q, r), qs, ArT.big.val(b)), 10n), d) : Nat}:
  (+q2, +r2) = p
  (i1, rest1) = dd
  +B = ArT.big.val(b)
  +R = ArT.big.val(r)
  +VQ = ArT.big.val(q <> qs)
  +qB = Nat.mul(q2, B)
  +r2v = ArT.big.val(r2)
  +M10 = Nat.mul(VQ, 10n)
  +X1 = Nat.mul(M10, B)
  +VB = Nat.mul(VQ, B)
  +X2 = Nat.mul(VB, 10n)
  +MR = Nat.mul(R, 10n)
  +rhs = Nat.add(Nat.mul(Nat.add(VB, R), 10n), d)
  %Equal.sym(Nat, Nat.mul(Nat.add(q2, M10), B), Nat.add(qB, X1), CN.ac.mul_add(q2, M10, B)) : {Nat.add(_, r2v) == rhs : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(qB, X1), r2v), Nat.add(Nat.add(qB, r2v), X1), CN.ac.add_rcomm(qB, X1, r2v)) : {_ == rhs : Nat}
  %Equal.sym(Nat, Nat.add(qB, r2v), Nat.add(d, MR), i1) : {Nat.add(_, X1) == rhs : Nat}
  %Equal.sym(Nat, X1, Nat.mul(Nat.mul(VQ, B), 10n), CN.ac.mul_rcomm(VQ, 10n, B)) : {Nat.add(Nat.add(d, MR), _) == rhs : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(VB, R), 10n), Nat.add(X2, MR), CN.ac.mul_add(VB, R, 10n)) : {Nat.add(Nat.add(d, MR), X2) == Nat.add(_, d) : Nat}
  %CN.ac.add_comm(X2, Nat.add(d, MR)) : {_ == Nat.add(Nat.add(X2, MR), d) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(X2, MR), d), Nat.add(X2, Nat.add(MR, d)), CN.ac.add_assoc(X2, MR, d)) : {Nat.add(X2, Nat.add(d, MR)) == _ : Nat}
  %CN.ac.add_comm(d, MR) : {Nat.add(X2, Nat.add(d, MR)) == Nat.add(X2, _) : Nat}
  {==}

def ac.go_fin(+t: List<&2, Nat>, +b: List<&2, Nat>, +q: Nat, +r: List<&2, Nat>, +qs: List<&2, Nat>, +d: Nat, ih: ac.G(t, ArT.div.digit(9n, d <> r, b, 0n), b, q <> qs), cu: {ac.cur(ArT.div.digit(9n, d <> r, b, 0n), q <> qs, ArT.big.val(b)) == Nat.add(Nat.mul(ac.cur((q, r), qs, ArT.big.val(b)), 10n), d) : Nat}) -> ac.G(d <> t, (q, r), b, qs):
  (g1, grest) = ih
  +B = ArT.big.val(b)
  (Equal.trans(Nat, Nat.add(Nat.mul(ArT.big.val(ArT.div.go(t, ArT.div.digit(9n, d <> r, b, 0n), b, q <> qs)), B), ArT.big.val(ac.drem(t, ArT.div.digit(9n, d <> r, b, 0n), b))), SD.num.go(t, ac.cur(ArT.div.digit(9n, d <> r, b, 0n), q <> qs, B)), SD.num.go(t, Nat.add(Nat.mul(ac.cur((q, r), qs, B), 10n), d)), g1, Equal.cong(Nat, Nat, x => SD.num.go(t, x), ac.cur(ArT.div.digit(9n, d <> r, b, 0n), q <> qs, B), Nat.add(Nat.mul(ac.cur((q, r), qs, B), 10n), d), cu)), grest)

def ac.go(ds: List<&2, Nat>, qr: Nat & List<&2, Nat>, +b: List<&2, Nat>, +qs: List<&2, Nat>, +hb: {SD.digits_ok(b) == True{} : Bool}, +hds: {SD.digits_ok(ds) == True{} : Bool}, +hqs: {SD.digits_ok(qs) == True{} : Bool}, hqr: ac.QR(qr, b)) -> ac.G(ds, qr, b, qs):
  match ds:
    case Nil{}:
      (q, r) = qr
      (q9, rest) = hqr
      (hr, hl) = rest
      ({==}, (hl, CB.ac.dok_cons(q, qs, {%CN.ac.le_lt_succ(q, 9n) : {_ == True{} : Bool}; q9 : {Nat.is_lt(q, 10n) == True{} : Bool}}, hqs)))
    case +d <> +t:
      (+q, +r) = qr
      (q9, rest) = hqr
      (hr, hl) = rest
      +hd = CB.ac.dok_hd(d, t, hds)
      +B = ArT.big.val(b)
      +hdr = CB.ac.dok_cons(d, r, hd, hr)
      qr2 = ac.qr_next(ArT.div.digit(9n, d <> r, b, 0n), d, r, b, hd, hl, ac.dd(9n, d <> r, b, 0n, hdr, hb))
      +cu = ac.cur_next(ArT.div.digit(9n, d <> r, b, 0n), q, r, qs, d, b, ac.dd(9n, d <> r, b, 0n, hdr, hb))
      ac.go_fin(t, b, q, r, qs, d, ac.go(t, ArT.div.digit(9n, d <> r, b, 0n), b, q <> qs, hb, CB.ac.dok_tl(d, t, hds), CB.ac.dok_cons(q, qs, {%CN.ac.le_lt_succ(q, 9n) : {_ == True{} : Bool}; q9 : {Nat.is_lt(q, 10n) == True{} : Bool}}, hqs), qr2), cu)

# The quotient
# ------------

def ac.rev_rev(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {ArT.rev(ArT.rev(xs, acc), Nil{}) == ArT.rev(acc, xs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      ac.rev_rev(t, x <> acc)

# the digits turned around are worth the number again
def ac.num_rev(+a: List<&2, Nat>) -> {SD.num.go(ArT.rev(a, Nil{}), 0n) == ArT.big.val(a) : Nat}:
  Equal.trans(Nat, SD.num.go(ArT.rev(a, Nil{}), 0n), ArT.big.val(ArT.rev(ArT.rev(a, Nil{}), Nil{})), ArT.big.val(a), Equal.sym(Nat, ArT.big.val(ArT.rev(ArT.rev(a, Nil{}), Nil{})), SD.num.go(ArT.rev(a, Nil{}), 0n), CB.ac.val_rev(ArT.rev(a, Nil{}), Nil{})), Equal.cong(List<&2, Nat>, Nat, x => ArT.big.val(x), ArT.rev(ArT.rev(a, Nil{}), Nil{}), a, ac.rev_rev(a, Nil{})))

# q B + r = n with r < B: n / B = q
def ac.div_by(+n: Nat, B: Nat, +q: Nat, +r: Nat, e: {Nat.add(Nat.mul(q, B), r) == n : Nat}, h: {Nat.is_lt(r, B) == True{} : Bool}) -> {Nat.div(n, B) == q : Nat}:
  match B:
    case 0n:
      CN.ac.lt0({Nat.div(n, 0n) == q : Nat}, r, h)
    case 1n++bp:
      CN.ac.div_unique(n, bp, q, r, e, {%Equal.sym(Bool, Nat.is_le(r, bp), Nat.is_lt(r, 1n+bp), CN.ac.le_lt_succ(r, bp)) : {_ == True{} : Bool}; h : {Nat.is_le(r, bp) == True{} : Bool}})

def ac.vs_at(r: List<&2, Nat>, +x: Nat, +V: Nat, e: {ArT.big.val(r) == V : Nat}) -> {ArT.big.val(ArL.strip.at(x, r)) == Nat.add(x, Nat.mul(V, 10n)) : Nat}:
  match r:
    case Nil{}:
      match x:
        case 0n:
          %e : {0n == Nat.mul(_, 10n) : Nat}
          {==}
        case 1n++p:
          %e : {ArT.big.val(ArL.strip.at(1n+p, Nil{})) == Nat.add(1n+p, Nat.mul(_, 10n)) : Nat}
          {==}
    case y <> u:
      %e : {ArT.big.val(ArL.strip.at(x, y <> u)) == Nat.add(x, Nat.mul(_, 10n)) : Nat}
      {==}

# strip keeps the value
def ac.val_strip(xs: List<&2, Nat>) -> {ArT.big.val(ArL.strip(xs)) == ArT.big.val(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      ac.vs_at(ArL.strip(t), x, ArT.big.val(t), ac.val_strip(t))

def ac.ls0(r: List<&2, Nat>, +x: Nat, +V: Nat, ih0: {Nat.is_le(ArD.len(r), 0n) == Nat.is_le(V, 0n) : Bool}) -> {Nat.is_le(ArD.len(ArL.strip.at(x, r)), 0n) == Nat.is_le(Nat.add(x, Nat.mul(V, 10n)), 0n) : Bool}:
  match r:
    case Nil{}:
      match x:
        case 0n:
          +e0 = CN.ac.le0_eq(V, Equal.sym(Bool, True{}, Nat.is_le(V, 0n), ih0))
          %Equal.sym(Nat, V, 0n, e0) : {True{} == Nat.is_le(Nat.mul(_, 10n), 0n) : Bool}
          {==}
        case 1n++p:
          {==}
    case y <> u:
      match V:
        case 0n:
          CN.ac.ft({Nat.is_le(ArD.len(ArL.strip.at(x, y <> u)), 0n) == Nat.is_le(Nat.add(x, Nat.mul(0n, 10n)), 0n) : Bool}, ih0)
        case 1n++v:
          %CN.ac.add_comm(Nat.mul(1n+v, 10n), x) : {False{} == Nat.is_le(_, 0n) : Bool}
          {==}

def ac.le0_is_eq(n: Nat) -> {Nat.is_le(n, 0n) == Nat.is_eq(n, 0n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      {==}

# nothing left once stripped: worth 0
def ac.strip0(q: List<&2, Nat>) -> {Nat.is_le(ArD.len(ArL.strip(q)), 0n) == Nat.is_eq(ArT.big.val(q), 0n) : Bool}:
  match q:
    case Nil{}:
      {==}
    case +x <> +t:
      +V = ArT.big.val(t)
      +n = Nat.add(x, Nat.mul(V, 10n))
      Equal.trans(Bool, Nat.is_le(ArD.len(ArL.strip.at(x, ArL.strip(t))), 0n), Nat.is_le(n, 0n), Nat.is_eq(n, 0n), ac.ls0(ArL.strip(t), x, V, Equal.trans(Bool, Nat.is_le(ArD.len(ArL.strip(t)), 0n), Nat.is_eq(V, 0n), Nat.is_le(V, 0n), ac.strip0(t), Equal.sym(Bool, Nat.is_le(V, 0n), Nat.is_eq(V, 0n), ac.le0_is_eq(V)))), ac.le0_is_eq(n))

def ac.shed0(k: Nat) -> {SS.shed(k, 0n) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      ac.shed0(j)

def ac.ls_step(r: List<&2, Nat>, +x: Nat, +j: Nat, -X: Bool, ih: {Nat.is_le(ArD.len(r), j) == X : Bool}) -> {Nat.is_le(ArD.len(ArL.strip.at(x, r)), 1n+j) == X : Bool}:
  match r:
    case Nil{}:
      match x:
        case 0n:
          Equal.trans(Bool, True{}, Nat.is_le(0n, j), X, Equal.sym(Bool, Nat.is_le(0n, j), True{}, CN.ac.le_zero(j)), ih)
        case 1n++p:
          ih
    case y <> u:
      ih

# at most k digits once stripped: nothing left after shedding k digits
def ac.len_shed(q: List<&2, Nat>, k: Nat, +h: {SD.digits_ok(q) == True{} : Bool}) -> {Nat.is_le(ArD.len(ArL.strip(q)), k) == Nat.is_eq(SS.shed(k, ArT.big.val(q)), 0n) : Bool}:
  match q:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n++j:
          %Equal.sym(Nat, SS.shed(j, 0n), 0n, ac.shed0(j)) : {Nat.is_le(0n, 1n+j) == Nat.is_eq(_, 0n) : Bool}
          {==}
    case +x <> +t:
      match k:
        case 0n:
          ac.strip0(x <> t)
        case 1n++j:
          +V = ArT.big.val(t)
          +n = Nat.add(x, Nat.mul(V, 10n))
          +ed = ac.div_by(n, 10n, V, x, CN.ac.add_comm(Nat.mul(V, 10n), x), CB.ac.dok_hd(x, t, h))
          %Equal.sym(Nat, Nat.div(n, 10n), V, ed) : {Nat.is_le(ArD.len(ArL.strip.at(x, ArL.strip(t))), 1n+j) == Nat.is_eq(SS.shed(j, _), 0n) : Bool}
          ac.ls_step(ArL.strip(t), x, j, Nat.is_eq(SS.shed(j, V), 0n), ac.len_shed(t, j, CB.ac.dok_tl(x, t, h)))

def ac.fit(c: Bool, +sq: List<&2, Nat>, +Q: Nat, ev: {ArT.big.val(sq) == Q : Nat}) -> {ArT.div.fit(c, sq) == SS.capped.at(c, Q) : Nat}:
  match c:
    case True{}:
      ev
    case False{}:
      {==}

def ac.div_ok2(+a: List<&2, Nat>, +b: List<&2, Nat>, g: ac.G(ArT.rev(a, Nil{}), (0n, Nil{}), b, Nil{})) -> {ArT.div(a, b) == SS.capped(Nat.div(ArT.big.val(a), ArT.big.val(b))) : Nat}:
  (g1, grest) = g
  (g2, g3) = grest
  +L = ArT.div.go(ArT.rev(a, Nil{}), (0n, Nil{}), b, Nil{})
  +B = ArT.big.val(b)
  +Q = ArT.big.val(L)
  +e = {%ac.num_rev(a) : {Nat.add(Nat.mul(Q, B), ArT.big.val(ac.drem(ArT.rev(a, Nil{}), (0n, Nil{}), b))) == _ : Nat}; g1 : {Nat.add(Nat.mul(Q, B), ArT.big.val(ac.drem(ArT.rev(a, Nil{}), (0n, Nil{}), b))) == ArT.big.val(a) : Nat}}
  +ed = ac.div_by(ArT.big.val(a), B, Q, ArT.big.val(ac.drem(ArT.rev(a, Nil{}), (0n, Nil{}), b)), e, g2)
  %Equal.sym(Nat, Nat.div(ArT.big.val(a), B), Q, ed) : {ArT.div(a, b) == SS.capped(_) : Nat}
  %ac.len_shed(L, 9n, g3) : {ArT.div.fit(Nat.is_le(ArD.len(ArL.strip(L)), 9n), ArL.strip(L)) == SS.capped.at(_, Q) : Nat}
  ac.fit(Nat.is_le(ArD.len(ArL.strip(L)), 9n), ArL.strip(L), Q, ac.val_strip(L))

# div(a, b) = a / b, or the cap past 9 digits, for b > 0
def ac.div_ok(+a: List<&2, Nat>, +b: List<&2, Nat>, +ha: {SD.digits_ok(a) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}, hB: {Nat.is_lt(0n, ArT.big.val(b)) == True{} : Bool}) -> {ArT.div(a, b) == SS.capped(Nat.div(ArT.big.val(a), ArT.big.val(b))) : Nat}:
  +hd = CB.ac.dok_rev(a, Nil{}, ha, {==})
  ac.div_ok2(a, b, ac.go(ArT.rev(a, Nil{}), (0n, Nil{}), b, Nil{}, hb, hd, {==}, ({==}, ({==}, hB))))
