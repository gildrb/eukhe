# eukhe: lemmas the proofs of area timeouts share

import Base
import ../../bend/ffi_timeouts.bend as FT
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/timeouts.bend as Timeouts
import ../autoresearch/base/conf/nat.bend as CN
import ../wire/wire_u32_round_trip.bend as PWU

# The reply
# ---------

# the entry counts digits as the wire does
def tmo.digits(f: Nat, q: Nat) -> {LawsBase.wire_digits.go(f, q) == FT.digits.go(f, q) : Nat}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      match q:
        case 0n:
          {==}
        case 1n+p:
          %tmo.digits(g, Nat.div(1n+p, 10n)) : {1n+LawsBase.wire_digits.go(g, Nat.div(1n+p, 10n)) == 1n+_ : Nat}
          {==}

# the entry's bound is the laws'
def tmo.below(+x: Nat) -> {Timeouts.tw_below(x) == FT.fits(x) : Bool}:
  %tmo.digits(x, Nat.div(x, 10n)) : {Timeouts.tw_below(x) == Nat.is_le(1n+_, 14n) : Bool}
  {==}

# the entry spells the values as the laws do
def tmo.spell(xs: List<&2, Nat>) -> {Timeouts.tw_spell_values(xs) == FT.put_nats(xs, "") : String}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      %tmo.spell(r) : {Wr.put_nat(x, Timeouts.tw_spell_values(r)) == Wr.put_nat(x, _) : String}
      {==}

# Magnitude: a value past the wire stays past it in a sum or a product
# ---------------------------------------------------------------------

# the quotient of divmod.go is at most its dividend plus its accumulator
def tmo.q(n: Nat, m: Nat, +d: Nat, +r: Nat) -> {Nat.is_le(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), Nat.add(n, d)) == True{} : Bool}:
  match n:
    case 0n:
      PWU.wu_le_refl(d)
    case 1n++np:
      match m:
        case 0n:
          %CN.ac.add_succ(np, d) : {Nat.is_le(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), _) == True{} : Bool}
          tmo.q(np, r, 1n+d, 0n)
        case 1n++mp:
          PWU.wu_le_succ_r(Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r)), Nat.add(np, d), tmo.q(np, mp, d, 1n+r))

def tmo.le_rw(-a: Nat, -b: Nat, -c: Nat, h: {Nat.is_le(a, b) == True{} : Bool}, e: {b == c : Nat}) -> {Nat.is_le(a, c) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  h

# n / 10 <= n
def tmo.div10_le(+n: Nat) -> {Nat.is_le(Nat.div(n, 10n), n) == True{} : Bool}:
  tmo.le_rw(Nat.div(n, 10n), Nat.add(n, 0n), n, tmo.q(n, 9n, 0n, 0n), CN.ac.add_zero(n))

# (1 + p) / 10 <= p
def tmo.div10_lt(+p: Nat) -> {Nat.is_le(Nat.div(1n+p, 10n), p) == True{} : Bool}:
  tmo.le_rw(Nat.div(1n+p, 10n), Nat.add(p, 0n), p, tmo.q(p, 8n, 0n, 1n), CN.ac.add_zero(p))

# (1 + p) / 2 <= p
def tmo.div2_lt(+p: Nat) -> {Nat.is_le(Nat.div(1n+p, 2n), p) == True{} : Bool}:
  tmo.le_rw(Nat.div(1n+p, 2n), Nat.add(p, 0n), p, tmo.q(p, 0n, 0n, 1n), CN.ac.add_zero(p))

# more digits for a larger higher part (with enough fuel for it)
def tmo.go_mono(f: Nat, q: Nat, f2: Nat, q2: Nat, hq: {Nat.is_le(q, q2) == True{} : Bool}, hf: {Nat.is_le(q2, f2) == True{} : Bool}) -> {Nat.is_le(FT.digits.go(f, q), FT.digits.go(f2, q2)) == True{} : Bool}:
  match f:
    case 0n:
      PWU.wu_le_zero(FT.digits.go(f2, q2))
    case 1n+g:
      match q:
        case 0n:
          PWU.wu_le_zero(FT.digits.go(f2, q2))
        case 1n++p:
          match f2:
            case 0n:
              match q2:
                case 0n:
                  CN.ac.ft({Nat.is_le(1n+FT.digits.go(g, Nat.div(1n+p, 10n)), 0n) == True{} : Bool}, hq)
                case 1n+p2:
                  CN.ac.ft({Nat.is_le(1n+FT.digits.go(g, Nat.div(1n+p, 10n)), 0n) == True{} : Bool}, hf)
            case 1n++g2:
              match q2:
                case 0n:
                  CN.ac.ft({Nat.is_le(1n+FT.digits.go(g, Nat.div(1n+p, 10n)), 0n) == True{} : Bool}, hq)
                case 1n++p2:
                  tmo.go_mono(g, Nat.div(1n+p, 10n), g2, Nat.div(1n+p2, 10n), PWU.wu_div_mono(1n+p, 1n+p2, hq), PWU.wu_le_trans(Nat.div(1n+p2, 10n), p2, g2, tmo.div10_lt(p2), hf))

# a larger Nat has at least as many digits
def tmo.digits_mono(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(FT.digits(a), FT.digits(b)) == True{} : Bool}:
  tmo.go_mono(a, Nat.div(a, 10n), b, Nat.div(b, 10n), PWU.wu_div_mono(a, b, h), tmo.div10_le(b))

# x not at most c, x <= y: y not at most c
def tmo.le_false(x: Nat, y: Nat, c: Nat, h: {Nat.is_le(x, y) == True{} : Bool}, n: {Nat.is_le(x, c) == False{} : Bool}) -> {Nat.is_le(y, c) == False{} : Bool}:
  match x y c:
    case 0n y c:
      match c:
        case 0n:
          CN.ac.tf({Nat.is_le(y, 0n) == False{} : Bool}, n)
        case 1n+cp:
          CN.ac.tf({Nat.is_le(y, 1n+cp) == False{} : Bool}, n)
    case 1n+a 0n c:
      CN.ac.ft({Nat.is_le(0n, c) == False{} : Bool}, h)
    case 1n+a 1n+b 0n:
      {==}
    case 1n+a 1n+b 1n+cp:
      tmo.le_false(a, b, cp, h, n)

# a value past the wire: every larger one is past it
def tmo.fits_mono(+x: Nat, +y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}, n: {FT.fits(x) == False{} : Bool}) -> {FT.fits(y) == False{} : Bool}:
  tmo.le_false(FT.digits(x), FT.digits(y), 14n, tmo.digits_mono(x, y, h), n)

def tmo.le_add_l(a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      PWU.wu_le_zero(b)
    case 1n+p:
      tmo.le_add_l(p, b)

def tmo.le_add_r(a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      PWU.wu_le_refl(b)
    case 1n++p:
      PWU.wu_le_succ_r(b, Nat.add(p, b), tmo.le_add_r(p, b))

# Capped sums and products
# ------------------------

def tmo.plus.at(ba: Bool, bb: Bool, +a: Nat, +b: Nat, ea: {FT.fits(a) == ba : Bool}, eb: {FT.fits(b) == bb : Bool}) -> {FT.plus(FT.fit.put(ba, a), FT.fit.put(bb, b)) == FT.fit(Nat.add(a, b)) : Maybe<&2, Nat>}:
  match ba:
    case False{}:
      %Equal.sym(Bool, FT.fits(Nat.add(a, b)), False{}, tmo.fits_mono(a, Nat.add(a, b), tmo.le_add_l(a, b), ea)) : {None{} == FT.fit.put(_, Nat.add(a, b)) : Maybe<&2, Nat>}
      {==}
    case True{}:
      match bb:
        case False{}:
          %Equal.sym(Bool, FT.fits(Nat.add(a, b)), False{}, tmo.fits_mono(b, Nat.add(a, b), tmo.le_add_r(a, b), eb)) : {None{} == FT.fit.put(_, Nat.add(a, b)) : Maybe<&2, Nat>}
          {==}
        case True{}:
          {==}

# the capped sum of two values is the value of their sum
def tmo.plus(+a: Nat, +b: Nat) -> {FT.plus(FT.fit(a), FT.fit(b)) == FT.fit(Nat.add(a, b)) : Maybe<&2, Nat>}:
  tmo.plus.at(FT.fits(a), FT.fits(b), a, b, {==}, {==})

# the capped sum of two capped values
def tmo.pc(-ma: Maybe<&2, Nat>, -mb: Maybe<&2, Nat>, +a: Nat, +b: Nat, ea: {ma == FT.fit(a) : Maybe<&2, Nat>}, eb: {mb == FT.fit(b) : Maybe<&2, Nat>}) -> {FT.plus(ma, mb) == FT.fit(Nat.add(a, b)) : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, ma, FT.fit(a), ea) : {FT.plus(_, mb) == FT.fit(Nat.add(a, b)) : Maybe<&2, Nat>}
  %Equal.sym(Maybe<&2, Nat>, mb, FT.fit(b), eb) : {FT.plus(FT.fit(a), _) == FT.fit(Nat.add(a, b)) : Maybe<&2, Nat>}
  tmo.plus(a, b)

# 2 q y + r y is (2 q + r) y
def tmo.arith(+q: Nat, +r: Nat, +y: Nat) -> {Nat.mul(Nat.add(Nat.mul(q, 2n), r), y) == Nat.add(Nat.add(Nat.mul(q, y), Nat.mul(q, y)), Nat.mul(r, y)) : Nat}:
  +qy = Nat.mul(q, y)
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(q, 2n), r), y), Nat.add(Nat.mul(Nat.mul(q, 2n), y), Nat.mul(r, y)), CN.ac.mul_add(Nat.mul(q, 2n), r, y)) : {_ == Nat.add(Nat.add(qy, qy), Nat.mul(r, y)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(q, 2n), y), Nat.mul(Nat.mul(q, y), 2n), CN.ac.mul_rcomm(q, 2n, y)) : {Nat.add(_, Nat.mul(r, y)) == Nat.add(Nat.add(qy, qy), Nat.mul(r, y)) : Nat}
  %Equal.sym(Nat, Nat.mul(qy, 2n), Nat.mul(2n, qy), CN.ac.mul_comm(qy, 2n)) : {Nat.add(_, Nat.mul(r, y)) == Nat.add(Nat.add(qy, qy), Nat.mul(r, y)) : Nat}
  %Equal.sym(Nat, Nat.add(qy, 0n), qy, CN.ac.add_zero(qy)) : {Nat.add(Nat.add(qy, _), Nat.mul(r, y)) == Nat.add(Nat.add(qy, qy), Nat.mul(r, y)) : Nat}
  {==}

def tmo.fit_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {FT.fit(a) == FT.fit(b) : Maybe<&2, Nat>}:
  %e : {FT.fit(a) == FT.fit(_) : Maybe<&2, Nat>}
  {==}

# a value that fits is itself, capped
def tmo.some(+y: Nat, hy: {FT.fits(y) == True{} : Bool}) -> {Some{y} == FT.fit(y) : Maybe<&2, Nat>}:
  %Equal.sym(Bool, FT.fits(y), True{}, hy) : {Some{y} == FT.fit.put(_, y) : Maybe<&2, Nat>}
  {==}

# one bit of the product: twice q y, plus y for a bit 1, is x1 y
def tmo.bit(r: Nat, +q: Nat, -x1: Nat, +y: Nat, hr: {Nat.is_le(r, 1n) == True{} : Bool}, ex: {Nat.add(Nat.mul(q, 2n), r) == x1 : Nat}, hy: {FT.fits(y) == True{} : Bool}) -> {FT.times.bit(r, FT.fit(Nat.mul(q, y)), y) == FT.fit(Nat.mul(x1, y)) : Maybe<&2, Nat>}:
  match r:
    case 0n:
      +qy = Nat.mul(q, y)
      %ex : {FT.times.bit(0n, FT.fit(qy), y) == FT.fit(Nat.mul(_, y)) : Maybe<&2, Nat>}
      %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(q, 2n), 0n), y), Nat.add(Nat.add(qy, qy), Nat.mul(0n, y)), tmo.arith(q, 0n, y)) : {FT.times.bit(0n, FT.fit(qy), y) == FT.fit(_) : Maybe<&2, Nat>}
      %Equal.sym(Nat, Nat.add(Nat.add(qy, qy), 0n), Nat.add(qy, qy), CN.ac.add_zero(Nat.add(qy, qy))) : {FT.plus(FT.fit(qy), FT.fit(qy)) == FT.fit(_) : Maybe<&2, Nat>}
      tmo.plus(qy, qy)
    case 1n+rp:
      match rp:
        case 0n:
          +qy = Nat.mul(q, y)
          %ex : {FT.times.bit(1n, FT.fit(qy), y) == FT.fit(Nat.mul(_, y)) : Maybe<&2, Nat>}
          %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(q, 2n), 1n), y), Nat.add(Nat.add(qy, qy), Nat.mul(1n, y)), tmo.arith(q, 1n, y)) : {FT.times.bit(1n, FT.fit(qy), y) == FT.fit(_) : Maybe<&2, Nat>}
          %Equal.sym(Nat, Nat.add(y, 0n), y, CN.ac.add_zero(y)) : {FT.plus(FT.plus(FT.fit(qy), FT.fit(qy)), Some{y}) == FT.fit(Nat.add(Nat.add(qy, qy), _)) : Maybe<&2, Nat>}
          tmo.pc(FT.plus(FT.fit(qy), FT.fit(qy)), Some{y}, Nat.add(qy, qy), y, tmo.plus(qy, qy), tmo.some(y, hy))
        case 1n+rq:
          CN.ac.ft({FT.times.bit(2n+rq, FT.fit(Nat.mul(q, y)), y) == FT.fit(Nat.mul(x1, y)) : Maybe<&2, Nat>}, hr)

# the product of x and a y that fits, with enough fuel
def tmo.times_go(f: Nat, x: Nat, +y: Nat, hx: {Nat.is_le(x, f) == True{} : Bool}, +hy: {FT.fits(y) == True{} : Bool}) -> {FT.times.go(f, x, y) == FT.fit(Nat.mul(x, y)) : Maybe<&2, Nat>}:
  match f:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n+p:
          CN.ac.ft({FT.times.go(0n, 1n+p, y) == FT.fit(Nat.mul(1n+p, y)) : Maybe<&2, Nat>}, hx)
    case 1n++g:
      match x:
        case 0n:
          {==}
        case 1n++p:
          +x1 = {1n+p : Nat}
          +q = Nat.div(x1, 2n)
          +hq = PWU.wu_le_trans(q, p, g, tmo.div2_lt(p), hx)
          %Equal.sym(Maybe<&2, Nat>, FT.times.go(g, q, y), FT.fit(Nat.mul(q, y)), tmo.times_go(g, q, y, hq, hy)) : {FT.times.bit(Nat.mod(x1, 2n), _, y) == FT.fit(Nat.mul(x1, y)) : Maybe<&2, Nat>}
          tmo.bit(Nat.mod(x1, 2n), q, x1, y, CN.ac.mod_le(x1, 1n), CN.ac.div_eq(x1, 1n), hy)

def tmo.times.at(b: Bool, +k: Nat, +y: Nat, eb: {FT.fits(y) == b : Bool}) -> {FT.times(1n+k, FT.fit.put(b, y)) == FT.fit(Nat.mul(1n+k, y)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      tmo.times_go(1n+k, 1n+k, y, PWU.wu_le_refl(k), eb)
    case False{}:
      %Equal.sym(Bool, FT.fits(Nat.mul(1n+k, y)), False{}, tmo.fits_mono(y, Nat.mul(1n+k, y), tmo.le_add_l(y, Nat.mul(k, y)), eb)) : {None{} == FT.fit.put(_, Nat.mul(1n+k, y)) : Maybe<&2, Nat>}
      {==}

# the capped product of 1 + k and a capped value
def tmo.times(+k: Nat, -mb: Maybe<&2, Nat>, +b: Nat, eb: {mb == FT.fit(b) : Maybe<&2, Nat>}) -> {FT.times(1n+k, mb) == FT.fit(Nat.mul(1n+k, b)) : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, mb, FT.fit(b), eb) : {FT.times(1n+k, _) == FT.fit(Nat.mul(1n+k, b)) : Maybe<&2, Nat>}
  tmo.times.at(FT.fits(b), k, b, {==})

# The derived values
# ------------------

# each value, capped
def tmo.fitl(xs: List<&2, Nat>) -> List<&2, Maybe<&2, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      FT.fit(x) <> tmo.fitl(t)

def tmo.cons(-x: Maybe<&2, Nat>, -y: Maybe<&2, Nat>, -xs: List<&2, Maybe<&2, Nat>>, -ys: List<&2, Maybe<&2, Nat>>, ex: {x == y : Maybe<&2, Nat>}, et: {xs == ys : List<&2, Maybe<&2, Nat>>}) -> {x <> xs == y <> ys : List<&2, Maybe<&2, Nat>>}:
  %ex : {x <> xs == _ <> ys : List<&2, Maybe<&2, Nat>>}
  %et : {x <> xs == x <> _ : List<&2, Maybe<&2, Nat>>}
  {==}

# the base values' capped sums, by name
def tc.F(+n: Nat) -> Maybe<&2, Nat>:
  FT.fit(n)

def tc.ks(+k: Nat) -> Maybe<&2, Nat>:
  FT.plus(FT.fit(k), FT.plus(FT.fit(k), FT.plus(FT.fit(k), FT.fit(0n))))

# the entry's capped values are the laws' values, capped
def tmo.derived(t: Su.Tm) -> {FT.derived(t) == tmo.fitl(Timeouts.tw_values(t)) : List<&2, Maybe<&2, Nat>>}:
  match t:
    case Su.Tm{+snap, +host, +kstep, +kterm, +kverify, +harness, +wterm, +wverify, +margin, +refresh, +boot, +relaunch, +startup, +check, +slack, +k, +bmax, +loop, +qanswer}:
      +K = FT.fit(kstep)
      +k1 = tmo.plus(kstep, 0n)
      +k2 = tmo.pc(K, FT.plus(K, FT.fit(0n)), kstep, Nat.add(kstep, 0n), {==}, k1)
      +k3 = tmo.pc(K, FT.plus(K, FT.plus(K, FT.fit(0n))), kstep, Nat.add(kstep, Nat.add(kstep, 0n)), {==}, k2)
      +SH = FT.plus(FT.fit(snap), FT.fit(host))
      +a1 = tmo.plus(snap, host)
      +K3 = FT.plus(K, FT.plus(K, FT.plus(K, FT.fit(0n))))
      +a2 = tmo.pc(SH, K3, Nat.add(snap, host), Nat.mul(3n, kstep), a1, k3)
      +A2 = FT.plus(SH, K3)
      +a3 = tmo.pc(A2, FT.fit(kterm), Nat.add(Nat.add(snap, host), Nat.mul(3n, kstep)), kterm, a2, {==})
      +A3 = FT.plus(A2, FT.fit(kterm))
      +td = Nat.add(Nat.add(Nat.add(Nat.add(snap, host), Nat.mul(3n, kstep)), kterm), kverify)
      +TD = FT.plus(A3, FT.fit(kverify))
      +etd = tmo.pc(A3, FT.fit(kverify), Nat.add(Nat.add(Nat.add(snap, host), Nat.mul(3n, kstep)), kterm), kverify, a3, {==})
      +sg = Nat.add(td, harness)
      +SG = FT.plus(TD, FT.fit(harness))
      +esg = tmo.pc(TD, FT.fit(harness), td, harness, etd, {==})
      +DR1 = FT.plus(SG, FT.fit(wterm))
      +edr1 = tmo.pc(SG, FT.fit(wterm), sg, wterm, esg, {==})
      +dr = Nat.add(Nat.add(sg, wterm), wverify)
      +DR = FT.plus(DR1, FT.fit(wverify))
      +edr = tmo.pc(DR1, FT.fit(wverify), Nat.add(sg, wterm), wverify, edr1, {==})
      +elw = tmo.pc(DR, FT.fit(margin), dr, margin, edr, {==})
      +eck1 = tmo.pc(SG, DR, sg, dr, esg, edr)
      +eck = tmo.pc(FT.plus(SG, DR), FT.fit(margin), Nat.add(sg, dr), margin, eck1, {==})
      +el1 = tmo.plus(relaunch, startup)
      +el2 = tmo.pc(FT.plus(FT.fit(relaunch), FT.fit(startup)), FT.fit(check), Nat.add(relaunch, startup), check, el1, {==})
      +el3 = tmo.pc(FT.plus(FT.plus(FT.fit(relaunch), FT.fit(startup)), FT.fit(check)), FT.fit(slack), Nat.add(Nat.add(relaunch, startup), check), slack, el2, {==})
      +emx = tmo.plus(refresh, boot)
      +eqh = tmo.pc(FT.fit(qanswer), SG, qanswer, sg, {==}, esg)
      +ewn = tmo.times(k, FT.plus(FT.fit(bmax), FT.fit(loop)), Nat.add(bmax, loop), tmo.plus(bmax, loop))
      +L9 = {[FT.times(1n+k, FT.plus(FT.fit(bmax), FT.fit(loop)))] : List<&2, Maybe<&2, Nat>>}
      +R9 = {[FT.fit(Nat.mul(1n+k, Nat.add(bmax, loop)))] : List<&2, Maybe<&2, Nat>>}
      +e9 = tmo.cons(FT.times(1n+k, FT.plus(FT.fit(bmax), FT.fit(loop))), FT.fit(Nat.mul(1n+k, Nat.add(bmax, loop))), Nil{}, Nil{}, ewn, {==})
      +L8 = {FT.plus(FT.fit(qanswer), SG) <> L9 : List<&2, Maybe<&2, Nat>>}
      +R8 = {FT.fit(Nat.add(qanswer, sg)) <> R9 : List<&2, Maybe<&2, Nat>>}
      +e8 = tmo.cons(FT.plus(FT.fit(qanswer), SG), FT.fit(Nat.add(qanswer, sg)), L9, R9, eqh, e9)
      +L7 = {FT.plus(FT.fit(refresh), FT.fit(boot)) <> L8 : List<&2, Maybe<&2, Nat>>}
      +R7 = {FT.fit(Nat.add(refresh, boot)) <> R8 : List<&2, Maybe<&2, Nat>>}
      +e7 = tmo.cons(FT.plus(FT.fit(refresh), FT.fit(boot)), FT.fit(Nat.add(refresh, boot)), L8, R8, emx, e8)
      +LO = FT.plus(FT.plus(FT.plus(FT.fit(relaunch), FT.fit(startup)), FT.fit(check)), FT.fit(slack))
      +L6 = {LO <> L7 : List<&2, Maybe<&2, Nat>>}
      +R6 = {FT.fit(Nat.add(Nat.add(Nat.add(relaunch, startup), check), slack)) <> R7 : List<&2, Maybe<&2, Nat>>}
      +e6 = tmo.cons(LO, FT.fit(Nat.add(Nat.add(Nat.add(relaunch, startup), check), slack)), L7, R7, el3, e7)
      +L5 = {FT.plus(FT.plus(SG, DR), FT.fit(margin)) <> L6 : List<&2, Maybe<&2, Nat>>}
      +R5 = {FT.fit(Nat.add(Nat.add(sg, dr), margin)) <> R6 : List<&2, Maybe<&2, Nat>>}
      +e5 = tmo.cons(FT.plus(FT.plus(SG, DR), FT.fit(margin)), FT.fit(Nat.add(Nat.add(sg, dr), margin)), L6, R6, eck, e6)
      +L4 = {FT.plus(DR, FT.fit(margin)) <> L5 : List<&2, Maybe<&2, Nat>>}
      +R4 = {FT.fit(Nat.add(dr, margin)) <> R5 : List<&2, Maybe<&2, Nat>>}
      +e4 = tmo.cons(FT.plus(DR, FT.fit(margin)), FT.fit(Nat.add(dr, margin)), L5, R5, elw, e5)
      +L3 = {DR <> L4 : List<&2, Maybe<&2, Nat>>}
      +R3 = {FT.fit(dr) <> R4 : List<&2, Maybe<&2, Nat>>}
      +e3 = tmo.cons(DR, FT.fit(dr), L4, R4, edr, e4)
      +L2 = {SG <> L3 : List<&2, Maybe<&2, Nat>>}
      +R2 = {FT.fit(sg) <> R3 : List<&2, Maybe<&2, Nat>>}
      +e2 = tmo.cons(SG, FT.fit(sg), L3, R3, esg, e3)
      tmo.cons(TD, FT.fit(td), L2, R2, etd, e2)

# Every value, or none
# --------------------

def tmo.sel(b: Bool, xs: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  match b:
    case True{}:
      Some{xs}
    case False{}:
      None{}

def tmo.cons_sel(c: Bool, +v: Nat, t: List<&2, Nat>) -> {FT.every.cons(v, tmo.sel(c, t)) == tmo.sel(c, v <> t) : Maybe<&2, List<&2, Nat>>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def tmo.every.at(b: Bool, +v: Nat, +t: List<&2, Nat>, ih: {FT.every(tmo.fitl(t)) == tmo.sel(Timeouts.tw_all_below(t), t) : Maybe<&2, List<&2, Nat>>}) -> {FT.every(FT.fit.put(b, v) <> tmo.fitl(t)) == tmo.sel(Bool.and(b, Timeouts.tw_all_below(t)), v <> t) : Maybe<&2, List<&2, Nat>>}:
  match b:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Maybe<&2, List<&2, Nat>>, FT.every(tmo.fitl(t)), tmo.sel(Timeouts.tw_all_below(t), t), ih) : {FT.every.cons(v, _) == tmo.sel(Timeouts.tw_all_below(t), v <> t) : Maybe<&2, List<&2, Nat>>}
      tmo.cons_sel(Timeouts.tw_all_below(t), v, t)

# the capped values are every value exactly when every value fits
def tmo.every(xs: List<&2, Nat>) -> {FT.every(tmo.fitl(xs)) == tmo.sel(Timeouts.tw_all_below(xs), xs) : Maybe<&2, List<&2, Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case +v <> +t:
      %Equal.sym(Bool, Timeouts.tw_below(v), FT.fits(v), tmo.below(v)) : {FT.every(FT.fit(v) <> tmo.fitl(t)) == tmo.sel(Bool.and(_, Timeouts.tw_all_below(t)), v <> t) : Maybe<&2, List<&2, Nat>>}
      tmo.every.at(FT.fits(v), v, t, tmo.every(t))

def tmo.of(b: Bool, xs: List<&2, Nat>) -> {FT.answer.of(tmo.sel(b, xs)) == Timeouts.tw_reply.put(b, xs) : String}:
  match b:
    case True{}:
      Equal.sym(String, Timeouts.tw_spell_values(xs), FT.put_nats(xs, ""), tmo.spell(xs))
    case False{}:
      {==}

# the entry answers the laws' reply on every base values
def tmo.answer(+t: Su.Tm) -> {FT.answer(t) == Timeouts.tw_reply(t) : String}:
  +xs = Timeouts.tw_values(t)
  %Equal.sym(List<&2, Maybe<&2, Nat>>, FT.derived(t), tmo.fitl(xs), tmo.derived(t)) : {FT.answer.of(FT.every(_)) == Timeouts.tw_reply(t) : String}
  %Equal.sym(Maybe<&2, List<&2, Nat>>, FT.every(tmo.fitl(xs)), tmo.sel(Timeouts.tw_all_below(xs), xs), tmo.every(xs)) : {FT.answer.of(_) == Timeouts.tw_reply(t) : String}
  tmo.of(Timeouts.tw_all_below(xs), xs)
