# PROOF, section wire: the proofs of LAWS.bend section wire
# (bend/wire.bend), moved out of PROOF.bend so the proof/ files of later
# sections can use the Laws.wire_* fills (a proof/ file can use only laws
# filled in files it imports). PROOF.bend imports this file.

import Base
import ../LAWS.bend as Laws
import ../bend/wire.bend as Wr


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

# The value of digits read last first: d0 + 10 * value(rest).
def wo_value(ds: List<&2, Nat>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, t}:
      Nat.add(d, Nat.mul(10n, wo_value(t)))

# No digit is left: only the end mark may follow.
def wo_end(ts: Wr.Tok & String, ds: List<&2, Nat>) -> Wr.Dec<Nat>:
  (t, s) = ts
  match t:
    case Wr.Dig{d}:
      Wr.Bad{}
    case Wr.Comma{}:
      Wr.Got{wo_value(ds), s}
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
          Wr.Got{wo_value(ds), s}
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

# ---- wire nat (wn_): Bool kit (copied from the skill's examples/sort/proof/kit.bend) ----

def wn_Clash(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      G

def wn_absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : wn_Clash(_, G)
  Unit{}

def wn_absurd2(-G: Type, e: {True{} == False{} : Bool}) -> G:
  wn_absurd(G, Equal.sym(Bool, True{}, False{}, e))

def wn_and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      wn_absurd({False{} == True{} : Bool}, e)
    case True{}:
      {==}

def wn_and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      wn_absurd({b == True{} : Bool}, e)
    case True{}:
      e

def wn_and_intro(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool})
  -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# ---- Nat.add (copied from the skill's examples/sort/proof/nat_add.bend) ----

def wn_add_zero_r(m: Nat) -> {Nat.add(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 0n), p, wn_add_zero_r(p))

def wn_add_succ_r(m: Nat, -n: Nat) -> {Nat.add(m, 1n+n) == 1n+Nat.add(m, n) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 1n+n), 1n+Nat.add(p, n), wn_add_succ_r(p, n))

def wn_add_comm(m: Nat, +n: Nat) -> {Nat.add(m, n) == Nat.add(n, m) : Nat}:
  match m:
    case 0n:
      Equal.sym(Nat, Nat.add(n, 0n), n, wn_add_zero_r(n))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(n, 1n+p), 1n+Nat.add(n, p), wn_add_succ_r(n, p)) : {1n+Nat.add(p, n) == _ : Nat}
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, n), Nat.add(n, p), wn_add_comm(p, n))

def wn_add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)),
        wn_add_assoc(p, b, c))

def wn_add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), wn_add_assoc(a, b, c)),
    Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c), Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, k => Nat.add(k, c), Nat.add(a, b), Nat.add(b, a), wn_add_comm(a, b)),
      wn_add_assoc(b, a, c)))

# ---- Nat: zero, mul, order ----

def wn_isz(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

# 1 + n is not 0
def wn_succ_nz(-G: Type, -n: Nat, e: {1n+n == 0n : Nat}) -> G:
  wn_absurd(G, Equal.cong(Nat, Bool, wn_isz, 1n+n, 0n, e))

def wn_pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def wn_add_eq_zero_l(a: Nat, -b: Nat, e: {Nat.add(a, b) == 0n : Nat}) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      wn_succ_nz({1n+p == 0n : Nat}, Nat.add(p, b), e)

def wn_add_eq_zero_r(a: Nat, -b: Nat, e: {Nat.add(a, b) == 0n : Nat}) -> {b == 0n : Nat}:
  match a:
    case 0n:
      e
    case 1n+p:
      wn_succ_nz({b == 0n : Nat}, Nat.add(p, b), e)

def wn_mul_succ_r(+a: Nat, +w: Nat) -> {Nat.mul(a, 1n+w) == Nat.add(a, Nat.mul(a, w)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(p, 1n+w), Nat.add(p, Nat.mul(p, w)), wn_mul_succ_r(p, w)) : {1n+Nat.add(w, _) == 1n+Nat.add(p, Nat.add(w, Nat.mul(p, w))) : Nat}
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(w, Nat.add(p, Nat.mul(p, w))), Nat.add(p, Nat.add(w, Nat.mul(p, w))),
        wn_add_swap(w, p, Nat.mul(p, w)))

def wn_le_step(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      wn_absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      wn_le_step(p, q, h)

def wn_le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+z:
      {==}
    case 0n 1n+y 0n:
      {==}
    case 0n 1n+y 1n+z:
      {==}
    case 1n+x 0n 0n:
      wn_absurd({Nat.is_le(1n+x, 0n) == True{} : Bool}, h1)
    case 1n+x 0n 1n+z:
      wn_absurd({Nat.is_le(1n+x, 1n+z) == True{} : Bool}, h1)
    case 1n+x 1n+y 0n:
      wn_absurd({Nat.is_le(1n+x, 0n) == True{} : Bool}, h2)
    case 1n+x 1n+y 1n+z:
      wn_le_trans(x, y, z, h1, h2)

def wn_le_add(+k: Nat, +a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, Nat.add(k, b)) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n+j:
      wn_le_step(a, Nat.add(j, b), wn_le_add(j, a, b, h))

# a - b, cut at 0
def wn_sub(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n 0n:
      0n
    case 0n 1n+q:
      0n
    case 1n+p 0n:
      1n+p
    case 1n+p 1n+q:
      wn_sub(p, q)

def wn_le_k(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(a, wn_sub(b, a)) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      wn_absurd({Nat.add(1n+p, 0n) == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, wn_sub(q, p)), q, wn_le_k(p, q, h))

def wn_le_zero(p: Nat, h: {Nat.is_le(p, 0n) == True{} : Bool}) -> {p == 0n : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      wn_absurd({1n+q == 0n : Nat}, h)

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

# ---- Nat.divmod by 10 ----

def wn_lt10(d: Nat) -> Bool:
  match d:
    case 0n:
      True{}
    case 1n:
      True{}
    case 2n:
      True{}
    case 3n:
      True{}
    case 4n:
      True{}
    case 5n:
      True{}
    case 6n:
      True{}
    case 7n:
      True{}
    case 8n:
      True{}
    case 9n:
      True{}
    case 10n+p:
      False{}

def wn_dm_fst(n: Nat, +m: Nat, -d: Nat, +r: Nat) ->
  {Pair.fst(Nat, Nat, Nat.divmod.go(n, m, 1n+d, r)) == 1n+Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          wn_dm_fst(np, r, 1n+d, 0n)
        case 1n+mp:
          wn_dm_fst(np, mp, d, 1n+r)

def wn_dm_snd(n: Nat, +m: Nat, -d: Nat, +r: Nat) ->
  {Pair.snd(Nat, Nat, Nat.divmod.go(n, m, 1n+d, r)) == Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          wn_dm_snd(np, r, 1n+d, 0n)
        case 1n+mp:
          wn_dm_snd(np, mp, d, 1n+r)

def wn_div_step(n: Nat) -> {Nat.div(10n+n, 10n) == 1n+Nat.div(n, 10n) : Nat}:
  wn_dm_fst(n, 9n, 0n, 0n)

def wn_mod_step(n: Nat) -> {Nat.mod(10n+n, 10n) == Nat.mod(n, 10n) : Nat}:
  wn_dm_snd(n, 9n, 0n, 0n)

def wn_mod_lt(+n: Nat) -> {wn_lt10(Nat.mod(n, 10n)) == True{} : Bool}:
  match n:
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
      %Equal.sym(Nat, Nat.mod(10n+p, 10n), Nat.mod(p, 10n), wn_mod_step(p)) : {wn_lt10(_) == True{} : Bool}
      wn_mod_lt(p)

# n == n % 10 + 10 * (n / 10)
def wn_dm(+n: Nat) -> {Nat.add(Nat.mod(n, 10n), Nat.mul(10n, Nat.div(n, 10n))) == n : Nat}:
  match n:
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
      %Equal.sym(Nat, Nat.mod(10n+p, 10n), Nat.mod(p, 10n), wn_mod_step(p)) : {Nat.add(_, Nat.mul(10n, Nat.div(10n+p, 10n))) == 10n+p : Nat}
      %Equal.sym(Nat, Nat.div(10n+p, 10n), 1n+Nat.div(p, 10n), wn_div_step(p)) : {Nat.add(Nat.mod(p, 10n), Nat.mul(10n, _)) == 10n+p : Nat}
      %Equal.sym(Nat, Nat.mul(10n, 1n+Nat.div(p, 10n)), Nat.add(10n, Nat.mul(10n, Nat.div(p, 10n))), wn_mul_succ_r(10n, Nat.div(p, 10n))) : {Nat.add(Nat.mod(p, 10n), _) == 10n+p : Nat}
      %Equal.sym(Nat, Nat.add(Nat.mod(p, 10n), Nat.add(10n, Nat.mul(10n, Nat.div(p, 10n)))), Nat.add(10n, Nat.add(Nat.mod(p, 10n), Nat.mul(10n, Nat.div(p, 10n)))), wn_add_swap(Nat.mod(p, 10n), 10n, Nat.mul(10n, Nat.div(p, 10n)))) : {_ == 10n+p : Nat}
      Equal.cong(Nat, Nat, k => 10n+k, Nat.add(Nat.mod(p, 10n), Nat.mul(10n, Nat.div(p, 10n))), p, wn_dm(p))

# (1 + p) / 10 <= p
def wn_div_lt(+p: Nat) -> {Nat.is_le(Nat.div(1n+p, 10n), p) == True{} : Bool}:
  match p:
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
    case 10n+q:
      %Equal.sym(Nat, Nat.div(11n+q, 10n), 1n+Nat.div(1n+q, 10n), wn_div_step(1n+q)) : {Nat.is_le(_, 10n+q) == True{} : Bool}
      wn_le_add(9n, Nat.div(1n+q, 10n), q, wn_div_lt(q))

def wn_div_le(+n: Nat) -> {Nat.is_le(Nat.div(n, 10n), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      wn_le_step(Nat.div(1n+p, 10n), p, wn_div_lt(p))

# n / 10 == 0 gives n % 10 == n
def wn_dm0(+n: Nat, e: {Nat.div(n, 10n) == 0n : Nat}) -> {Nat.mod(n, 10n) == n : Nat}:
  %wn_add_zero_r(Nat.mod(n, 10n)) : {_ == n : Nat}
  %e : {Nat.add(Nat.mod(n, 10n), Nat.mul(10n, _)) == n : Nat}
  wn_dm(n)

def wn_ud0(+d: Nat, h: {wn_lt10(d) == True{} : Bool}) -> {Nat.div(Nat.add(d, Nat.mul(10n, 0n)), 10n) == 0n : Nat}:
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
      wn_absurd({Nat.div(Nat.add(10n+p, Nat.mul(10n, 0n)), 10n) == 0n : Nat}, h)

def wn_um0(+d: Nat, h: {wn_lt10(d) == True{} : Bool}) -> {Nat.mod(Nat.add(d, Nat.mul(10n, 0n)), 10n) == d : Nat}:
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
      wn_absurd({Nat.mod(Nat.add(10n+p, Nat.mul(10n, 0n)), 10n) == 10n+p : Nat}, h)

# a digit d below 10 then v: (d + 10 * v) / 10 == v
def wn_ud(+v: Nat, +d: Nat, h: {wn_lt10(d) == True{} : Bool}) -> {Nat.div(Nat.add(d, Nat.mul(10n, v)), 10n) == v : Nat}:
  match v:
    case 0n:
      wn_ud0(d, h)
    case 1n+w:
      %Equal.sym(Nat, Nat.mul(10n, 1n+w), Nat.add(10n, Nat.mul(10n, w)), wn_mul_succ_r(10n, w)) : {Nat.div(Nat.add(d, _), 10n) == 1n+w : Nat}
      %Equal.sym(Nat, Nat.add(d, Nat.add(10n, Nat.mul(10n, w))), Nat.add(10n, Nat.add(d, Nat.mul(10n, w))), wn_add_swap(d, 10n, Nat.mul(10n, w))) : {Nat.div(_, 10n) == 1n+w : Nat}
      %Equal.sym(Nat, Nat.div(10n+Nat.add(d, Nat.mul(10n, w)), 10n), 1n+Nat.div(Nat.add(d, Nat.mul(10n, w)), 10n), wn_div_step(Nat.add(d, Nat.mul(10n, w)))) : {_ == 1n+w : Nat}
      Equal.cong(Nat, Nat, k => 1n+k, Nat.div(Nat.add(d, Nat.mul(10n, w)), 10n), w, wn_ud(w, d, h))

# a digit d below 10 then v: (d + 10 * v) % 10 == d
def wn_um(+v: Nat, +d: Nat, h: {wn_lt10(d) == True{} : Bool}) -> {Nat.mod(Nat.add(d, Nat.mul(10n, v)), 10n) == d : Nat}:
  match v:
    case 0n:
      wn_um0(d, h)
    case 1n+w:
      %Equal.sym(Nat, Nat.mul(10n, 1n+w), Nat.add(10n, Nat.mul(10n, w)), wn_mul_succ_r(10n, w)) : {Nat.mod(Nat.add(d, _), 10n) == d : Nat}
      %Equal.sym(Nat, Nat.add(d, Nat.add(10n, Nat.mul(10n, w))), Nat.add(10n, Nat.add(d, Nat.mul(10n, w))), wn_add_swap(d, 10n, Nat.mul(10n, w))) : {Nat.mod(_, 10n) == d : Nat}
      %Equal.sym(Nat, Nat.mod(10n+Nat.add(d, Nat.mul(10n, w)), 10n), Nat.mod(Nat.add(d, Nat.mul(10n, w)), 10n), wn_mod_step(Nat.add(d, Nat.mul(10n, w)))) : {_ == d : Nat}
      wn_um(w, d, h)

# ---- U32.is_eq is sound (copied, renamed, from the skill's examples/sort/proof/u32_order.bend: eq_sound, Word.cmp_eq) ----

def wn_lt_eq(-G: Type, e: {LT{} == EQ{} : Cmp}) -> G:
  wn_absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), LT{}, EQ{}, e))

def wn_gt_eq(-G: Type, e: {GT{} == EQ{} : Cmp}) -> G:
  wn_absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), GT{}, EQ{}, e))

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
      wn_absurd({a == b : U32}, e)
    case EQ{}:
      wn_u32_cmp_eq(a, b, et)
    case GT{}:
      wn_absurd({a == b : U32}, e)

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
          wn_absurd({False{} == True{} : Bool} & {d2 == d : Nat}, Equal.cong(Wr.Tok, Bool, wn_tok_isdig, Wr.Comma{}, Wr.Dig{d}, e))
        case False{}:
          wn_absurd({False{} == True{} : Bool} & {d2 == d : Nat}, Equal.cong(Wr.Tok, Bool, wn_tok_isdig, Wr.Other{}, Wr.Dig{d}, e))

# tok.is answered Comma{}: the char was ','
def wn_tokis_comma(ok: Bool, d2: Nat, comma: Bool, e: {Wr.tok.is(ok, d2, comma) == Wr.Comma{} : Wr.Tok})
  -> {comma == True{} : Bool}:
  match ok:
    case True{}:
      wn_absurd({comma == True{} : Bool}, Equal.cong(Wr.Tok, Bool, wn_tok_iscomma, Wr.Dig{d2}, Wr.Comma{}, e))
    case False{}:
      match comma:
        case True{}:
          {==}
        case False{}:
          wn_absurd({False{} == True{} : Bool}, Equal.cong(Wr.Tok, Bool, wn_tok_iscomma, Wr.Other{}, Wr.Comma{}, e))

# a d below 10 is a digit, and the code 48 + d is the code of its char
def wn_code(d: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool})
  -> {Chr{U32.from_nat(Nat.add(48n, d))} == Wr.dchar(d) : Char} & {wn_lt10(d) == True{} : Bool}:
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
          wn_absurd({Chr{U32.from_nat(Nat.add(48n, 10n))} == Wr.dchar(10n) : Char} & {wn_lt10(10n) == True{} : Bool}, h)
        case 1n+q:
          wn_absurd({Chr{U32.from_nat(Nat.add(48n, 11n+q))} == Wr.dchar(11n+q) : Char} & {wn_lt10(11n+q) == True{} : Bool}, h)

# tok.code(x, d2) == Dig{d}: the char of code x is the digit d, below 10
def wn_tdi(+x: U32, +d2: Nat, -d: Nat, +e: {Wr.tok.code(x, d2) == Wr.Dig{d} : Wr.Tok})
  -> {Chr{x} == Wr.dchar(d) : Char} & {wn_lt10(d) == True{} : Bool}:
  +ok = Pair.fst({Bool.and(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2)))) == True{} : Bool}, {d2 == d : Nat},
    wn_tokis_dig(Bool.and(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2)))), d2, U32.is_eq(x, 44), d, e))
  +dd = Pair.snd({Bool.and(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2)))) == True{} : Bool}, {d2 == d : Nat},
    wn_tokis_dig(Bool.and(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2)))), d2, U32.is_eq(x, 44), d, e))
  +lt = wn_and_l(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2))), ok)
  +ex = wn_eq_sound(x, U32.from_nat(Nat.add(48n, d2)), wn_and_r(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2))), ok))
  %dd : {Chr{x} == Wr.dchar(_) : Char} & {wn_lt10(_) == True{} : Bool}
  %Equal.sym(U32, x, U32.from_nat(Nat.add(48n, d2)), ex) : {Chr{_} == Wr.dchar(d2) : Char} & {wn_lt10(d2) == True{} : Bool}
  wn_code(d2, lt)

def wn_tok_dig_inv(c: Char, -d: Nat, e: {Wr.tok(c) == Wr.Dig{d} : Wr.Tok}) -> {c == Wr.dchar(d) : Char} & {wn_lt10(d) == True{} : Bool}:
  match c:
    case Chr{+x}:
      wn_tdi(x, Nat.sub(U32.to_nat(x), 48n), d, e)

# tok(c) == Dig{d}: c is the char of d
def wn_tdi_c(+c: Char, -d: Nat, e: {Wr.tok(c) == Wr.Dig{d} : Wr.Tok}) -> {c == Wr.dchar(d) : Char}:
  Pair.fst({c == Wr.dchar(d) : Char}, {wn_lt10(d) == True{} : Bool}, wn_tok_dig_inv(c, d, e))

# tok(c) == Dig{d}: d is below 10
def wn_tdi_lt(+c: Char, -d: Nat, e: {Wr.tok(c) == Wr.Dig{d} : Wr.Tok}) -> {wn_lt10(d) == True{} : Bool}:
  Pair.snd({c == Wr.dchar(d) : Char}, {wn_lt10(d) == True{} : Bool}, wn_tok_dig_inv(c, d, e))

# tok(c) == Comma{}: c is ','
def wn_tok_comma_inv(c: Char, e: {Wr.tok(c) == Wr.Comma{} : Wr.Tok}) -> {c == ',' : Char}:
  match c:
    case Chr{+x}:
      +d2 = Nat.sub(U32.to_nat(x), 48n)
      Equal.cong(U32, Char, y => Chr{y}, x, 44, wn_eq_sound(x, 44,
        wn_tokis_comma(Bool.and(Nat.is_lt(d2, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d2)))), d2, U32.is_eq(x, 44), e)))

# a digit below 10 reads back as itself
def wn_tok_dig(+d: Nat, h: {wn_lt10(d) == True{} : Bool}) -> {Wr.tok(Wr.dchar(d)) == Wr.Dig{d} : Wr.Tok}:
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
      wn_absurd({Wr.tok(Wr.dchar(10n+p)) == Wr.Dig{10n+p} : Wr.Tok}, h)

# no digit char is 'E'
def wn_dchar_ne(d: Nat) -> {Char.is_eq(Wr.dchar(d), 'E') == False{} : Bool}:
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
      {==}

# ---- the digits of a Nat, lowest first ----

# the chars of ds (lowest digit first) before acc: the highest digit leads
def wn_emit(ds: List<&2, Nat>, acc: String) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{d, t}:
      wn_emit(t, SCon{Wr.dchar(d), acc})

# the digits of q, lowest first, under the fuel g (put_nat.go's recursion)
def wn_L(g: Nat, q: Nat) -> List<&2, Nat>:
  match g:
    case 0n:
      Nil{}
    case 1n+f:
      match q:
        case 0n:
          Nil{}
        case 1n+p:
          +m = {1n+p : Nat}
          Nat.mod(m, 10n) <> wn_L(f, Nat.div(m, 10n))

# all the digits of n, lowest first
def wn_full(n: Nat) -> List<&2, Nat>:
  +m = n
  Nat.mod(m, 10n) <> wn_L(m, Nat.div(m, 10n))

def wn_nz10(d: Nat) -> Bool:
  match d:
    case 0n:
      False{}
    case 1n+p:
      wn_lt10(1n+p)

# d <> t is a canonical digit list: digits below 10, the last (highest) not 0
def wn_okc(t: List<&2, Nat>, d: Nat) -> Bool:
  match t:
    case Nil{}:
      wn_nz10(d)
    case Con{e, u}:
      Bool.and(wn_lt10(d), wn_okc(u, e))

def wn_canon(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      wn_okc(t, d)

def wn_pe(g: Nat, +q: Nat, acc: String) -> {Wr.put_nat.go(g, q, acc) == wn_emit(wn_L(g, q), acc) : String}:
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
def wn_put_emit(+n: Nat, rest: String) -> {Wr.put_nat(n, rest) == wn_emit(wn_full(n), SCon{',', rest}) : String}:
  wn_pe(n, Nat.div(n, 10n), SCon{Wr.dchar(Nat.mod(n, 10n)), SCon{',', rest}})

def wn_Lzero(g: Nat) -> {wn_L(g, 0n) == Nil{} : List<&2, Nat>}:
  match g:
    case 0n:
      {==}
    case 1n+f:
      {==}

def wn_lenL(g: Nat, +q: Nat) -> {List.length(&2, Nat, wn_L(g, q)) == Laws.wire_digits.go(g, q) : Nat}:
  match g:
    case 0n:
      {==}
    case 1n+f:
      match q:
        case 0n:
          {==}
        case 1n+p:
          Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Nat, wn_L(f, Nat.div(1n+p, 10n))),
            Laws.wire_digits.go(f, Nat.div(1n+p, 10n)), wn_lenL(f, Nat.div(1n+p, 10n)))

# wire_digits(n) counts the digits of n
def wn_wl(+n: Nat) -> {Laws.wire_digits(n) == List.length(&2, Nat, wn_full(n)) : Nat}:
  Equal.cong(Nat, Nat, k => 1n+k, Laws.wire_digits.go(n, Nat.div(n, 10n)), List.length(&2, Nat, wn_L(n, Nat.div(n, 10n))),
    Equal.sym(Nat, List.length(&2, Nat, wn_L(n, Nat.div(n, 10n))), Laws.wire_digits.go(n, Nat.div(n, 10n)), wn_lenL(n, Nat.div(n, 10n))))

def wn_vl(+g: Nat, +q: Nat, h: {Nat.is_le(q, g) == True{} : Bool}) -> {wo_value(wn_L(g, q)) == q : Nat}:
  match g q:
    case 0n 0n:
      {==}
    case 0n 1n+p:
      wn_absurd({wo_value(wn_L(0n, 1n+p)) == 1n+p : Nat}, h)
    case 1n+f 0n:
      {==}
    case 1n+f 1n+p:
      %Equal.sym(Nat, wo_value(wn_L(f, Nat.div(1n+p, 10n))), Nat.div(1n+p, 10n), wn_vl(f, Nat.div(1n+p, 10n), wn_le_trans(Nat.div(1n+p, 10n), p, f, wn_div_lt(p), h))) : {Nat.add(Nat.mod(1n+p, 10n), Nat.mul(10n, _)) == 1n+p : Nat}
      wn_dm(1n+p)

# the digits of n are worth n
def wn_vf(+n: Nat) -> {wo_value(wn_full(n)) == n : Nat}:
  %Equal.sym(Nat, wo_value(wn_L(n, Nat.div(n, 10n))), Nat.div(n, 10n), wn_vl(n, Nat.div(n, 10n), wn_div_le(n))) : {Nat.add(Nat.mod(n, 10n), Nat.mul(10n, _)) == n : Nat}
  wn_dm(n)

def wn_nz_lt(+d: Nat, c: {wn_nz10(d) == True{} : Bool}) -> {wn_lt10(d) == True{} : Bool}:
  match d:
    case 0n:
      wn_absurd({wn_lt10(0n) == True{} : Bool}, c)
    case 1n+p:
      c

def wn_okc_lt(t: List<&2, Nat>, +d: Nat, c: {wn_okc(t, d) == True{} : Bool}) -> {wn_lt10(d) == True{} : Bool}:
  match t:
    case Nil{}:
      wn_nz_lt(d, c)
    case Con{e, u}:
      wn_and_l(wn_lt10(d), wn_okc(u, e), c)

def wn_okh(r: Nat, f: Nat, +q: Nat, er: {Nat.div(1n+q, 10n) == r : Nat}, hf: {Nat.is_le(r, f) == True{} : Bool},
  rec: @q2: Nat -> @d2: Nat -> {wn_lt10(d2) == True{} : Bool} -> {Nat.is_le(1n+q2, f) == True{} : Bool}
    -> {wn_okc(wn_L(f, 1n+q2), d2) == True{} : Bool})
  -> {wn_okc(wn_L(f, r), Nat.mod(1n+q, 10n)) == True{} : Bool}:
  match r:
    case 0n:
      +em = wn_dm0(1n+q, er)
      %Equal.sym(List<&2, Nat>, wn_L(f, 0n), Nil{}, wn_Lzero(f)) : {wn_okc(_, Nat.mod(1n+q, 10n)) == True{} : Bool}
      %Equal.sym(Nat, Nat.mod(1n+q, 10n), 1n+q, em) : {wn_nz10(_) == True{} : Bool}
      %em : {wn_lt10(_) == True{} : Bool}
      wn_mod_lt(1n+q)
    case 1n+r2:
      rec(r2, Nat.mod(1n+q, 10n), wn_mod_lt(1n+q), hf)

def wn_okL(+g: Nat) -> @q: Nat -> @d: Nat -> {wn_lt10(d) == True{} : Bool} -> {Nat.is_le(1n+q, g) == True{} : Bool}
  -> {wn_okc(wn_L(g, 1n+q), d) == True{} : Bool}:
  match g:
    case 0n:
      q => d => hd => hg => wn_absurd({wn_okc(wn_L(0n, 1n+q), d) == True{} : Bool}, hg)
    case 1n+f:
      +q => d => hd => hg =>
        wn_and_intro(wn_lt10(d), wn_okc(wn_L(f, Nat.div(1n+q, 10n)), Nat.mod(1n+q, 10n)), hd,
          wn_okh(Nat.div(1n+q, 10n), f, q, {==}, wn_le_trans(Nat.div(1n+q, 10n), q, f, wn_div_lt(q), hg), wn_okL(f)))

# the digits of a positive n are canonical
def wn_cf(+p: Nat) -> {wn_canon(wn_full(1n+p)) == True{} : Bool}:
  wn_okh(Nat.div(1n+p, 10n), 1n+p, p, {==}, wn_div_le(1n+p), wn_okL(1n+p))

# a canonical list is not worth 0
def wn_vp(u: List<&2, Nat>, +e: Nat, -G: Type, cu: {wn_okc(u, e) == True{} : Bool}, eq: {wo_value(e <> u) == 0n : Nat}) -> G:
  match u:
    case Nil{}:
      wn_absurd(G, Equal.trans(Bool, False{}, wn_nz10(e), True{},
        Equal.sym(Bool, wn_nz10(e), False{}, Equal.cong(Nat, Bool, wn_nz10, e, 0n, wn_add_eq_zero_l(e, Nat.mul(10n, 0n), eq))), cu))
    case Con{+e2, +u2}:
      wn_vp(u2, e2, G, wn_and_r(wn_lt10(e), wn_okc(u2, e2), cu),
        wn_add_eq_zero_l(wo_value(e2 <> u2), Nat.mul(9n, wo_value(e2 <> u2)),
          wn_add_eq_zero_r(e, Nat.mul(10n, wo_value(e2 <> u2)), eq)))

def wn_lth(+q: Nat, +g: Nat, +e: Nat, +u: List<&2, Nat>, +eq: {wo_value(e <> u) == q : Nat}, +cu: {wn_okc(u, e) == True{} : Bool},
  h: {Nat.is_le(q, g) == True{} : Bool},
  rec: @d2: Nat -> @g2: Nat -> {wn_okc(u, d2) == True{} : Bool} -> {Nat.is_le(wo_value(u), g2) == True{} : Bool}
    -> {wn_L(g2, wo_value(u)) == u : List<&2, Nat>})
  -> {wn_L(g, q) == e <> u : List<&2, Nat>}:
  match q g:
    case 0n 0n:
      wn_vp(u, e, {wn_L(0n, 0n) == e <> u : List<&2, Nat>}, cu, eq)
    case 0n 1n+f:
      wn_vp(u, e, {wn_L(1n+f, 0n) == e <> u : List<&2, Nat>}, cu, eq)
    case 1n+p 0n:
      wn_absurd({wn_L(0n, 1n+p) == e <> u : List<&2, Nat>}, h)
    case 1n+p 1n+f:
      +he = wn_okc_lt(u, e, cu)
      +ed = Equal.trans(Nat, Nat.div(1n+p, 10n), Nat.div(wo_value(e <> u), 10n), wo_value(u),
        Equal.cong(Nat, Nat, x => Nat.div(x, 10n), 1n+p, wo_value(e <> u), Equal.sym(Nat, wo_value(e <> u), 1n+p, eq)),
        wn_ud(wo_value(u), e, he))
      +em = Equal.trans(Nat, Nat.mod(1n+p, 10n), Nat.mod(wo_value(e <> u), 10n), e,
        Equal.cong(Nat, Nat, x => Nat.mod(x, 10n), 1n+p, wo_value(e <> u), Equal.sym(Nat, wo_value(e <> u), 1n+p, eq)),
        wn_um(wo_value(u), e, he))
      +fuel = Equal.trans(Bool, Nat.is_le(wo_value(u), f), Nat.is_le(Nat.div(1n+p, 10n), f), True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, f), wo_value(u), Nat.div(1n+p, 10n), Equal.sym(Nat, Nat.div(1n+p, 10n), wo_value(u), ed)),
        wn_le_trans(Nat.div(1n+p, 10n), p, f, wn_div_lt(p), h))
      %Equal.sym(Nat, Nat.mod(1n+p, 10n), e, em) : {_ <> wn_L(f, Nat.div(1n+p, 10n)) == e <> u : List<&2, Nat>}
      %Equal.sym(Nat, Nat.div(1n+p, 10n), wo_value(u), ed) : {e <> wn_L(f, _) == e <> u : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, wn_L(f, wo_value(u)), u, rec(e, f, cu, fuel)) : {e <> _ == e <> u : List<&2, Nat>}
      {==}

def wn_lt(t: List<&2, Nat>) -> @d: Nat -> @g: Nat -> {wn_okc(t, d) == True{} : Bool} -> {Nat.is_le(wo_value(t), g) == True{} : Bool}
  -> {wn_L(g, wo_value(t)) == t : List<&2, Nat>}:
  match t:
    case Nil{}:
      d => g => c => h => wn_Lzero(g)
    case Con{+e, +u}:
      d => g => c => h =>
        wn_lth(wo_value(e <> u), g, e, u, {==}, wn_and_r(wn_lt10(d), wn_okc(u, e), c), h, wn_lt(u))

# the digits of the value of a canonical list are that list
def wn_lv(+t: List<&2, Nat>, +d: Nat, +c: {wn_okc(t, d) == True{} : Bool}) -> {wn_full(wo_value(d <> t)) == d <> t : List<&2, Nat>}:
  +he = wn_okc_lt(t, d, c)
  +ed = wn_ud(wo_value(t), d, he)
  +fuel = Equal.trans(Bool, Nat.is_le(wo_value(t), wo_value(d <> t)), Nat.is_le(Nat.div(wo_value(d <> t), 10n), wo_value(d <> t)), True{},
    Equal.cong(Nat, Bool, x => Nat.is_le(x, wo_value(d <> t)), wo_value(t), Nat.div(wo_value(d <> t), 10n),
      Equal.sym(Nat, Nat.div(wo_value(d <> t), 10n), wo_value(t), ed)),
    wn_div_le(wo_value(d <> t)))
  %Equal.sym(Nat, Nat.mod(wo_value(d <> t), 10n), d, wn_um(wo_value(t), d, he)) : {_ <> wn_L(wo_value(d <> t), Nat.div(wo_value(d <> t), 10n)) == d <> t : List<&2, Nat>}
  %Equal.sym(Nat, Nat.div(wo_value(d <> t), 10n), wo_value(t), ed) : {d <> wn_L(wo_value(d <> t), _) == d <> t : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, wn_L(wo_value(d <> t), wo_value(t)), t, wn_lt(t)(d, wo_value(d <> t), c, fuel)) : {d <> _ == d <> t : List<&2, Nat>}
  {==}

# put_nat of the value of a canonical list writes that list
def wn_E(+t: List<&2, Nat>, +d: Nat, y: String, c: {wn_okc(t, d) == True{} : Bool})
  -> {Wr.put_nat(wo_value(d <> t), y) == wn_emit(d <> t, SCon{',', y}) : String}:
  %wn_lv(t, d, c) : {Wr.put_nat(wo_value(d <> t), y) == wn_emit(_, SCon{',', y}) : String}
  wn_put_emit(wo_value(d <> t), y)

# ---- the decoder ----

def wn_isgot(r: Wr.Dec<Nat>) -> Bool:
  match r:
    case Wr.Got{v, s}:
      True{}
    case Wr.Bad{}:
      False{}

def wn_bad_got(-G: Type, -n: Nat, -s: String, e: {Wr.Bad{} == Wr.Got{n, s} : Wr.Dec<Nat>}) -> G:
  wn_absurd(G, Equal.cong(Wr.Dec<Nat>, Bool, wn_isgot, Wr.Bad{}, Wr.Got{n, s}, e))

# the encoding a decoder answer stands for
def wn_put_dec(r: Wr.Dec<Nat>) -> String:
  match r:
    case Wr.Got{v, s}:
      Wr.put_nat(v, s)
    case Wr.Bad{}:
      SNil{}

def wn_gc(k: Nat, ds: List<&2, Nat>, s: String) -> {wo_go(k, (Wr.Comma{}, s), ds) == Wr.Got{wo_value(ds), s} : Wr.Dec<Nat>}:
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
def wn_eq_end(t: Wr.Tok, s: String, -v: Nat, -ds: List<&2, Nat>, e: {v == wo_value(ds) : Nat})
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
def wn_eq_go(k: Nat, t: Wr.Tok, s: String, +v: Nat, +ds: List<&2, Nat>, e: {v == wo_value(ds) : Nat})
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
                Equal.cong(Nat, Nat, x => Nat.add(d, Nat.mul(10n, x)), v, wo_value(ds), e))
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
      wn_eq_go(13n, t, s, 1n+p, [1n+p], Equal.sym(Nat, Nat.add(1n+p, 0n), 1n+p, wn_add_zero_r(1n+p)))

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

def wn_f1_one(+d: Nat, x: String, +k: Nat, c: {wn_nz10(d) == True{} : Bool}, e: {1n+k == 14n : Nat})
  -> {wo_first(wo_peek(wn_emit([d], x))) == wo_go(k, wo_peek(x), [d]) : Wr.Dec<Nat>}:
  match d:
    case 0n:
      wn_absurd({wo_first(wo_peek(wn_emit([0n], x))) == wo_go(k, wo_peek(x), [0n]) : Wr.Dec<Nat>}, c)
    case 1n+p:
      %Equal.sym(Nat, k, 13n, Equal.cong(Nat, Nat, wn_pred, 1n+k, 14n, e)) : {wo_first(wo_peek(wn_emit([1n+p], x))) == wo_go(_, wo_peek(x), [1n+p]) : Wr.Dec<Nat>}
      %Equal.sym(Wr.Tok, Wr.tok(Wr.dchar(1n+p)), Wr.Dig{1n+p}, wn_tok_dig(1n+p, c)) : {wo_first((_, x)) == wo_go(13n, wo_peek(x), [1n+p]) : Wr.Dec<Nat>}
      {==}

# a canonical list of at most 14 digits: the decoder reads all of it and
# has k digits left to read
def wn_f1(t: List<&2, Nat>, +d: Nat, +x: String, +k: Nat, +c: {wn_okc(t, d) == True{} : Bool},
  e: {Nat.add(List.length(&2, Nat, d <> t), k) == 14n : Nat})
  -> {wo_first(wo_peek(wn_emit(d <> t, x))) == wo_go(k, wo_peek(x), d <> t) : Wr.Dec<Nat>}:
  match t:
    case Nil{}:
      wn_f1_one(d, x, k, c, e)
    case Con{+e2, +u}:
      +hd = wn_and_l(wn_lt10(d), wn_okc(u, e2), c)
      +ih = wn_f1(u, e2, SCon{Wr.dchar(d), x}, 1n+k, wn_and_r(wn_lt10(d), wn_okc(u, e2), c),
        Equal.trans(Nat, Nat.add(List.length(&2, Nat, e2 <> u), 1n+k), 1n+Nat.add(List.length(&2, Nat, e2 <> u), k), 14n,
          wn_add_succ_r(List.length(&2, Nat, e2 <> u), k), e))
      %Equal.sym(Wr.Dec<Nat>, wo_first(wo_peek(wn_emit(e2 <> u, SCon{Wr.dchar(d), x}))), wo_go(1n+k, wo_peek(SCon{Wr.dchar(d), x}), e2 <> u), ih) : {_ == wo_go(k, wo_peek(x), d <> (e2 <> u)) : Wr.Dec<Nat>}
      %Equal.sym(Wr.Tok, Wr.tok(Wr.dchar(d)), Wr.Dig{d}, wn_tok_dig(d, hd)) : {wo_go(1n+k, (_, x), e2 <> u) == wo_go(k, wo_peek(x), d <> (e2 <> u)) : Wr.Dec<Nat>}
      {==}

def wn_f2h(b: Bool, +u: List<&2, Nat>, +e2: Nat, +d: Nat, +x: String,
  eb: {Nat.is_le(List.length(&2, Nat, e2 <> u), 14n) == b : Bool},
  hd: {wn_lt10(d) == True{} : Bool}, ct: {wn_okc(u, e2) == True{} : Bool},
  hyp: {Nat.is_le(List.length(&2, Nat, e2 <> u), 13n) == False{} : Bool},
  rec: {Nat.is_le(List.length(&2, Nat, e2 <> u), 14n) == False{} : Bool}
    -> {wo_first(wo_peek(wn_emit(e2 <> u, SCon{Wr.dchar(d), x}))) == Wr.Bad{} : Wr.Dec<Nat>})
  -> {wo_first(wo_peek(wn_emit(e2 <> u, SCon{Wr.dchar(d), x}))) == Wr.Bad{} : Wr.Dec<Nat>}:
  match b:
    case False{}:
      rec(eb)
    case True{}:
      +l14 = wn_le_last(List.length(&2, Nat, e2 <> u), 13n, eb, hyp)
      +r = wn_f1(u, e2, SCon{Wr.dchar(d), x}, 0n, ct,
        Equal.trans(Nat, Nat.add(List.length(&2, Nat, e2 <> u), 0n), List.length(&2, Nat, e2 <> u), 14n,
          wn_add_zero_r(List.length(&2, Nat, e2 <> u)), l14))
      %Equal.sym(Wr.Dec<Nat>, wo_first(wo_peek(wn_emit(e2 <> u, SCon{Wr.dchar(d), x}))), wo_go(0n, wo_peek(SCon{Wr.dchar(d), x}), e2 <> u), r) : {_ == Wr.Bad{} : Wr.Dec<Nat>}
      %Equal.sym(Wr.Tok, Wr.tok(Wr.dchar(d)), Wr.Dig{d}, wn_tok_dig(d, hd)) : {wo_end((_, x), e2 <> u) == Wr.Bad{} : Wr.Dec<Nat>}
      {==}

# a canonical list of more than 14 digits: the decoder refuses it
def wn_f2(t: List<&2, Nat>, +d: Nat, +x: String, +c: {wn_okc(t, d) == True{} : Bool})
  -> {Nat.is_le(List.length(&2, Nat, d <> t), 14n) == False{} : Bool}
  -> {wo_first(wo_peek(wn_emit(d <> t, x))) == Wr.Bad{} : Wr.Dec<Nat>}:
  match t:
    case Nil{}:
      h => wn_absurd2({wo_first(wo_peek(wn_emit([d], x))) == Wr.Bad{} : Wr.Dec<Nat>}, h)
    case Con{+e2, +u}:
      h => wn_f2h(Nat.is_le(List.length(&2, Nat, e2 <> u), 14n), u, e2, d, x, {==},
        wn_and_l(wn_lt10(d), wn_okc(u, e2), c), wn_and_r(wn_lt10(d), wn_okc(u, e2), c), h,
        wn_f2(u, e2, SCon{Wr.dchar(d), x}, wn_and_r(wn_lt10(d), wn_okc(u, e2), c)))

def wn_EC(ds: List<&2, Nat>, y: String, c: {wn_canon(ds) == True{} : Bool}) -> {Wr.put_nat(wo_value(ds), y) == wn_emit(ds, SCon{',', y}) : String}:
  match ds:
    case Nil{}:
      wn_absurd({Wr.put_nat(wo_value(Nil{}), y) == wn_emit(Nil{}, SCon{',', y}) : String}, c)
    case Con{+d, +t}:
      wn_E(t, d, y, c)

def wn_invh(tk: Wr.Tok, +k: Nat, +ds: List<&2, Nat>, +c: Char, +t: String, -n: Nat, -rest: String,
  cd: {wn_canon(ds) == True{} : Bool},
  h: {wo_go(k, (tk, t), ds) == Wr.Got{n, rest} : Wr.Dec<Nat>},
  +et: {Wr.tok(c) == tk : Wr.Tok},
  ih: @k2: Nat -> @ds2: List<&2, Nat> -> {wn_canon(ds2) == True{} : Bool}
    -> {wo_go(k2, wo_peek(t), ds2) == Wr.Got{n, rest} : Wr.Dec<Nat>} -> {wn_emit(ds2, t) == Wr.put_nat(n, rest) : String})
  -> {wn_emit(ds, SCon{c, t}) == Wr.put_nat(n, rest) : String}:
  match tk:
    case Wr.Dig{+d}:
      match k:
        case 0n:
          wn_bad_got({wn_emit(ds, SCon{c, t}) == Wr.put_nat(n, rest) : String}, n, rest, h)
        case 1n+j:
          match ds:
            case Nil{}:
              wn_absurd({wn_emit(Nil{}, SCon{c, t}) == Wr.put_nat(n, rest) : String}, cd)
            case Con{+e, +u}:
              +r = ih(j, d <> (e <> u), wn_and_intro(wn_lt10(d), wn_okc(u, e), wn_tdi_lt(c, d, et), cd), h)
              %Equal.sym(Char, c, Wr.dchar(d), wn_tdi_c(c, d, et)) : {wn_emit(e <> u, SCon{_, t}) == Wr.put_nat(n, rest) : String}
              r
    case Wr.Comma{}:
      +hg = Equal.trans(Wr.Dec<Nat>, Wr.Got{wo_value(ds), t}, wo_go(k, (Wr.Comma{}, t), ds), Wr.Got{n, rest},
        Equal.sym(Wr.Dec<Nat>, wo_go(k, (Wr.Comma{}, t), ds), Wr.Got{wo_value(ds), t}, wn_gc(k, ds, t)), h)
      %hg : {wn_emit(ds, SCon{c, t}) == wn_put_dec(_) : String}
      %Equal.sym(Char, c, ',', wn_tok_comma_inv(c, et)) : {wn_emit(ds, SCon{_, t}) == Wr.put_nat(wo_value(ds), t) : String}
      Equal.sym(String, Wr.put_nat(wo_value(ds), t), wn_emit(ds, SCon{',', t}), wn_EC(ds, t, cd))
    case Wr.Other{}:
      wn_bad_got({wn_emit(ds, SCon{c, t}) == Wr.put_nat(n, rest) : String}, n, rest,
        Equal.trans(Wr.Dec<Nat>, Wr.Bad{}, wo_go(k, (Wr.Other{}, t), ds), Wr.Got{n, rest},
          Equal.sym(Wr.Dec<Nat>, wo_go(k, (Wr.Other{}, t), ds), Wr.Bad{}, wn_gother(k, ds, t)), h))

# what the decoder accepted after the digits ds (canonical, read last first)
# is exactly the encoding of its value
def wn_inv(x: String, -n: Nat, -rest: String) -> @k: Nat -> @ds: List<&2, Nat> -> {wn_canon(ds) == True{} : Bool}
  -> {wo_go(k, wo_peek(x), ds) == Wr.Got{n, rest} : Wr.Dec<Nat>} -> {wn_emit(ds, x) == Wr.put_nat(n, rest) : String}:
  match x:
    case SNil{}:
      k => ds => cd => h => wn_bad_got({wn_emit(ds, SNil{}) == Wr.put_nat(n, rest) : String}, n, rest,
        Equal.trans(Wr.Dec<Nat>, Wr.Bad{}, wo_go(k, (Wr.Other{}, SNil{}), ds), Wr.Got{n, rest},
          Equal.sym(Wr.Dec<Nat>, wo_go(k, (Wr.Other{}, SNil{}), ds), Wr.Bad{}, wn_gother(k, ds, SNil{})), h))
    case SCon{+c, +t}:
      k => ds => cd => h => wn_invh(Wr.tok(c), k, ds, c, t, n, rest, cd, h, {==}, wn_inv(t, n, rest))

def wn_ex0h(tk: Wr.Tok, +c: Char, +c2: Char, +x2: String, -n: Nat, -rest: String,
  et: {Wr.tok(c) == Wr.Dig{0n} : Wr.Tok}, et2: {Wr.tok(c2) == tk : Wr.Tok},
  h: {wo_end((tk, x2), [0n]) == Wr.Got{n, rest} : Wr.Dec<Nat>})
  -> {SCon{c, SCon{c2, x2}} == Wr.put_nat(n, rest) : String}:
  match tk:
    case Wr.Dig{d}:
      wn_bad_got({SCon{c, SCon{c2, x2}} == Wr.put_nat(n, rest) : String}, n, rest, h)
    case Wr.Comma{}:
      %h : {SCon{c, SCon{c2, x2}} == wn_put_dec(_) : String}
      %Equal.sym(Char, c, Wr.dchar(0n), wn_tdi_c(c, 0n, et)) : {SCon{_, SCon{c2, x2}} == Wr.put_nat(wo_value([0n]), x2) : String}
      %Equal.sym(Char, c2, ',', wn_tok_comma_inv(c2, et2)) : {SCon{Wr.dchar(0n), SCon{_, x2}} == Wr.put_nat(wo_value([0n]), x2) : String}
      {==}
    case Wr.Other{}:
      wn_bad_got({SCon{c, SCon{c2, x2}} == Wr.put_nat(n, rest) : String}, n, rest, h)

def wn_ex0(x: String, +c: Char, -n: Nat, -rest: String, et: {Wr.tok(c) == Wr.Dig{0n} : Wr.Tok},
  h: {wo_end(wo_peek(x), [0n]) == Wr.Got{n, rest} : Wr.Dec<Nat>}) -> {SCon{c, x} == Wr.put_nat(n, rest) : String}:
  match x:
    case SNil{}:
      wn_bad_got({SCon{c, SNil{}} == Wr.put_nat(n, rest) : String}, n, rest, h)
    case SCon{+c2, +x2}:
      wn_ex0h(Wr.tok(c2), c, c2, x2, n, rest, et, {==}, h)

def wn_exh(tk: Wr.Tok, +c: Char, +x: String, -n: Nat, -rest: String,
  h: {wo_first((tk, x)) == Wr.Got{n, rest} : Wr.Dec<Nat>}, +et: {Wr.tok(c) == tk : Wr.Tok})
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
      wn_bad_got({SCon{c, x} == Wr.put_nat(n, rest) : String}, n, rest, h)
    case Wr.Other{}:
      wn_bad_got({SCon{c, x} == Wr.put_nat(n, rest) : String}, n, rest, h)

def wn_rt(+n: Nat, +rest: String, h: {Laws.wire_fits(n) == True{} : Bool}) -> {wo_get_nat(Wr.put_nat(n, rest)) == Wr.Got{n, rest} : Wr.Dec<Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +hl = Equal.trans(Bool, Nat.is_le(List.length(&2, Nat, wn_full(1n+p)), 14n), Nat.is_le(Laws.wire_digits(1n+p), 14n), True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, 14n), List.length(&2, Nat, wn_full(1n+p)), Laws.wire_digits(1n+p),
          Equal.sym(Nat, Laws.wire_digits(1n+p), List.length(&2, Nat, wn_full(1n+p)), wn_wl(1n+p))), h)
      +k = wn_sub(14n, List.length(&2, Nat, wn_full(1n+p)))
      +f1 = wn_f1(wn_L(1n+p, Nat.div(1n+p, 10n)), Nat.mod(1n+p, 10n), SCon{',', rest}, k, wn_cf(p),
        wn_le_k(List.length(&2, Nat, wn_full(1n+p)), 14n, hl))
      %Equal.sym(String, Wr.put_nat(1n+p, rest), wn_emit(wn_full(1n+p), SCon{',', rest}), wn_put_emit(1n+p, rest)) : {wo_get_nat(_) == Wr.Got{1n+p, rest} : Wr.Dec<Nat>}
      %Equal.sym(Wr.Dec<Nat>, wo_first(wo_peek(wn_emit(wn_full(1n+p), SCon{',', rest}))), wo_go(k, wo_peek(SCon{',', rest}), wn_full(1n+p)), f1) : {_ == Wr.Got{1n+p, rest} : Wr.Dec<Nat>}
      %Equal.sym(Wr.Dec<Nat>, wo_go(k, (Wr.Comma{}, rest), wn_full(1n+p)), Wr.Got{wo_value(wn_full(1n+p)), rest}, wn_gc(k, wn_full(1n+p), rest)) : {_ == Wr.Got{1n+p, rest} : Wr.Dec<Nat>}
      %wn_vf(1n+p) : {Wr.Got{wo_value(wn_full(1n+p)), rest} == Wr.Got{_, rest} : Wr.Dec<Nat>}
      {==}

def wn_tl(+n: Nat, +rest: String, h: {Laws.wire_fits(n) == False{} : Bool}) -> {wo_get_nat(Wr.put_nat(n, rest)) == Wr.Bad{} : Wr.Dec<Nat>}:
  match n:
    case 0n:
      wn_absurd2({wo_get_nat(Wr.put_nat(0n, rest)) == Wr.Bad{} : Wr.Dec<Nat>}, h)
    case 1n+p:
      +hl = Equal.trans(Bool, Nat.is_le(List.length(&2, Nat, wn_full(1n+p)), 14n), Nat.is_le(Laws.wire_digits(1n+p), 14n), False{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, 14n), List.length(&2, Nat, wn_full(1n+p)), Laws.wire_digits(1n+p),
          Equal.sym(Nat, Laws.wire_digits(1n+p), List.length(&2, Nat, wn_full(1n+p)), wn_wl(1n+p))), h)
      %Equal.sym(String, Wr.put_nat(1n+p, rest), wn_emit(wn_full(1n+p), SCon{',', rest}), wn_put_emit(1n+p, rest)) : {wo_get_nat(_) == Wr.Bad{} : Wr.Dec<Nat>}
      wn_f2(wn_L(1n+p, Nat.div(1n+p, 10n)), Nat.mod(1n+p, 10n), SCon{',', rest}, wn_cf(p))(hl)

def wn_ne(ds: List<&2, Nat>, c: Char, t: String, hc: {Char.is_eq(c, 'E') == False{} : Bool})
  -> {Laws.wire_opens_err(wn_emit(ds, SCon{c, t})) == False{} : Bool}:
  match ds:
    case Nil{}:
      hc
    case Con{+d, u}:
      wn_ne(u, Wr.dchar(d), SCon{c, t}, wn_dchar_ne(d))

def wn_not_err(+n: Nat, +rest: String) -> {Laws.wire_opens_err(Wr.put_nat(n, rest)) == False{} : Bool}:
  %Equal.sym(String, Wr.put_nat(n, rest), wn_emit(wn_full(n), SCon{',', rest}), wn_put_emit(n, rest)) : {Laws.wire_opens_err(_) == False{} : Bool}
  wn_ne(wn_full(n), ',', rest, {==})


# a canonical list fits the wire as its length does
def wn_fits_len(+t: List<&2, Nat>, +d: Nat, +c: {wn_okc(t, d) == True{} : Bool})
  -> {Laws.wire_fits(wo_value(d <> t)) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}:
  %Equal.sym(Nat, Laws.wire_digits(wo_value(d <> t)), List.length(&2, Nat, wn_full(wo_value(d <> t))), wn_wl(wo_value(d <> t))) : {Nat.is_le(_, 14n) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}
  %Equal.sym(List<&2, Nat>, wn_full(wo_value(d <> t)), d <> t, wn_lv(t, d, c)) : {Nat.is_le(List.length(&2, Nat, _), 14n) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}
  {==}

# ---- the laws of section wire, Nat part ----

def Laws.wire_nat_example():
  {==}

def Laws.wire_nat_zero_example():
  {==}

def Laws.wire_nat_leading_zero_example():
  {==}

def Laws.wire_nat_unterminated_example():
  {==}

def Laws.wire_nat_round_trip(n, rest, h):
  +r = rest
  Equal.trans(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, r)), wo_get_nat(Wr.put_nat(n, r)), Wr.Got{n, r},
    wn_eqv(Wr.put_nat(n, r)), wn_rt(n, r, h))

def Laws.wire_nat_exact(s, n, rest, h):
  match s:
    case SNil{}:
      wn_bad_got({SNil{} == Wr.put_nat(n, rest) : String}, n, rest, h)
    case SCon{+c, +x}:
      wn_exh(Wr.tok(c), c, x, n, rest,
        Equal.trans(Wr.Dec<Nat>, wo_get_nat(SCon{c, x}), Wr.get_nat(SCon{c, x}), Wr.Got{n, rest},
          Equal.sym(Wr.Dec<Nat>, Wr.get_nat(SCon{c, x}), wo_get_nat(SCon{c, x}), wn_eqv(SCon{c, x})), h), {==})

def Laws.wire_nat_too_long(n, rest, h):
  +r = rest
  Equal.trans(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, r)), wo_get_nat(Wr.put_nat(n, r)), Wr.Bad{},
    wn_eqv(Wr.put_nat(n, r)), wn_tl(n, r, h))

def wn_dfh(b: Bool, +s: String, +n: Nat, +rest: String, eb: {Laws.wire_fits(n) == b : Bool},
  +h: {Wr.get_nat(s) == Wr.Got{n, rest} : Wr.Dec<Nat>}) -> {Laws.wire_fits(n) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +ex = Laws.wire_nat_exact(s, n, rest, h)
      +tl = Laws.wire_nat_too_long(n, rest, eb)
      wn_bad_got({Laws.wire_fits(n) == True{} : Bool}, n, rest,
        Equal.trans(Wr.Dec<Nat>, Wr.Bad{}, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest},
          Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Bad{}, tl),
          Equal.trans(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.get_nat(s), Wr.Got{n, rest},
            Equal.cong(String, Wr.Dec<Nat>, y => Wr.get_nat(y), Wr.put_nat(n, rest), s, Equal.sym(String, s, Wr.put_nat(n, rest), ex)), h)))

def Laws.wire_nat_decoded_fits(s, n, rest, h):
  wn_dfh(Laws.wire_fits(n), s, n, rest, {==}, h)


def Laws.wire_nat_not_err(n, rest):
  wn_not_err(n, rest)

def Laws.wire_too_long_exists():
  (wo_value([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n]), Equal.trans(Bool, Laws.wire_fits(wo_value([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n])), Nat.is_le(List.length(&2, Nat, [0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n]), 14n), False{},
    wn_fits_len([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n], 0n, {==}), {==}))

# emit adds one char per digit to acc
def wn_len_emit(+ds: List<&2, Nat>, +acc: String)
  -> {String.length(wn_emit(ds, acc)) == Nat.add(List.length(&2, Nat, ds), String.length(acc)) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      %wn_add_succ_r(List.length(&2, Nat, t), String.length(acc)) : {String.length(wn_emit(t, SCon{Wr.dchar(d), acc})) == _ : Nat}
      wn_len_emit(t, SCon{Wr.dchar(d), acc})

def Laws.wire_digits_spells(n):
  +l = List.length(&2, Nat, wn_full(n))
  %Equal.sym(Nat, Laws.wire_digits(n), l, wn_wl(n)) : {String.length(Wr.put_nat(n, "")) == 1n+_ : Nat}
  %Equal.sym(String, Wr.put_nat(n, ""), wn_emit(wn_full(n), ","), wn_put_emit(n, "")) : {String.length(_) == 1n+l : Nat}
  %Equal.sym(Nat, String.length(wn_emit(wn_full(n), ",")), Nat.add(l, 1n), wn_len_emit(wn_full(n), ",")) : {_ == 1n+l : Nat}
  %Equal.sym(Nat, Nat.add(l, 1n), 1n+Nat.add(l, 0n), wn_add_succ_r(l, 0n)) : {_ == 1n+l : Nat}
  Equal.cong(Nat, Nat, k => 1n+k, Nat.add(l, 0n), l, wn_add_zero_r(l))

# ---- wire: u32 ----

# ---- wire: U32 (prefix wu_) ----

# Bool / Nat kit (copied from the bend skill, examples/sort/proof/kit.bend)

# a motive that is the goal G at True and trivial at False
def wu_Clash(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      G

# False == True proves anything
def wu_absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : wu_Clash(_, G)
  Unit{}

def wu_nat_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      wu_nat_eq_refl(p)

def wu_nat_eq_sound(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      wu_absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      wu_absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, wu_nat_eq_sound(p, q, e))

# Nat order (Nat.is_le)

def wu_le_zero(b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

def wu_le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      wu_le_refl(p)

def wu_le_succ_r(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      wu_absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      wu_le_succ_r(p, q, h)

def wu_le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      wu_le_zero(c)
    case 1n+p 0n c:
      wu_absurd({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      wu_absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      wu_le_trans(p, q, r, ab, bc)

def wu_dbl_mono(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.double(a), Nat.double(b)) == True{} : Bool}:
  match a b:
    case 0n b:
      wu_le_zero(Nat.double(b))
    case 1n+p 0n:
      wu_absurd({Nat.is_le(Nat.double(1n+p), 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      wu_dbl_mono(p, q, h)

# Nat.div by 10: Nat.div(n, 10n) is Pair.fst(Nat.divmod.go(n, 9n, 0n, 0n))

# the quotient of divmod.go never drops below its accumulator
def wu_go_acc(n: Nat, m: Nat, +e: Nat, +d: Nat, r: Nat, h: {Nat.is_le(e, d) == True{} : Bool}) -> {Nat.is_le(e, Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r))) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+np:
      match m:
        case 0n:
          wu_go_acc(np, r, e, 1n+d, 0n, wu_le_succ_r(e, d, h))
        case 1n+mp:
          wu_go_acc(np, mp, e, d, 1n+r, h)

# the quotient of divmod.go is monotone in the dividend
def wu_go_mono(n: Nat, k: Nat, m: Nat, +d: Nat, r: Nat, h: {Nat.is_le(n, k) == True{} : Bool}) -> {Nat.is_le(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), Pair.fst(Nat, Nat, Nat.divmod.go(k, m, d, r))) == True{} : Bool}:
  match n k:
    case 0n k:
      wu_go_acc(k, m, d, d, r, wu_le_refl(d))
    case 1n+np 0n:
      wu_absurd({Nat.is_le(Pair.fst(Nat, Nat, Nat.divmod.go(1n+np, m, d, r)), d) == True{} : Bool}, h)
    case 1n+np 1n+nk:
      match m:
        case 0n:
          wu_go_mono(np, nk, r, 1n+d, 0n, h)
        case 1n+mp:
          wu_go_mono(np, nk, mp, d, 1n+r, h)

def wu_div_mono(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.div(a, 10n), Nat.div(b, 10n)) == True{} : Bool}:
  wu_go_mono(a, b, 9n, 0n, 0n, h)

# the accumulator of divmod.go adds to its quotient
def wu_go_succ(n: Nat, m: Nat, d: Nat, r: Nat) -> {Pair.fst(Nat, Nat, Nat.divmod.go(n, m, 1n+d, r)) == 1n+Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          wu_go_succ(np, r, 1n+d, 0n)
        case 1n+mp:
          wu_go_succ(np, mp, d, 1n+r)

# 10 * x + 9
def wu_t10(x: Nat) -> Nat:
  match x:
    case 0n:
      9n
    case 1n+p:
      10n+wu_t10(p)

# (10 * x + 9) / 10 == x
def wu_div_t10(+x: Nat) -> {Nat.div(wu_t10(x), 10n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      +t = wu_t10(p)
      %Equal.sym(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(t, 9n, 1n, 0n)), 1n+Pair.fst(Nat, Nat, Nat.divmod.go(t, 9n, 0n, 0n)), wu_go_succ(t, 9n, 0n, 0n)) : {_ == 1n+p : Nat}
      %wu_div_t10(p) : {1n+Nat.div(t, 10n) == 1n+_ : Nat}
      {==}

# rewrite the upper bound of an is_le fact
def wu_le_rw(-a: Nat, -b: Nat, -c: Nat, h: {Nat.is_le(a, b) == True{} : Bool}, e: {b == c : Nat}) -> {Nat.is_le(a, c) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  h

# 10^e - 1: the largest Nat of e digits
def wu_nines(e: Nat) -> Nat:
  match e:
    case 0n:
      0n
    case 1n+d:
      wu_t10(wu_nines(d))

# a higher part q below 10^e adds at most e digits (whatever the fuel)
def wu_go_le(f: Nat, +q: Nat, +e: Nat, h: {Nat.is_le(q, wu_nines(e)) == True{} : Bool}) -> {Nat.is_le(Laws.wire_digits.go(f, q), e) == True{} : Bool}:
  match f q e:
    case 0n q e:
      wu_le_zero(e)
    case 1n+g 0n e:
      wu_le_zero(e)
    case 1n+g 1n+p 0n:
      wu_absurd({Nat.is_le(Laws.wire_digits.go(1n+g, 1n+p), 0n) == True{} : Bool}, h)
    case 1n+g 1n+p 1n+d:
      +n = wu_nines(d)
      wu_go_le(g, Nat.div(1n+p, 10n), d, wu_le_rw(Nat.div(1n+p, 10n), Nat.div(wu_t10(n), 10n), n, wu_div_mono(1n+p, wu_t10(n), h), wu_div_t10(n)))

# a Nat at most 10^(1+e) - 1 has at most 1+e digits
def wu_digits_le(+n: Nat, +e: Nat, h: {Nat.is_le(n, wu_nines(1n+e)) == True{} : Bool}) -> {Nat.is_le(Laws.wire_digits(n), 1n+e) == True{} : Bool}:
  +m = wu_nines(e)
  wu_go_le(n, Nat.div(n, 10n), e, wu_le_rw(Nat.div(n, 10n), Nat.div(wu_t10(m), 10n), m, wu_div_mono(n, wu_t10(m), h), wu_div_t10(m)))

# a word of 3j + r bits (r < 3) has at most 1+j decimal digits
def wu_bd(k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n:
      0n
    case 2n:
      0n
    case 3n+j:
      1n+wu_bd(j)

# one more bit: 2x + b <= 2z + 1 when x <= z
def wu_wcon_le(+p: Nat, b: Bool, +t: Word(p), +z: Nat, h: {Nat.is_le(Word.to_nat(p, t), z) == True{} : Bool}) -> {Nat.is_le(Word.to_nat(1n+p, WCon{b, t}), 1n+Nat.double(z)) == True{} : Bool}:
  match b:
    case False{}:
      wu_le_succ_r(Nat.double(Word.to_nat(p, t)), Nat.double(z), wu_dbl_mono(Word.to_nat(p, t), z, h))
    case True{}:
      wu_dbl_mono(Word.to_nat(p, t), z, h)

# 8x + 7 <= 10x + 9
def wu_87(+x: Nat) -> {Nat.is_le(1n+Nat.double(1n+Nat.double(1n+Nat.double(x))), wu_t10(x)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      +l = {1n+Nat.double(1n+Nat.double(1n+Nat.double(p))) : Nat}
      wu_le_succ_r(l, 1n+wu_t10(p), wu_le_succ_r(l, wu_t10(p), wu_87(p)))

# a word of k bits is at most 10^(1+bd(k)) - 1
def wu_word_le(+k: Nat, +w: Word(k)) -> {Nat.is_le(Word.to_nat(k, w), wu_nines(1n+wu_bd(k))) == True{} : Bool}:
  match k:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n:
      match w:
        case WCon{False{}, t}:
          {==}
        case WCon{True{}, t}:
          {==}
    case 2n:
      match w:
        case WCon{False{}, WCon{False{}, t}}:
          {==}
        case WCon{False{}, WCon{True{}, t}}:
          {==}
        case WCon{True{}, WCon{False{}, t}}:
          {==}
        case WCon{True{}, WCon{True{}, t}}:
          {==}
    case 3n+j:
      match w:
        case WCon{b0, WCon{b1, WCon{b2, t}}}:
          +n = {wu_nines(1n+wu_bd(j)) : Nat}
          +z2 = {1n+Nat.double(n) : Nat}
          +z1 = {1n+Nat.double(z2) : Nat}
          +z0 = {1n+Nat.double(z1) : Nat}
          s2 = wu_wcon_le(j, b2, t, n, wu_word_le(j, t))
          s1 = wu_wcon_le(1n+j, b1, WCon{b2, t}, z2, s2)
          s0 = wu_wcon_le(2n+j, b0, WCon{b1, WCon{b2, t}}, z1, s1)
          wu_le_trans(Word.to_nat(3n+j, WCon{b0, WCon{b1, WCon{b2, t}}}), z0, wu_t10(n), s0, wu_87(n))

# every 32-bit word fits the wire (at most 11 digits), with no 2^32 computed
def wu_u32_fits(+w: Word(32n)) -> {Laws.wire_fits(Word.to_nat(32n, w)) == True{} : Bool}:
  +n = Word.to_nat(32n, w)
  wu_le_trans(Laws.wire_digits(n), 1n+wu_bd(32n), 14n, wu_digits_le(n, wu_bd(32n), wu_word_le(32n, w)), {==})

# U32.from_nat inverts U32.to_nat

# Word.inc applied m times to the zero word of k bits
def wu_iter(+k: Nat, m: Nat) -> Word(k):
  match m:
    case 0n:
      Word.zero(k)
    case 1n+p:
      Word.inc(k, wu_iter(k, p))

def wu_from_nat(+m: Nat) -> {U32.from_nat(m) == U32{wu_iter(32n, m)} : U32}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(U32, U32.from_nat(p), U32{wu_iter(32n, p)}, wu_from_nat(p)) : {U32.inc(_) == U32{Word.inc(32n, wu_iter(32n, p))} : U32}
      {==}

# 2m increments of a word of 1+p bits: bit 0 low, m increments above
def wu_iter_even(+p: Nat, +m: Nat) -> {wu_iter(1n+p, Nat.double(m)) == WCon{False{}, wu_iter(p, m)} : Word(1n+p)}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(Word(1n+p), wu_iter(1n+p, Nat.double(q)), WCon{False{}, wu_iter(p, q)}, wu_iter_even(p, q)) : {Word.inc(1n+p, Word.inc(1n+p, _)) == WCon{False{}, Word.inc(p, wu_iter(p, q))} : Word(1n+p)}
      {==}

# 2m + 1 increments: bit 0 high, m increments above
def wu_iter_odd(+p: Nat, +m: Nat) -> {wu_iter(1n+p, 1n+Nat.double(m)) == WCon{True{}, wu_iter(p, m)} : Word(1n+p)}:
  %Equal.sym(Word(1n+p), wu_iter(1n+p, Nat.double(m)), WCon{False{}, wu_iter(p, m)}, wu_iter_even(p, m)) : {Word.inc(1n+p, _) == WCon{True{}, wu_iter(p, m)} : Word(1n+p)}
  {==}

# Word.to_nat(k, w) increments of zero give w back
def wu_iter_to_nat(+k: Nat, +w: Word(k)) -> {wu_iter(k, Word.to_nat(k, w)) == w : Word(k)}:
  match k:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          %Equal.sym(Word(1n+p), wu_iter(1n+p, Nat.double(Word.to_nat(p, t))), WCon{False{}, wu_iter(p, Word.to_nat(p, t))}, wu_iter_even(p, Word.to_nat(p, t))) : {_ == WCon{False{}, t} : Word(1n+p)}
          %wu_iter_to_nat(p, t) : {WCon{False{}, wu_iter(p, Word.to_nat(p, t))} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, t}:
          %Equal.sym(Word(1n+p), wu_iter(1n+p, 1n+Nat.double(Word.to_nat(p, t))), WCon{True{}, wu_iter(p, Word.to_nat(p, t))}, wu_iter_odd(p, Word.to_nat(p, t))) : {_ == WCon{True{}, t} : Word(1n+p)}
          %wu_iter_to_nat(p, t) : {WCon{True{}, wu_iter(p, Word.to_nat(p, t))} == WCon{True{}, _} : Word(1n+p)}
          {==}

def wu_from_to(+w: Word(32n)) -> {U32.from_nat(Word.to_nat(32n, w)) == U32{w} : U32}:
  +n = Word.to_nat(32n, w)
  %Equal.sym(U32, U32.from_nat(n), U32{wu_iter(32n, n)}, wu_from_nat(n)) : {_ == U32{w} : U32}
  %wu_iter_to_nat(32n, w) : {U32{wu_iter(32n, n)} == U32{_} : U32}
  {==}

# get_u32 accepts only what get_nat read and from_nat keeps

# a motive: at Got{y, r}, a is the Nat answer of y and r; trivial at Bad
def wu_M(a: Wr.Dec<Nat>, d: Wr.Dec<U32>) -> Type:
  match d:
    case Wr.Got{y, r}:
      {a == Wr.Got{U32.to_nat(y), r} : Wr.Dec<Nat>}
    case Wr.Bad{}:
      Unit

def wu_in_inv(ok: Bool, +n: Nat, +s: String, -x: U32, -rest: String, eok: {Nat.is_eq(U32.to_nat(U32.from_nat(n)), n) == ok : Bool}, h: {Wr.get_u32.in(ok, U32.from_nat(n), s) == Wr.Got{x, rest} : Wr.Dec<U32>}) -> {Wr.Got{n, s} == Wr.Got{U32.to_nat(x), rest} : Wr.Dec<Nat>}:
  match ok:
    case False{}:
      %h : wu_M(Wr.Got{n, s}, _)
      Unit{}
    case True{}:
      %h : wu_M(Wr.Got{n, s}, _)
      %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, wu_nat_eq_sound(U32.to_nat(U32.from_nat(n)), n, eok)) : {Wr.Got{n, s} == Wr.Got{_, s} : Wr.Dec<Nat>}
      {==}

def wu_fit_inv(+r: Wr.Dec<Nat>, -x: U32, -rest: String, h: {Wr.get_u32.fit(r) == Wr.Got{x, rest} : Wr.Dec<U32>}) -> {r == Wr.Got{U32.to_nat(x), rest} : Wr.Dec<Nat>}:
  match r:
    case Wr.Got{n, s}:
      wu_in_inv(Nat.is_eq(U32.to_nat(U32.from_nat(n)), n), n, s, x, rest, {==}, h)
    case Wr.Bad{}:
      %h : wu_M(Wr.Bad{}, _)
      Unit{}

# laws of the other slices used here (filled by their provers)
def Laws.wire_u32_round_trip(x, rest):
  match x:
    case U32{w}:
      +n = Word.to_nat(32n, w)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Laws.wire_nat_round_trip(n, rest, wu_u32_fits(w))) : {Wr.get_u32.fit(_) == Wr.Got{U32{w}, rest} : Wr.Dec<U32>}
      %Equal.sym(U32, U32.from_nat(n), U32{w}, wu_from_to(w)) : {Wr.get_u32.in(Nat.is_eq(U32.to_nat(_), n), _, rest) == Wr.Got{U32{w}, rest} : Wr.Dec<U32>}
      %Equal.sym(Bool, Nat.is_eq(n, n), True{}, wu_nat_eq_refl(n)) : {Wr.get_u32.in(_, U32{w}, rest) == Wr.Got{U32{w}, rest} : Wr.Dec<U32>}
      {==}

# LAW wire_u32_exact
def Laws.wire_u32_exact(s, x, rest, h):
  Laws.wire_nat_exact(s, U32.to_nat(x), rest, wu_fit_inv(Wr.get_nat(s), x, rest, h))

# LAW wire_u32_example
def Laws.wire_u32_example():
  {==}

# ---- wire: rest ----

# ---- wire (Bool, String, List, replies) ----

# Kit (copied from the bend skill, examples/sort/proof/u32_order.bend)
# ---

# a motive that is the goal G at True and trivial at False
def wr_clash(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      G

# False == True proves anything
def wr_absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : wr_clash(_, G)
  Unit{}

def wr_lt_eq(-G: Type, e: {LT{} == EQ{} : Cmp}) -> G:
  wr_absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), LT{}, EQ{}, e))

def wr_gt_eq(-G: Type, e: {GT{} == EQ{} : Cmp}) -> G:
  wr_absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), GT{}, EQ{}, e))

def wr_cmp_eq_fin(-p: Nat, -at: Word(p), -bt: Word(p), t: Cmp, +ab: Bool, +bb: Bool,
  et: {Word.cmp(p, at, bt) == t : Cmp},
  rec: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)},
  e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp})
  -> {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}:
  match t:
    case LT{}:
      wr_lt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case GT{}:
      wr_gt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt, rec(et))
        case False{} True{}:
          wr_lt_eq({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, e)
        case True{} False{}:
          wr_gt_eq({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, e)
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt, rec(et))

# words that compare EQ are the same word (u32_order: Word.cmp_eq)
def wr_word_cmp_eq(+n: Nat, +a: Word(n), +b: Word(n)) ->
  {Word.cmp(n, a, b) == EQ{} : Cmp} -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          e => {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          e => wr_cmp_eq_fin(p, at, bt, Word.cmp(p, at, bt), ab, bb, {==},
            wr_word_cmp_eq(p, at, bt), e)

# U32 values that compare EQ are equal (u32_order: cmp_eq)
def wr_cmp_eq(+a: U32, +b: U32) -> {U32.cmp(a, b) == EQ{} : Cmp} -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      e => Equal.cong(Word(32n), U32, w => U32{w}, x, y, wr_word_cmp_eq(32n, x, y)(e))

def wr_sound_fin(+a: U32, +b: U32, t: Cmp, et: {U32.cmp(a, b) == t : Cmp},
  e: {Cmp.is_eq(t) == True{} : Bool}) -> {a == b : U32}:
  match t:
    case LT{}:
      wr_absurd({a == b : U32}, e)
    case EQ{}:
      wr_cmp_eq(a, b)(et)
    case GT{}:
      wr_absurd({a == b : U32}, e)

# U32.is_eq is real equality (u32_order: eq_sound)
def wr_eq_sound(+a: U32, +b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  wr_sound_fin(a, b, U32.cmp(a, b), {==}, e)

# Bool.and == True splits
def wr_and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      {==}

def wr_and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      wr_absurd({b == True{} : Bool}, e)
    case True{}:
      e

# Bool
# ----

# what a Bool decoder answer says about its input s
def wr_pb(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def wr_bool_pick(+x: U32, +t: String, p: Bool, ep: {U32.is_eq(x, 84) == p : Bool},
  q: Bool, eq: {U32.is_eq(x, 70) == q : Bool}) -> wr_pb(SCon{Chr{x}, t}, Wr.get_bool.pick(p, q, t)):
  match p:
    case True{}:
      %Equal.sym(U32, x, 84, wr_eq_sound(x, 84, ep)) : {SCon{Chr{_}, t} == SCon{'T', t} : String}
      {==}
    case False{}:
      match q:
        case True{}:
          %Equal.sym(U32, x, 70, wr_eq_sound(x, 70, eq)) : {SCon{Chr{_}, t} == SCon{'F', t} : String}
          {==}
        case False{}:
          Unit{}

# every Bool the decoder reads is the encoding of what it answers
def wr_bool_spec(s: String) -> wr_pb(s, Wr.get_bool(s)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          wr_bool_pick(x, t, U32.is_eq(x, 84), {==}, U32.is_eq(x, 70), {==})

def Laws.wire_bool_round_trip(b, rest):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.wire_bool_exact(s, b, rest, h):
  %h : wr_pb(s, _)
  wr_bool_spec(s)

def Laws.wire_bool_not_err(b, rest):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.wire_bool_example():
  {==}

# String
# ------

# a then rest
def wr_app(a: String, rest: String) -> String:
  match a:
    case SNil{}:
      rest
    case SCon{c, t}:
      SCon{c, wr_app(t, rest)}

# put_str.go turns a around onto acc and adds its length to n
def wr_put_str_go(a: String, -acc: String, -n: Nat) ->
  {Wr.put_str.go(a, acc, n) == (Nat.add(String.length(a), n), String.reverse.go(a, acc)) : Nat & String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      %Equal.sym(Nat & String, Wr.put_str.go(t, SCon{c, acc}, 1n+n), (Nat.add(String.length(t), 1n+n), String.reverse.go(t, SCon{c, acc})), wr_put_str_go(t, SCon{c, acc}, 1n+n)) : {_ == (1n+Nat.add(String.length(t), n), String.reverse.go(t, SCon{c, acc})) : Nat & String}
      %wn_add_succ_r(String.length(t), n) : {(Nat.add(String.length(t), 1n+n), String.reverse.go(t, SCon{c, acc})) == (_, String.reverse.go(t, SCon{c, acc})) : Nat & String}
      {==}

# turning a around onto acc, then all of it around onto rest, puts a before rest
def wr_rev_rev(a: String, -acc: String, -rest: String) ->
  {String.reverse.go(String.reverse.go(a, acc), rest) == String.reverse.go(acc, wr_app(a, rest)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      wr_rev_rev(t, SCon{c, acc}, rest)

# a string is its length, then its chars
def wr_put_str(+a: String, +rest: String) ->
  {Wr.put_str(a, rest) == Wr.put_nat(String.length(a), wr_app(a, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_str.go(a, SNil{}, 0n), (Nat.add(String.length(a), 0n), String.reverse.go(a, SNil{})), wr_put_str_go(a, SNil{}, 0n)) : {Wr.put_str.fin(_, rest) == Wr.put_nat(String.length(a), wr_app(a, rest)) : String}
  %Equal.sym(Nat, Nat.add(String.length(a), 0n), String.length(a), wn_add_zero_r(String.length(a))) : {Wr.put_nat(_, String.reverse.go(String.reverse.go(a, SNil{}), rest)) == Wr.put_nat(String.length(a), wr_app(a, rest)) : String}
  %Equal.sym(String, String.reverse.go(String.reverse.go(a, SNil{}), rest), wr_app(a, rest), wr_rev_rev(a, SNil{}, rest)) : {Wr.put_nat(String.length(a), _) == Wr.put_nat(String.length(a), wr_app(a, rest)) : String}
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
  {wo_take(String.length(a), wr_app(a, rest)) == Wr.Got{a, rest} : Wr.Dec<String>}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      %Equal.sym(Wr.Dec<String>, wo_take(String.length(t), wr_app(t, rest)), Wr.Got{t, rest}, wr_take_rt(t, rest)) : {wo_take_cons(c, _) == Wr.Got{SCon{c, t}, rest} : Wr.Dec<String>}
      {==}

# what take's answer says about its input s
def wr_pt(s: String, n: Nat, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{+a, r}:
      {s == wr_app(a, r) : String} & {String.length(a) == n : Nat}
    case Wr.Bad{}:
      Unit

def wr_take_step(c: Char, +t: String, -m: Nat, r: Wr.Dec<String>, ih: wr_pt(t, m, r)) ->
  wr_pt(SCon{c, t}, 1n+m, wo_take_cons(c, r)):
  match r:
    case Wr.Got{+a, +s3}:
      (e1, e2) = ih
      (Equal.cong(String, String, z => SCon{c, z}, t, wr_app(a, s3), e1),
        Equal.cong(Nat, Nat, k => 1n+k, String.length(a), m, e2))
    case Wr.Bad{}:
      Unit{}

# the reference take(n, s) == Got{a, r} only when s == a ++ r and a has n chars
def wr_take_spec(n: Nat, s: String) -> wr_pt(s, n, wo_take(n, s)):
  match n:
    case 0n:
      ({==}, {==})
    case 1n++m:
      match s:
        case SNil{}:
          Unit{}
        case SCon{c, +t}:
          wr_take_step(c, t, m, wo_take(m, t), wr_take_spec(m, t))

# Nat laws used as lemmas (proved in the Nat slice)
def Laws.wire_str_round_trip(a, rest, h):
  +r = rest
  %Equal.sym(String, Wr.put_str(a, r), Wr.put_nat(String.length(a), wr_app(a, r)), wr_put_str(a, r)) : {Wr.get_str(_) == Wr.Got{a, r} : Wr.Dec<String>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(String.length(a), wr_app(a, r))), Wr.Got{String.length(a), wr_app(a, r)}, Laws.wire_nat_round_trip(String.length(a), wr_app(a, r), h)) : {Wr.get_str.go(_) == Wr.Got{a, r} : Wr.Dec<String>}
  Equal.trans(Wr.Dec<String>, Wr.take(String.length(a), wr_app(a, r)), wo_take(String.length(a), wr_app(a, r)), Wr.Got{a, r},
    wr_take_eq(String.length(a), wr_app(a, r)), wr_take_rt(a, r))

# what a String decoder answer says about its input s
def wr_ps(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == Wr.put_str(a, r) : String}
    case Wr.Bad{}:
      Unit

def wr_str_conv(+s: String, +s2: String, -n: Nat, en: {s == Wr.put_nat(n, s2) : String},
  d: Wr.Dec<String>, pt: wr_pt(s2, n, d)) -> wr_ps(s, d):
  match d:
    case Wr.Got{+a, +r}:
      (e1, e2) = pt
      %Equal.sym(String, Wr.put_str(a, r), Wr.put_nat(String.length(a), wr_app(a, r)), wr_put_str(a, r)) : {s == _ : String}
      %Equal.sym(Nat, String.length(a), n, e2) : {s == Wr.put_nat(_, wr_app(a, r)) : String}
      %e1 : {s == Wr.put_nat(n, _) : String}
      en
    case Wr.Bad{}:
      Unit{}

def wr_str_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) ->
  wr_ps(s, Wr.get_str.go(r)):
  match r:
    case Wr.Got{+n, +s2}:
      %Equal.sym(Wr.Dec<String>, Wr.take(n, s2), wo_take(n, s2), wr_take_eq(n, s2)) : wr_ps(s, _)
      wr_str_conv(s, s2, n, Laws.wire_nat_exact(s, n, s2, er), wo_take(n, s2), wr_take_spec(n, s2))
    case Wr.Bad{}:
      Unit{}

def Laws.wire_str_exact(s, a, rest, h):
  %h : wr_ps(s, _)
  wr_str_top(s, Wr.get_nat(s), {==})

def Laws.wire_str_example():
  {==}

# Lists
# -----

# the items of xs, then rest
def wr_items(xs: List<&2, Nat>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Wr.put_nat(x, wr_items(t, rest))

def wr_put_list_go(xs: List<&2, Nat>, -rest: String) ->
  {Wr.put_list.go(~Nat, ~Wr.put_nat, xs, rest) == (List.length(&2, Nat, xs), wr_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Nat, ~Wr.put_nat, t, rest), (List.length(&2, Nat, t), wr_items(t, rest)), wr_put_list_go(t, rest)) : {Wr.put_list.step(~Nat, ~Wr.put_nat, x, _) == (1n+List.length(&2, Nat, t), Wr.put_nat(x, wr_items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def wr_put_list(+xs: List<&2, Nat>, -rest: String) ->
  {Wr.put_list(~Nat, ~Wr.put_nat, xs, rest) == Wr.put_nat(List.length(&2, Nat, xs), wr_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Nat, ~Wr.put_nat, xs, rest), (List.length(&2, Nat, xs), wr_items(xs, rest)), wr_put_list_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Nat, xs), wr_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def wr_list_go_rt(+t: List<&2, Nat>, +x: Nat, +rest: String,
  +hf: {Laws.wire_nats_fit(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Nat, ~Wr.get_nat, List.length(&2, Nat, t), Wr.get_nat(Wr.put_nat(x, wr_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Nat>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(x, rest)), Wr.Got{x, rest}, Laws.wire_nat_round_trip(x, rest, wr_and_l(Laws.wire_fits(x), True{}, hf))) : {Wr.get_list.go(~Nat, ~Wr.get_nat, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Nat>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(x, Wr.put_nat(y, wr_items(u, rest)))), Wr.Got{x, Wr.put_nat(y, wr_items(u, rest))}, Laws.wire_nat_round_trip(x, Wr.put_nat(y, wr_items(u, rest)), wr_and_l(Laws.wire_fits(x), Laws.wire_nats_fit(y <> u), hf))) : {Wr.get_list.go(~Nat, ~Wr.get_nat, 1n+List.length(&2, Nat, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Nat>>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list.go(~Nat, ~Wr.get_nat, List.length(&2, Nat, u), Wr.get_nat(Wr.put_nat(y, wr_items(u, rest)))), Wr.Got{y <> u, rest}, wr_list_go_rt(u, y, rest, wr_and_r(Laws.wire_fits(x), Laws.wire_nats_fit(y <> u), hf))) : {Wr.get_list.cons(Nat, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Nat>>}
      {==}

def Laws.wire_list_round_trip(xs, rest, h):
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Laws.wire_nat_round_trip(0n, rest, wr_and_l(Laws.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Nat, ~Wr.get_nat, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Nat>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, x <> t, r), Wr.put_nat(List.length(&2, Nat, x <> t), wr_items(x <> t, r)), wr_put_list(x <> t, r)) : {Wr.get_list(~Nat, ~Wr.get_nat, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Nat>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Nat, x <> t), wr_items(x <> t, r))), Wr.Got{List.length(&2, Nat, x <> t), wr_items(x <> t, r)}, Laws.wire_nat_round_trip(List.length(&2, Nat, x <> t), wr_items(x <> t, r), wr_and_l(Laws.wire_fits(List.length(&2, Nat, x <> t)), Laws.wire_nats_fit(x <> t), hh))) : {Wr.get_list.start(~Nat, ~Wr.get_nat, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Nat>>}
      wr_list_go_rt(t, x, r, wr_and_r(Laws.wire_fits(List.length(&2, Nat, x <> t)), Laws.wire_nats_fit(x <> t), hh))

# what the item loop's answer says about its input s (m + 1 items)
def wr_pl(s: String, m: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == wr_items(xs, r) : String} & {List.length(&2, Nat, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def wr_list_step(-s: String, +x: Nat, +s3: String, -k: Nat, ex: {s == Wr.put_nat(x, s3) : String},
  d: Wr.Dec<List<&2, Nat>>, ih: wr_pl(s3, k, d)) -> wr_pl(s, 1n+k, Wr.get_list.cons(Nat, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (Equal.trans(String, s, Wr.put_nat(x, s3), Wr.put_nat(x, wr_items(ys, r)), ex,
          Equal.cong(String, String, z => Wr.put_nat(x, z), s3, wr_items(ys, r), e1)),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Nat, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only items that are encodings
def wr_list_spec(m: Nat, cur: Wr.Dec<Nat>, +s: String, er: {Wr.get_nat(s) == cur : Wr.Dec<Nat>}) ->
  wr_pl(s, m, Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (Laws.wire_nat_exact(s, x, s3, er), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      wr_list_step(s, x, s3, k, Laws.wire_nat_exact(s, x, s3, er),
        Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(s3)), wr_list_spec(k, Wr.get_nat(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder answer says about its input s
def wr_pls(s: String, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_list(~Nat, ~Wr.put_nat, xs, r) : String}
    case Wr.Bad{}:
      Unit

def wr_list_conv(+s: String, +s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  d: Wr.Dec<List<&2, Nat>>, pl: wr_pl(s2, m, d)) -> wr_pls(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = pl
      %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, xs, r), Wr.put_nat(List.length(&2, Nat, xs), wr_items(xs, r)), wr_put_list(xs, r)) : {s == _ : String}
      %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e2) : {s == Wr.put_nat(_, wr_items(xs, r)) : String}
      %e1 : {s == Wr.put_nat(1n+m, _) : String}
      en
    case Wr.Bad{}:
      Unit{}

def wr_list_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}) ->
  wr_pls(s, Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s2})):
  match n:
    case 0n:
      en
    case 1n++m:
      wr_list_conv(s, s2, m, en, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s2)),
        wr_list_spec(m, Wr.get_nat(s2), s2, {==}))

def wr_list_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) ->
  wr_pls(s, Wr.get_list.start(~Nat, ~Wr.get_nat, r)):
  match r:
    case Wr.Got{+n, +s2}:
      wr_list_nat(s, n, s2, Laws.wire_nat_exact(s, n, s2, er))
    case Wr.Bad{}:
      Unit{}

def Laws.wire_list_exact(s, xs, rest, h):
  %h : wr_pls(s, _)
  wr_list_top(s, Wr.get_nat(s), {==})

def Laws.wire_list_example():
  {==}

# Replies
# -------

def Laws.wire_err_example(text):
  {==}

def Laws.wire_end_exact(s):
  {==}
