# eukhe: lemmas the proofs of two or more areas share

import Base
import ../bend/child.bend as Ch
import ../bend/command.bend as Cmd
import ../bend/director.bend as Dr
import ../bend/effort.bend as Ef
import ../bend/fsmode.bend as Fs
import ../bend/infer.bend as If
import ../bend/optchat.bend as O
import ../bend/path_policy.bend as Pp
import ../bend/progress.bend as Pr
import ../bend/replace.bend as Rp
import ../bend/retry.bend as R
import ../bend/run.bend as Rn
import ../bend/semver.bend as Sv
import ../bend/tree.bend as Tr
import ../bend/wire.bend as Wr
import ../bend/wire_flat.bend as Fl
import ../laws/command.bend as Command
import ../laws/base.bend as LawsBase
import ../laws/replace.bend as Replace
import ../laws/wire.bend as Wire

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

def wn_pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

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

def wn_lenL(g: Nat, +q: Nat) -> {List.length(&2, Nat, wn_L(g, q)) == LawsBase.wire_digits.go(g, q) : Nat}:
  match g:
    case 0n:
      {==}
    case 1n+f:
      match q:
        case 0n:
          {==}
        case 1n+p:
          Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Nat, wn_L(f, Nat.div(1n+p, 10n))),
            LawsBase.wire_digits.go(f, Nat.div(1n+p, 10n)), wn_lenL(f, Nat.div(1n+p, 10n)))

# wire_digits(n) counts the digits of n
def wn_wl(+n: Nat) -> {LawsBase.wire_digits(n) == List.length(&2, Nat, wn_full(n)) : Nat}:
  Equal.cong(Nat, Nat, k => 1n+k, LawsBase.wire_digits.go(n, Nat.div(n, 10n)), List.length(&2, Nat, wn_L(n, Nat.div(n, 10n))),
    Equal.sym(Nat, List.length(&2, Nat, wn_L(n, Nat.div(n, 10n))), LawsBase.wire_digits.go(n, Nat.div(n, 10n)), wn_lenL(n, Nat.div(n, 10n))))

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

def wn_rt(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {wo_get_nat(Wr.put_nat(n, rest)) == Wr.Got{n, rest} : Wr.Dec<Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +hl = Equal.trans(Bool, Nat.is_le(List.length(&2, Nat, wn_full(1n+p)), 14n), Nat.is_le(LawsBase.wire_digits(1n+p), 14n), True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, 14n), List.length(&2, Nat, wn_full(1n+p)), LawsBase.wire_digits(1n+p),
          Equal.sym(Nat, LawsBase.wire_digits(1n+p), List.length(&2, Nat, wn_full(1n+p)), wn_wl(1n+p))), h)
      +k = wn_sub(14n, List.length(&2, Nat, wn_full(1n+p)))
      +f1 = wn_f1(wn_L(1n+p, Nat.div(1n+p, 10n)), Nat.mod(1n+p, 10n), SCon{',', rest}, k, wn_cf(p),
        wn_le_k(List.length(&2, Nat, wn_full(1n+p)), 14n, hl))
      %Equal.sym(String, Wr.put_nat(1n+p, rest), wn_emit(wn_full(1n+p), SCon{',', rest}), wn_put_emit(1n+p, rest)) : {wo_get_nat(_) == Wr.Got{1n+p, rest} : Wr.Dec<Nat>}
      %Equal.sym(Wr.Dec<Nat>, wo_first(wo_peek(wn_emit(wn_full(1n+p), SCon{',', rest}))), wo_go(k, wo_peek(SCon{',', rest}), wn_full(1n+p)), f1) : {_ == Wr.Got{1n+p, rest} : Wr.Dec<Nat>}
      %Equal.sym(Wr.Dec<Nat>, wo_go(k, (Wr.Comma{}, rest), wn_full(1n+p)), Wr.Got{wo_value(wn_full(1n+p)), rest}, wn_gc(k, wn_full(1n+p), rest)) : {_ == Wr.Got{1n+p, rest} : Wr.Dec<Nat>}
      %wn_vf(1n+p) : {Wr.Got{wo_value(wn_full(1n+p)), rest} == Wr.Got{_, rest} : Wr.Dec<Nat>}
      {==}

def Wire.wire_nat_round_trip(n, rest, h):
  +r = rest
  Equal.trans(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, r)), wo_get_nat(Wr.put_nat(n, r)), Wr.Got{n, r},
    wn_eqv(Wr.put_nat(n, r)), wn_rt(n, r, h))

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

# Nat laws used as lemmas (proved in the Nat slice)
def Wire.wire_str_round_trip(a, rest, h):
  +r = rest
  %Equal.sym(String, Wr.put_str(a, r), Wr.put_nat(String.length(a), wr_app(a, r)), wr_put_str(a, r)) : {Wr.get_str(_) == Wr.Got{a, r} : Wr.Dec<String>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(String.length(a), wr_app(a, r))), Wr.Got{String.length(a), wr_app(a, r)}, Wire.wire_nat_round_trip(String.length(a), wr_app(a, r), h)) : {Wr.get_str.go(_) == Wr.Got{a, r} : Wr.Dec<String>}
  Equal.trans(Wr.Dec<String>, Wr.take(String.length(a), wr_app(a, r)), wo_take(String.length(a), wr_app(a, r)), Wr.Got{a, r},
    wr_take_eq(String.length(a), wr_app(a, r)), wr_take_rt(a, r))

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
  +hf: {LawsBase.wire_nats_fit(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Nat, ~Wr.get_nat, List.length(&2, Nat, t), Wr.get_nat(Wr.put_nat(x, wr_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Nat>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(x, rest)), Wr.Got{x, rest}, Wire.wire_nat_round_trip(x, rest, wr_and_l(LawsBase.wire_fits(x), True{}, hf))) : {Wr.get_list.go(~Nat, ~Wr.get_nat, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Nat>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(x, Wr.put_nat(y, wr_items(u, rest)))), Wr.Got{x, Wr.put_nat(y, wr_items(u, rest))}, Wire.wire_nat_round_trip(x, Wr.put_nat(y, wr_items(u, rest)), wr_and_l(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(y <> u), hf))) : {Wr.get_list.go(~Nat, ~Wr.get_nat, 1n+List.length(&2, Nat, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Nat>>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list.go(~Nat, ~Wr.get_nat, List.length(&2, Nat, u), Wr.get_nat(Wr.put_nat(y, wr_items(u, rest)))), Wr.Got{y <> u, rest}, wr_list_go_rt(u, y, rest, wr_and_r(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(y <> u), hf))) : {Wr.get_list.cons(Nat, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Nat>>}
      {==}

def Wire.wire_list_round_trip(xs, rest, h):
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, wr_and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Nat, ~Wr.get_nat, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Nat>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, x <> t, r), Wr.put_nat(List.length(&2, Nat, x <> t), wr_items(x <> t, r)), wr_put_list(x <> t, r)) : {Wr.get_list(~Nat, ~Wr.get_nat, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Nat>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Nat, x <> t), wr_items(x <> t, r))), Wr.Got{List.length(&2, Nat, x <> t), wr_items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Nat, x <> t), wr_items(x <> t, r), wr_and_l(LawsBase.wire_fits(List.length(&2, Nat, x <> t)), LawsBase.wire_nats_fit(x <> t), hh))) : {Wr.get_list.start(~Nat, ~Wr.get_nat, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Nat>>}
      wr_list_go_rt(t, x, r, wr_and_r(LawsBase.wire_fits(List.length(&2, Nat, x <> t)), LawsBase.wire_nats_fit(x <> t), hh))

# Logic
# -----

# G when b is True, Unit when False
def cb_If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True: anything follows
def cb_absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : cb_If(_, G)
  Unit{}

def cb_and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      cb_absurd({False{} == True{} : Bool}, e)
    case True{}:
      {==}

def cb_and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      cb_absurd({b == True{} : Bool}, e)
    case True{}:
      e

def cb_app_assoc(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %cb_app_assoc(A, t, ys, zs) : {h <> List.append(&2, A, List.append(&2, A, t, ys), zs) == h <> _ : List<&2, A>}
      {==}

# Equality of chars, names, paths
# -------------------------------

def cb_nat_eq(+x: Nat, +y: Nat, e: {Nat.is_eq(x, y) == True{} : Bool}) -> {x == y : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      cb_absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      cb_absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %cb_nat_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def cb_nat_refl(x: Nat) -> {Nat.is_eq(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      cb_nat_refl(p)

def cb_and_intro(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# cmd_eq true: the names are equal
def cb_eq(+a: List<&2, Nat>, +b: List<&2, Nat>, +e: {Command.cmd_eq(a, b) == True{} : Bool}) -> {a == b : List<&2, Nat>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      cb_absurd({Nil{} == y <> ys : List<&2, Nat>}, e)
    case Con{x, xs} Nil{}:
      cb_absurd({x <> xs == Nil{} : List<&2, Nat>}, e)
    case Con{+x, +xs} Con{+y, +ys}:
      %cb_nat_eq(x, y, cb_and_l(Nat.is_eq(x, y), Command.cmd_eq(xs, ys), e)) : {x <> xs == _ <> ys : List<&2, Nat>}
      %cb_eq(xs, ys, cb_and_r(Nat.is_eq(x, y), Command.cmd_eq(xs, ys), e)) : {x <> xs == x <> _ : List<&2, Nat>}
      {==}

def cb_eq_refl(a: List<&2, Nat>) -> {Command.cmd_eq(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      cb_and_intro(Nat.is_eq(x, x), Command.cmd_eq(xs, xs), cb_nat_refl(x), cb_eq_refl(xs))

# the model's same is cmd_eq
def cb_same(a: List<&2, Nat>, b: List<&2, Nat>) -> {Cmd.same(a, b) == Command.cmd_eq(a, b) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      {==}
    case Con{x, xs} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      %cb_same(xs, ys) : {Bool.and(Nat.is_eq(x, y), Cmd.same(xs, ys)) == Bool.and(Nat.is_eq(x, y), _) : Bool}
      {==}

def cb_same_eq(+a: List<&2, Nat>, +b: List<&2, Nat>, e: {Cmd.same(a, b) == True{} : Bool}) -> {a == b : List<&2, Nat>}:
  cb_eq(a, b, Equal.trans(Bool, Command.cmd_eq(a, b), Cmd.same(a, b), True{}, Equal.sym(Bool, Cmd.same(a, b), Command.cmd_eq(a, b), cb_same(a, b)), e))

# cmd_path_eq true: the paths are equal
def cb_path_eq(+a: List<&2, List<&2, Nat>>, +b: List<&2, List<&2, Nat>>, +e: {Command.cmd_path_eq(a, b) == True{} : Bool}) -> {a == b : List<&2, List<&2, Nat>>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      cb_absurd({Nil{} == y <> ys : List<&2, List<&2, Nat>>}, e)
    case Con{x, xs} Nil{}:
      cb_absurd({x <> xs == Nil{} : List<&2, List<&2, Nat>>}, e)
    case Con{+x, +xs} Con{+y, +ys}:
      %cb_eq(x, y, cb_and_l(Command.cmd_eq(x, y), Command.cmd_path_eq(xs, ys), e)) : {x <> xs == _ <> ys : List<&2, List<&2, Nat>>}
      %cb_path_eq(xs, ys, cb_and_r(Command.cmd_eq(x, y), Command.cmd_path_eq(xs, ys), e)) : {x <> xs == x <> _ : List<&2, List<&2, Nat>>}
      {==}

def cb_path_refl(a: List<&2, List<&2, Nat>>) -> {Command.cmd_path_eq(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      cb_and_intro(Command.cmd_eq(x, x), Command.cmd_path_eq(xs, xs), cb_eq_refl(x), cb_path_refl(xs))

# the model's same_path is cmd_path_eq
def cb_same_path(a: List<&2, List<&2, Nat>>, b: List<&2, List<&2, Nat>>) -> {Cmd.same_path(a, b) == Command.cmd_path_eq(a, b) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      {==}
    case Con{x, xs} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      %cb_same(x, y) : {Bool.and(Cmd.same(x, y), Cmd.same_path(xs, ys)) == Bool.and(_, Command.cmd_path_eq(xs, ys)) : Bool}
      %cb_same_path(xs, ys) : {Bool.and(Cmd.same(x, y), Cmd.same_path(xs, ys)) == Bool.and(Cmd.same(x, y), _) : Bool}
      {==}

def cb_same_path_eq(+a: List<&2, List<&2, Nat>>, +b: List<&2, List<&2, Nat>>, e: {Cmd.same_path(a, b) == True{} : Bool}) -> {a == b : List<&2, List<&2, Nat>>}:
  cb_path_eq(a, b, Equal.trans(Bool, Command.cmd_path_eq(a, b), Cmd.same_path(a, b), True{}, Equal.sym(Bool, Cmd.same_path(a, b), Command.cmd_path_eq(a, b), cb_same_path(a, b)), e))

def cb_names_app_l(a: List<&2, List<&2, Nat>>, -b: List<&2, List<&2, Nat>>, +h: {Command.cmd_names_ok(List.append(&2, List<&2, Nat>, a, b)) == True{} : Bool}) -> {Command.cmd_names_ok(a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+w, +r}:
      cb_and_intro(Command.cmd_name_ok(w), Command.cmd_names_ok(r), cb_and_l(Command.cmd_name_ok(w), Command.cmd_names_ok(List.append(&2, List<&2, Nat>, r, b)), h), cb_names_app_l(r, b, cb_and_r(Command.cmd_name_ok(w), Command.cmd_names_ok(List.append(&2, List<&2, Nat>, r, b)), h)))

# from q, the names of x <> more walked one by one are declared: so is
# q and all of them
def cb_walks_decl(more: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +h: {Command.cmd_walks.go(x <> more, t, q) == True{} : Bool}) -> {Command.cmd_declared(t, List.append(&2, List<&2, Nat>, q, x <> more)) == True{} : Bool}:
  match more:
    case Nil{}:
      cb_and_l(Command.cmd_declared(t, List.append(&2, List<&2, Nat>, q, [x])), True{}, h)
    case Con{+y, +m2}:
      +qx = List.append(&2, List<&2, Nat>, q, [x])
      %cb_app_assoc(List<&2, Nat>, q, [x], y <> m2) : {Command.cmd_declared(t, _) == True{} : Bool}
      cb_walks_decl(m2, y, t, qx, cb_and_r(Command.cmd_declared(t, qx), Command.cmd_walks.go(y <> m2, t, qx), h))

# a path of the table is declared
def cb_path_decl(+t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, h: {Command.cmd_path(t, q) == True{} : Bool}) -> {Command.cmd_declared(t, q) == True{} : Bool}:
  match q:
    case Nil{}:
      cb_absurd({Command.cmd_declared(t, Nil{}) == True{} : Bool}, h)
    case Con{+x, +rest}:
      cb_walks_decl(rest, x, t, Nil{}, h)

# ---- fit ----

# proof_fit: the laws of a fit, of the summaries along a history, and of
# a compaction's view (LAWS.bend (e), (g)). A fit's merge is sound: best
# picks the first line of a mergeable pair (Has), so each merge drops a
# line and records a built parent; and complete: best finds none only
# when no pair can merge. Summarized survives every step: Info.set only
# adds built nodes, a merge inserts a built parent, a message a leaf.

# Logic
# -----

# a type picked by a Bool: a rewrite through it refutes True == False
def fit.pf.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pf.absurd_tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : fit.pf.BD(_, Unit, A)
  Unit{}

def pf.absurd_ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : fit.pf.BD(_, A, Unit)
  Unit{}

def pf.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      pf.absurd_ft({False{} == True{} : Bool}, e)
    case True{}:
      {==}

def pf.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      pf.absurd_ft({b == True{} : Bool}, e)
    case True{}:
      e

def pf.or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      {==}

# Node equality is reflexive
# --------------------------

def pf.nat_eq_refl(n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pf.nat_eq_refl(p)

def pf.bool_cmp_refl(b: Bool) -> {EQ{} == Bool.cmp(b, b) : Cmp}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def pf.bits_cmp_refl(bs: List<&2, Bool>) -> {EQ{} == O.Bits.cmp(bs, bs) : Cmp}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +r:
      %pf.bits_cmp_refl(r) : {EQ{} == O.Cmp.then(_, Bool.cmp(b, b)) : Cmp}
      pf.bool_cmp_refl(b)

def pf.node_eq_refl(n: O.Node) -> {True{} == O.Node.eq(n, n) : Bool}:
  match n:
    case O.Node{+l, +i}:
      %pf.nat_eq_refl(l) : {True{} == Bool.and(_, O.Bits.same(i, i)) : Bool}
      %pf.bits_cmp_refl(i) : {True{} == Cmp.is_eq(_) : Bool}
      {==}

# ---- agree ----

# proof_agree: push_agrees_always, for every number of pushes. Under push
# alone, Taelin's list is a bijective binary counter: T messages are
# T = sum (1 + d_j)·2^j with digits d_j in {0, 1} (the keep bits, newest
# entry first), and entry j is one line of level j + d_j. pa.GE writes
# push's list and pa.GV the view (that list read oldest first) as
# functions of the digits.
#
# One step appends message T's line, and push adds 1 to the digits. If
# every digit is 1, the list grows and the fit merges nothing. Otherwise
# let j be the lowest 0 digit: push's carry merges the two level-j lines
# j and j-1 (line 0 and the new line when j = 0), and with push's length
# as the budget the fit makes exactly one merge. The due order picks that
# pair:
# - j > 0 (the lowest digit is 1): the view is the view of the higher
#   digits one level up (every line lifted, T + 2 doubled) plus the new
#   line, and the due order between lifted lines is the same (pa.md_lift),
#   so the fit is the lifted fit of the higher digits (pa.fit_lift);
# - j = 0: the pair (line 0, the new line) is due (T + 1 - T)/1 = 1; every
#   older line ends recently enough, in its own line size, to be due less
#   than 1 (pa.Good, pa.old_one), and no later pair can merge (their
#   levels differ).
#
# The arithmetic runs on Nat through Bits.val: the comparisons of the
# model's bit lists are those of their values (pa.cmp_val, pa.val_add).

# Nat
# ---

def pa.succ(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def pa.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pa.succ(Nat.add(p, 0n), p, pa.add_zero(p))

def pa.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pa.succ(Nat.add(p, 1n+b), 1n+Nat.add(p, b), pa.add_succ(p, b))

def pa.add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, pa.add_zero(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p), pa.succ(Nat.add(p, b), Nat.add(b, p), pa.add_comm(p, b)), Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), pa.add_succ(b, p)))

# ---- compactor ----

# proof_compactor: the laws of a compactor call (H1) and of the wait for
# a settled view (H2), for bend/compactor.bend and the need-first queue of
# bend/optchat.bend. Every proof is by induction: on the tries of a line,
# on the outcomes of the settle, on the view of the queue.

# Logic
# -----

def compactor.pc.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pc.absurd_ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : compactor.pc.BD(_, A, Unit)
  Unit{}

def pc.absurd_tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : compactor.pc.BD(_, Unit, A)
  Unit{}

def pc.or_true(a: Bool) -> {Bool.or(True{}, a) == True{} : Bool}:
  {==}

# Numbers
# -------

def compactor.pc.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def compactor.pc.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      compactor.pc.le_refl(p)

def pc.lt_not_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      pc.absurd_ft({True{} == False{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      pc.absurd_ft({True{} == False{} : Bool}, e)
    case 1n+p 1n+q:
      pc.lt_not_le(p, q, e)

# nothing is below 0
def pc.lt_zero(-A: Type, a: Nat, e: {Nat.is_lt(a, 0n) == True{} : Bool}) -> A:
  match a:
    case 0n:
      pc.absurd_ft(A, e)
    case 1n+p:
      pc.absurd_ft(A, e)

def pc.le_succ_r(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n q:
      {==}
    case 1n+p 0n:
      pc.absurd_ft({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_succ_r(p, q, e)

def compactor.pc.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n q r:
      compactor.pc.le_zero(r)
    case 1n+p 0n r:
      pc.absurd_ft({Nat.is_le(1n+p, r) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      pc.absurd_ft({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      compactor.pc.le_trans(p, q, r, ab, bc)

# m <= n + m
def compactor.pc.le_add(n: Nat, +m: Nat) -> {Nat.is_le(m, Nat.add(n, m)) == True{} : Bool}:
  match n:
    case 0n:
      compactor.pc.le_refl(m)
    case 1n+p:
      +q = p
      pc.le_succ_r(m, Nat.add(q, m), compactor.pc.le_add(q, m))

# (H2) The settle
# ---------------

def pc.lt_to_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case p 0n:
      pc.lt_zero({Nat.is_le(p, 0n) == True{} : Bool}, p, e)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      pc.lt_to_le(p, q, e)

def pc.le_lt_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case p q 0n:
      pc.lt_zero({Nat.is_lt(p, 0n) == True{} : Bool}, q, bc)
    case 0n q 1n+r:
      {==}
    case 1n+p 0n 1n+r:
      pc.absurd_ft({Nat.is_lt(1n+p, 1n+r) == True{} : Bool}, ab)
    case 1n+p 1n+q 1n+r:
      pc.le_lt_trans(p, q, r, ab, bc)

# ---- child ----

# proof_child: the H5 laws of LAWS.bend (bend/child.bend, the life of one
# subagent).
#
# - The watch: a quiet poll takes 1 ms or more off the clock (`left`) and
#   a failed one a try (`tries`), so a run of them as long as the clock
#   ends the watch (`stalls_in_time`, `unreachable_in_time`); a clock
#   never grows past its full size (`clock_bounded`); progress sets it
#   back to full (`progress_is_not_a_stall`).
# - The report: an invariant `K` holds after any events: every submission
#   in the parent's inbox but the newest is withdrawn, under an id below
#   it (`Kin`), and the task owes the newest id, or the next one once the
#   newest is withdrawn (`Kowe`). Only the newest may be live, which gives
#   `one_live` and `report_once`; a delivery or withdrawal touches only the
#   newest. From any state that owes the report, a reopen and two task
#   steps (three when an abort mark is pending) leave the report queued
#   under the owed id or placed (`ready`), and a delivery of that id
#   places it (`delivered_once`). A potential (1 plus the withdrawn
#   submissions) bounds the inbox and grows only at a withdrawal
#   (`resubmits_per_abort`).

# Logic
# -----

def child.pc.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def child.pc.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : child.pc.BD(_, A, Unit)
  Unit{}

# Numbers
# -------

def child.pc.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      child.pc.eq_refl(p)

def pc.eq_succ(+a: Nat) -> {Nat.is_eq(1n+a, a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pc.eq_succ(p)

def child.pc.eq_of(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      child.pc.absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      child.pc.absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %child.pc.eq_of(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def child.pc.le_zero(+b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

def child.pc.le_refl(+a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      child.pc.le_refl(p)

def pc.le_succ(+a: Nat, +b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      child.pc.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_succ(p, q, e)

def child.pc.le_trans(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      child.pc.le_zero(c)
    case 1n+p 0n c:
      child.pc.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      child.pc.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      child.pc.le_trans(p, q, r, ab, bc)

def pc.sub_le(+a: Nat, +d: Nat) -> {Nat.is_le(Nat.sub(a, d), a) == True{} : Bool}:
  match a d:
    case 0n d:
      {==}
    case 1n+p 0n:
      child.pc.le_refl(p)
    case 1n+p 1n+e:
      pc.le_succ(Nat.sub(p, e), p, pc.sub_le(p, e))

def child.pc.le_add(+c: Nat, +x: Nat) -> {Nat.is_le(x, Nat.add(c, x)) == True{} : Bool}:
  match c:
    case 0n:
      child.pc.le_refl(x)
    case 1n+p:
      pc.le_succ(x, Nat.add(p, x), child.pc.le_add(p, x))

# The watch
# ---------

# an owed report stays owed through any more polls
def pc.owe_stops(hs: List<&2, Ch.Hush>, +cfg: Ch.Cfg, +k: Ch.Report) -> {Ch.Next.watching(Ch.hush(hs, cfg, Ch.Owe{k})) == False{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case h <> t:
      pc.owe_stops(t, cfg, k)

# the token the watch holds is no progress
def pc.moved_self(+tok: Maybe<&2, Nat>) -> {False{} == Ch.moved(tok, tok) : Bool}:
  match tok:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, child.pc.eq_refl(x)) : {False{} == Bool.not(_) : Bool}
      {==}

# from the clock spend(r, tok, n), quiet polls hs, at least r of them,
# end the watch: each takes 1 ms or more off the r ms left
def pc.stall(hs: List<&2, Ch.Hush>, +cfg: Ch.Cfg, +r: Nat, +tok: Maybe<&2, Nat>, +n: Nat, long: {Nat.is_le(r, List.length(&2, Ch.Hush, hs)) == True{} : Bool}) -> {Ch.Next.watching(Ch.hush(hs, cfg, Ch.spend(r, tok, n))) == False{} : Bool}:
  match hs:
    case Nil{}:
      match r:
        case 0n:
          {==}
        case 1n+p:
          child.pc.absurd({Ch.Next.watching(Ch.hush(Nil{}, cfg, Ch.spend(1n+p, tok, n))) == False{} : Bool}, long)
    case h <> +t:
      match h:
        case Ch.Same{+dt}:
          match r:
            case 0n:
              pc.owe_stops(t, cfg, Ch.Stalled{})
            case 1n+p:
              %pc.moved_self(tok) : {Ch.Next.watching(Ch.hush(t, cfg, Ch.busy(_, cfg, Ch.W{tok, 1n+p, n}, tok, 1n+dt))) == False{} : Bool}
              pc.stall(t, cfg, Nat.sub(p, dt), tok, Ch.Cfg.fails(cfg), child.pc.le_trans(Nat.sub(p, dt), p, List.length(&2, Ch.Hush, t), pc.sub_le(p, dt), long))
        case Ch.Miss{+dt}:
          match r:
            case 0n:
              pc.owe_stops(t, cfg, Ch.Stalled{})
            case 1n+p:
              match n:
                case 0n:
                  pc.owe_stops(t, cfg, Ch.Unreachable{})
                case 1n+q:
                  match q:
                    case 0n:
                      pc.owe_stops(t, cfg, Ch.Unreachable{})
                    case 1n+u:
                      pc.stall(t, cfg, Nat.sub(p, dt), tok, 1n+u, child.pc.le_trans(Nat.sub(p, dt), p, List.length(&2, Ch.Hush, t), pc.sub_le(p, dt), long))

# a clock with nothing left ends at the next quiet poll
def pc.spent(h: Ch.Hush, hs: List<&2, Ch.Hush>, +cfg: Ch.Cfg, +tok: Maybe<&2, Nat>, +n: Nat) -> {Ch.Next.watching(Ch.hush(h <> hs, cfg, Ch.Watch{Ch.W{tok, 0n, n}})) == False{} : Bool}:
  match h:
    case Ch.Same{+dt}:
      %pc.moved_self(tok) : {Ch.Next.watching(Ch.hush(hs, cfg, Ch.busy(_, cfg, Ch.W{tok, 0n, n}, tok, 1n+dt))) == False{} : Bool}
      pc.owe_stops(hs, cfg, Ch.Stalled{})
    case Ch.Miss{+dt}:
      match n:
        case 0n:
          pc.owe_stops(hs, cfg, Ch.Unreachable{})
        case 1n+q:
          match q:
            case 0n:
              pc.owe_stops(hs, cfg, Ch.Unreachable{})
            case 1n+u:
              pc.owe_stops(hs, cfg, Ch.Stalled{})

def pc.stalls_in_time(+cfg: Ch.Cfg, +w: Ch.W, +h: Ch.Hush, +hs: List<&2, Ch.Hush>, long: {Nat.is_le(Ch.W.left(w), List.length(&2, Ch.Hush, h <> hs)) == True{} : Bool}) -> {Ch.Next.watching(Ch.hush(h <> hs, cfg, Ch.Watch{w})) == False{} : Bool}:
  match w:
    case Ch.W{+tok, +l, +n}:
      match l:
        case 0n:
          pc.spent(h, hs, cfg, tok, n)
        case 1n+p:
          pc.stall(h <> hs, cfg, 1n+p, tok, n, long)

def pc.progress_is_not_a_stall(+cfg: Ch.Cfg, +w: Ch.W, +e: Nat, +x: Nat, news: {Ch.moved(Ch.W.tok(w), Some{x}) == True{} : Bool}) -> {Ch.look(cfg, w, e, Ch.Busy{Some{x}}) == Ch.Watch{Ch.W.fresh(cfg, Some{x})} : Ch.Next}:
  %Equal.sym(Bool, Ch.moved(Ch.W.tok(w), Some{x}), True{}, news) : {Ch.busy(_, cfg, w, Some{x}, e) == Ch.Watch{Ch.W.fresh(cfg, Some{x})} : Ch.Next}
  {==}

# j < n and j = n at once
def pc.lt_ne(-A: Type, +j: Nat, +n: Nat, lt: {Nat.is_le(1n+j, n) == True{} : Bool}, eq: {Nat.is_eq(j, n) == True{} : Bool}) -> A:
  match j n:
    case 0n 0n:
      child.pc.absurd(A, lt)
    case 0n 1n+q:
      child.pc.absurd(A, eq)
    case 1n+p 0n:
      child.pc.absurd(A, eq)
    case 1n+p 1n+q:
      pc.lt_ne(A, p, q, lt, eq)

# ---- run ----

# proof_run: the H4 laws of LAWS.bend about bend/run.bend.
#
# - run_ends: an explicit measure M (the inputs a run may still take) falls
#   by at least one at every input to a live run: lexicographically, the
#   rounds left, then the compactions, and the retries and notes left in
#   the generation (one budget u = a + n: each retry, noted or not, spends
#   one of them), the polls left, then the phase (prepare > call >
#   compact; tools ends the generation). M is that order written as one
#   number, in mixed radix, and M at the start is bound(cfg).
# - end_stays, abort_ends_now: by computation on each phase.
# - rounds_capped, rounds_fail_at_cap: invariants of every run and its
#   counted rounds, by induction on its inputs.
# - polls_need_defers: an invariant of the run and its deferred replies in
#   a row, by induction on its inputs.
# - no_answer, calls_never_answer, note_spends_no_retry,
#   retry_spends_no_note: by computation: Ended.reply makes a message with
#   a tool call Calls, whatever its text, and one with no text and no call
#   a noted Error; a noted Error spends a note, any other a retry.

# Logic
# -----

def BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : BD(_, A, Unit)
  Unit{}

def ND(n: Nat, t: Type, f: Type) -> Type:
  match n:
    case 0n:
      t
    case 1n+p:
      f

# 0 is no successor
def zero_succ(-A: Type, -n: Nat, e: {0n == 1n+n : Nat}) -> A:
  %e : ND(_, Unit, A)
  Unit{}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, pred, 1n+a, 1n+b, e)

# Numbers
# -------

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# a + (b + c) = b + (a + c)
def add_lcomm(+a: Nat, +b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  %add_assoc(a, b, c) : {_ == Nat.add(b, Nat.add(a, c)) : Nat}
  %Equal.sym(Nat, Nat.add(a, b), Nat.add(b, a), add_comm(a, b)) : {Nat.add(_, c) == Nat.add(b, Nat.add(a, c)) : Nat}
  add_assoc(b, a, c)

def add_succ_r(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  Equal.sym(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), add_succ(a, b))

def add_assoc_r(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), add_assoc(a, b, c))

# The measure
# -----------
# M(s): the inputs a run may still take from s, at most; 0 once it ended.
# A request takes Q = 2 + polls inputs (its preparation, its reply, its
# polls); a retry (noted or not) one more request; a compaction one input
# and one more request; a generation G inputs, its round's end included.
# u is the retries and notes left, U the retries and notes a generation
# starts with.

def Q(+P: Nat) -> Nat:
  2n+P

# what the compactions c and the retries and notes u left in a generation
# may take
def B(+P: Nat, c: Nat, u: Nat) -> Nat:
  Nat.add(Nat.mul(c, 1n+Q(P)), Nat.mul(u, Q(P)))

# what the generation may still take before its round ends
def gen(+P: Nat, ph: Rn.Ph, c: Nat, u: Nat, p: Nat) -> Nat:
  match ph:
    case Rn.Prepare{}:
      Nat.add(Q(P), B(P, c, u))
    case Rn.Call{}:
      1n+Nat.add(p, B(P, c, u))
    case Rn.Compact{over}:
      1n+Nat.add(Q(P), B(P, c, u))
    case Rn.Tools{}:
      0n
    case Rn.Answered{}:
      0n
    case Rn.Aborted{}:
      0n
    case Rn.Failed{why}:
      0n

def G(+P: Nat, +U: Nat) -> Nat:
  1n+gen(P, Rn.Prepare{}, 1n, U, 0n)

def M.ph(+P: Nat, +U: Nat, ph: Rn.Ph, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> Nat:
  match ph:
    case Rn.Prepare{}:
      Nat.add(gen(P, Rn.Prepare{}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case Rn.Call{}:
      Nat.add(gen(P, Rn.Call{}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case Rn.Compact{over}:
      Nat.add(gen(P, Rn.Compact{over}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case Rn.Tools{}:
      Nat.add(gen(P, Rn.Tools{}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case Rn.Answered{}:
      0n
    case Rn.Aborted{}:
      0n
    case Rn.Failed{why}:
      0n

def M(+cfg: Rn.Cfg, s: Rn.St) -> Nat:
  match cfg s:
    case Rn.Cfg{cap, P, A, N} Rn.St{ph, r, c, a, n, p}:
      M.ph(P, Nat.add(A, N), ph, r, c, Nat.add(a, n), p)

# a fall within the generation is a fall of M
def lift(k: Nat, -gs: Nat, -gt: Nat, -X: Nat, e: {gs == Nat.add(k, 1n+gt) : Nat}) -> {Nat.add(gs, 1n+X) == Nat.add(k, 1n+Nat.add(gt, 1n+X)) : Nat}:
  %Equal.sym(Nat, gs, Nat.add(k, 1n+gt), e) : {Nat.add(_, 1n+X) == Nat.add(k, 1n+Nat.add(gt, 1n+X)) : Nat}
  add_assoc(k, 1n+gt, 1n+X)

# a run that ends takes no more inputs
def to_end(+gs: Nat, +X: Nat) -> {Nat.add(gs, 1n+X) == Nat.add(Nat.add(gs, X), 1n+0n) : Nat}:
  %add_succ_r(Nat.add(gs, X), 0n) : {Nat.add(gs, 1n+X) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(gs, X), 0n), Nat.add(gs, X), add_zero(Nat.add(gs, X))) : {Nat.add(gs, 1n+X) == 1n+_ : Nat}
  add_succ(gs, X)

# Each input
# ----------

# prepare -> compact: the generation's compaction
def prep_compact(+P: Nat, +d: Nat, +u: Nat) -> {gen(P, Rn.Prepare{}, 1n+d, u, 0n) == Nat.add(1n+P, 1n+gen(P, Rn.Compact{False{}}, d, u, 0n)) : Nat}:
  +mD = Nat.mul(d, 1n+Q(P))
  +mU = Nat.mul(u, Q(P))
  %add_assoc_r(1n+Q(P), mD, mU) : {Nat.add(Q(P), _) == Nat.add(1n+P, 1n+gen(P, Rn.Compact{False{}}, d, u, 0n)) : Nat}
  %add_succ_r(P, gen(P, Rn.Compact{False{}}, d, u, 0n)) : {Nat.add(Q(P), Nat.add(1n+Q(P), Nat.add(mD, mU))) == 1n+_ : Nat}
  {==}

# call -> tools: the generation's round starts
def call_tools(+X: Nat) -> {1n+X == Nat.add(X, 1n+0n) : Nat}:
  %add_succ_r(X, 0n) : {1n+X == _ : Nat}
  %add_zero(X) : {1n+_ == 1n+Nat.add(X, 0n) : Nat}
  {==}

# call -> prepare: a retry, noted or not
def call_retry(+P: Nat, +c: Nat, +b: Nat, +p: Nat) -> {gen(P, Rn.Call{}, c, 1n+b, p) == Nat.add(p, 1n+gen(P, Rn.Prepare{}, c, b, 0n)) : Nat}:
  +mC = Nat.mul(c, 1n+Q(P))
  +mb = Nat.mul(b, Q(P))
  %add_succ_r(p, gen(P, Rn.Prepare{}, c, b, 0n)) : {gen(P, Rn.Call{}, c, 1n+b, p) == _ : Nat}
  %add_lcomm(mC, Q(P), mb) : {gen(P, Rn.Call{}, c, 1n+b, p) == 1n+Nat.add(p, _) : Nat}
  {==}

# call -> prepare: a noted retry spends a note, a + (1 + m) = 1 + (a + m)
def call_note(+P: Nat, +c: Nat, +a: Nat, +m: Nat, +p: Nat) -> {gen(P, Rn.Call{}, c, Nat.add(a, 1n+m), p) == Nat.add(p, 1n+gen(P, Rn.Prepare{}, c, Nat.add(a, m), 0n)) : Nat}:
  %add_succ_r(a, m) : {gen(P, Rn.Call{}, c, _, p) == Nat.add(p, 1n+gen(P, Rn.Prepare{}, c, Nat.add(a, m), 0n)) : Nat}
  call_retry(P, c, Nat.add(a, m), p)

# call -> compact: an overflow's compaction
def call_compact(+P: Nat, +d: Nat, +u: Nat, +p: Nat) -> {gen(P, Rn.Call{}, 1n+d, u, p) == Nat.add(p, 1n+gen(P, Rn.Compact{True{}}, d, u, 0n)) : Nat}:
  +mD = Nat.mul(d, 1n+Q(P))
  +mU = Nat.mul(u, Q(P))
  %add_succ_r(p, gen(P, Rn.Compact{True{}}, d, u, 0n)) : {gen(P, Rn.Call{}, 1n+d, u, p) == _ : Nat}
  %add_assoc(1n+Q(P), mD, mU) : {gen(P, Rn.Call{}, 1n+d, u, p) == 1n+Nat.add(p, _) : Nat}
  {==}

# tools -> prepare: the next generation
def next_gen(+gp: Nat, +X: Nat) -> {Nat.add(0n, 1n+Nat.add(1n+gp, X)) == Nat.add(0n, 1n+Nat.add(gp, 1n+X)) : Nat}:
  %add_succ(gp, X) : {1n+_ == 1n+Nat.add(gp, 1n+X) : Nat}
  {==}

# Each phase
# ----------
# For a live run s and any input e, M falls: M(s) = k + 1 + M(step(s, e)),
# with k = K(cfg, s, e). Once a run ends, M is 0.

# M falls from s to t, by k + 1
def Fall(+cfg: Rn.Cfg, s: Rn.St, k: Nat, t: Rn.St) -> Type:
  {M(cfg, s) == Nat.add(k, 1n+M(cfg, t)) : Nat}

def X(+P: Nat, +U: Nat, r: Nat) -> Nat:
  Nat.mul(r, G(P, U))

def K.prepare_cut(+P: Nat, cut: Bool, c: Nat) -> Nat:
  match cut c:
    case True{} 1n+d:
      1n+P
    case True{} 0n:
      0n
    case False{} c:
      0n

def dec_prepare_cut(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(Rn.Cfg{cap, P, A, N}, Rn.St{Rn.Prepare{}, r, c, a, n, p}, K.prepare_cut(P, cut, c), Rn.prepare.cut(Rn.Cfg{cap, P, A, N}, cut, r, c, a, n)):
  match cut c:
    case True{} 1n+d:
      lift(1n+P, gen(P, Rn.Prepare{}, 1n+d, Nat.add(a, n), p), gen(P, Rn.Compact{False{}}, d, Nat.add(a, n), P), X(P, Nat.add(A, N), r), prep_compact(P, d, Nat.add(a, n)))
    case True{} 0n:
      lift(0n, gen(P, Rn.Prepare{}, 0n, Nat.add(a, n), p), gen(P, Rn.Call{}, 0n, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})
    case False{} +c:
      lift(0n, gen(P, Rn.Prepare{}, c, Nat.add(a, n), p), gen(P, Rn.Call{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})

def K.prepare(+P: Nat, reply: Rn.Reply, c: Nat) -> Nat:
  match reply:
    case Rn.Overflow{cut}:
      K.prepare_cut(P, cut, c)
    case Rn.Plain{}:
      0n
    case Rn.Calls{}:
      0n
    case Rn.Deferred{}:
      0n
    case Rn.Error{retryable, noted}:
      0n

def dec_prepare(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: Rn.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(Rn.Cfg{cap, P, A, N}, Rn.St{Rn.Prepare{}, r, c, a, n, p}, K.prepare(P, reply, c), Rn.prepare(Rn.Cfg{cap, P, A, N}, reply, r, c, a, n)):
  match reply:
    case Rn.Overflow{cut}:
      dec_prepare_cut(cap, P, A, N, cut, r, c, a, n, p)
    case Rn.Plain{}:
      lift(0n, gen(P, Rn.Prepare{}, c, Nat.add(a, n), p), gen(P, Rn.Call{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})
    case Rn.Calls{}:
      lift(0n, gen(P, Rn.Prepare{}, c, Nat.add(a, n), p), gen(P, Rn.Call{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})
    case Rn.Deferred{}:
      lift(0n, gen(P, Rn.Prepare{}, c, Nat.add(a, n), p), gen(P, Rn.Call{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})
    case Rn.Error{retryable, noted}:
      lift(0n, gen(P, Rn.Prepare{}, c, Nat.add(a, n), p), gen(P, Rn.Call{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})

# the k of a call that ends the run
def K.call_end(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> Nat:
  Nat.add(gen(P, Rn.Call{}, c, u, p), X(P, U, r))

def call_end(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> {Nat.add(gen(P, Rn.Call{}, c, u, p), 1n+X(P, U, r)) == Nat.add(K.call_end(P, U, r, c, u, p), 1n+0n) : Nat}:
  to_end(gen(P, Rn.Call{}, c, u, p), X(P, U, r))

def K.retry(+P: Nat, +U: Nat, retryable: Bool, +r: Nat, +c: Nat, a: Nat, +n: Nat, +p: Nat) -> Nat:
  match retryable a:
    case True{} 1n+b:
      p
    case True{} 0n:
      K.call_end(P, U, r, c, Nat.add(0n, n), p)
    case False{} +a:
      K.call_end(P, U, r, c, Nat.add(a, n), p)

def dec_retry(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, +r: Nat, +c: Nat, a: Nat, +n: Nat, +p: Nat) -> Fall(Rn.Cfg{cap, P, A, N}, Rn.St{Rn.Call{}, r, c, a, n, p}, K.retry(P, Nat.add(A, N), retryable, r, c, a, n, p), Rn.retry(Rn.Cfg{cap, P, A, N}, retryable, r, c, a, n, p)):
  match retryable a:
    case True{} 1n+b:
      lift(p, gen(P, Rn.Call{}, c, Nat.add(1n+b, n), p), gen(P, Rn.Prepare{}, c, Nat.add(b, n), P), X(P, Nat.add(A, N), r), call_retry(P, c, Nat.add(b, n), p))
    case True{} 0n:
      call_end(P, Nat.add(A, N), r, c, Nat.add(0n, n), p)
    case False{} +a:
      call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), p)

def K.note(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +a: Nat, n: Nat, +p: Nat) -> Nat:
  match n:
    case 1n+m:
      p
    case 0n:
      K.call_end(P, U, r, c, Nat.add(a, 0n), p)

def dec_note(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +r: Nat, +c: Nat, +a: Nat, n: Nat, +p: Nat) -> Fall(Rn.Cfg{cap, P, A, N}, Rn.St{Rn.Call{}, r, c, a, n, p}, K.note(P, Nat.add(A, N), r, c, a, n, p), Rn.note(Rn.Cfg{cap, P, A, N}, r, c, a, n, p)):
  match n:
    case 1n+m:
      lift(p, gen(P, Rn.Call{}, c, Nat.add(a, 1n+m), p), gen(P, Rn.Prepare{}, c, Nat.add(a, m), P), X(P, Nat.add(A, N), r), call_note(P, c, a, m, p))
    case 0n:
      call_end(P, Nat.add(A, N), r, c, Nat.add(a, 0n), p)

def K.error(+P: Nat, +U: Nat, retryable: Bool, noted: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Nat:
  match noted:
    case True{}:
      K.note(P, U, r, c, a, n, p)
    case False{}:
      K.retry(P, U, retryable, r, c, a, n, p)

def dec_error(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, noted: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(Rn.Cfg{cap, P, A, N}, Rn.St{Rn.Call{}, r, c, a, n, p}, K.error(P, Nat.add(A, N), retryable, noted, r, c, a, n, p), Rn.error(Rn.Cfg{cap, P, A, N}, retryable, noted, r, c, a, n, p)):
  match noted:
    case True{}:
      dec_note(cap, P, A, N, r, c, a, n, p)
    case False{}:
      dec_retry(cap, P, A, N, retryable, r, c, a, n, p)

def K.overflow(+P: Nat, +U: Nat, cut: Bool, +r: Nat, c: Nat, +u: Nat, +p: Nat) -> Nat:
  match cut c:
    case True{} 1n+d:
      p
    case True{} 0n:
      K.call_end(P, U, r, 0n, u, p)
    case False{} +c:
      K.call_end(P, U, r, c, u, p)

def dec_overflow(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(Rn.Cfg{cap, P, A, N}, Rn.St{Rn.Call{}, r, c, a, n, p}, K.overflow(P, Nat.add(A, N), cut, r, c, Nat.add(a, n), p), Rn.overflow(cut, r, c, a, n, p)):
  match cut c:
    case True{} 1n+d:
      lift(p, gen(P, Rn.Call{}, 1n+d, Nat.add(a, n), p), gen(P, Rn.Compact{True{}}, d, Nat.add(a, n), p), X(P, Nat.add(A, N), r), call_compact(P, d, Nat.add(a, n), p))
    case True{} 0n:
      call_end(P, Nat.add(A, N), r, 0n, Nat.add(a, n), p)
    case False{} +c:
      call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), p)

def K.deferred(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +u: Nat, p: Nat) -> Nat:
  match p:
    case 0n:
      K.call_end(P, U, r, c, u, 0n)
    case 1n+q:
      0n

def dec_deferred(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +r: Nat, +c: Nat, +a: Nat, +n: Nat, p: Nat) -> Fall(Rn.Cfg{cap, P, A, N}, Rn.St{Rn.Call{}, r, c, a, n, p}, K.deferred(P, Nat.add(A, N), r, c, Nat.add(a, n), p), Rn.call(Rn.Cfg{cap, P, A, N}, Rn.Deferred{}, r, c, a, n, p)):
  match p:
    case 0n:
      call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), 0n)
    case 1n+q:
      lift(0n, gen(P, Rn.Call{}, c, Nat.add(a, n), 1n+q), gen(P, Rn.Call{}, c, Nat.add(a, n), q), X(P, Nat.add(A, N), r), {==})

def K.call(+P: Nat, +U: Nat, reply: Rn.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Nat:
  match reply:
    case Rn.Plain{}:
      K.call_end(P, U, r, c, Nat.add(a, n), p)
    case Rn.Calls{}:
      Nat.add(p, B(P, c, Nat.add(a, n)))
    case Rn.Deferred{}:
      K.deferred(P, U, r, c, Nat.add(a, n), p)
    case Rn.Error{retryable, noted}:
      K.error(P, U, retryable, noted, r, c, a, n, p)
    case Rn.Overflow{cut}:
      K.overflow(P, U, cut, r, c, Nat.add(a, n), p)

def dec_call(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: Rn.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(Rn.Cfg{cap, P, A, N}, Rn.St{Rn.Call{}, r, c, a, n, p}, K.call(P, Nat.add(A, N), reply, r, c, a, n, p), Rn.call(Rn.Cfg{cap, P, A, N}, reply, r, c, a, n, p)):
  match reply:
    case Rn.Plain{}:
      call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), p)
    case Rn.Calls{}:
      lift(Nat.add(p, B(P, c, Nat.add(a, n))), gen(P, Rn.Call{}, c, Nat.add(a, n), p), 0n, X(P, Nat.add(A, N), r), call_tools(Nat.add(p, B(P, c, Nat.add(a, n)))))
    case Rn.Deferred{}:
      dec_deferred(cap, P, A, N, r, c, a, n, p)
    case Rn.Error{retryable, noted}:
      dec_error(cap, P, A, N, retryable, noted, r, c, a, n, p)
    case Rn.Overflow{cut}:
      dec_overflow(cap, P, A, N, cut, r, c, a, n, p)

def K.compact(+P: Nat, +U: Nat, over: Bool, got: Rn.Got, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> Nat:
  match over got:
    case over Rn.Built{}:
      0n
    case True{} Rn.Kept{}:
      Nat.add(gen(P, Rn.Compact{True{}}, c, u, p), X(P, U, r))
    case False{} Rn.Kept{}:
      0n
    case over Rn.Broke{}:
      Nat.add(gen(P, Rn.Compact{over}, c, u, p), X(P, U, r))

def dec_compact(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +over: Bool, got: Rn.Got, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(Rn.Cfg{cap, P, A, N}, Rn.St{Rn.Compact{over}, r, c, a, n, p}, K.compact(P, Nat.add(A, N), over, got, r, c, Nat.add(a, n), p), Rn.compact(Rn.Cfg{cap, P, A, N}, over, got, r, c, a, n, p)):
  match over got:
    case over Rn.Built{}:
      lift(0n, gen(P, Rn.Compact{over}, c, Nat.add(a, n), p), gen(P, Rn.Prepare{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})
    case True{} Rn.Kept{}:
      to_end(gen(P, Rn.Compact{True{}}, c, Nat.add(a, n), p), X(P, Nat.add(A, N), r))
    case False{} Rn.Kept{}:
      lift(0n, gen(P, Rn.Compact{False{}}, c, Nat.add(a, n), p), gen(P, Rn.Prepare{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})
    case over Rn.Broke{}:
      to_end(gen(P, Rn.Compact{over}, c, Nat.add(a, n), p), X(P, Nat.add(A, N), r))

def K.round(+P: Nat, +U: Nat, reset: Bool, r: Nat) -> Nat:
  match reset r:
    case reset 0n:
      Nat.add(0n, X(P, U, 0n))
    case True{} 1n+s:
      Nat.add(0n, X(P, U, 1n+s))
    case False{} 1n+s:
      0n

def dec_round(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reset: Bool, r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(Rn.Cfg{cap, P, A, N}, Rn.St{Rn.Tools{}, r, c, a, n, p}, K.round(P, Nat.add(A, N), reset, r), Rn.round(Rn.Cfg{cap, P, A, N}, reset, r, c, a, n, p)):
  match reset r:
    case reset 0n:
      to_end(0n, X(P, Nat.add(A, N), 0n))
    case True{} 1n+s:
      to_end(0n, X(P, Nat.add(A, N), 1n+s))
    case False{} 1n+s:
      next_gen(gen(P, Rn.Prepare{}, 1n, Nat.add(A, N), 0n), X(P, Nat.add(A, N), s))

def K.tools(+P: Nat, +U: Nat, fin: Rn.Fin, +r: Nat) -> Nat:
  match fin:
    case Rn.Stops{}:
      Nat.add(0n, X(P, U, r))
    case Rn.Goes{}:
      K.round(P, U, False{}, r)
    case Rn.Resets{}:
      K.round(P, U, True{}, r)

def dec_tools(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, fin: Rn.Fin, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(Rn.Cfg{cap, P, A, N}, Rn.St{Rn.Tools{}, r, c, a, n, p}, K.tools(P, Nat.add(A, N), fin, r), Rn.tools(Rn.Cfg{cap, P, A, N}, fin, r, c, a, n, p)):
  match fin:
    case Rn.Stops{}:
      to_end(0n, X(P, Nat.add(A, N), r))
    case Rn.Goes{}:
      dec_round(cap, P, A, N, False{}, r, c, a, n, p)
    case Rn.Resets{}:
      dec_round(cap, P, A, N, True{}, r, c, a, n, p)

# k for any input
def K(+cfg: Rn.Cfg, s: Rn.St, e: Rn.Ev) -> Nat:
  match cfg s:
    case Rn.Cfg{cap, P, A, N} Rn.St{ph, r, c, a, n, p}:
      match ph e:
        case Rn.Answered{} e:
          0n
        case Rn.Aborted{} e:
          0n
        case Rn.Failed{why} e:
          0n
        case Rn.Prepare{} Rn.Abort{}:
          Nat.add(gen(P, Rn.Prepare{}, c, Nat.add(a, n), p), X(P, Nat.add(A, N), r))
        case Rn.Call{} Rn.Abort{}:
          K.call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), p)
        case Rn.Compact{over} Rn.Abort{}:
          Nat.add(gen(P, Rn.Compact{over}, c, Nat.add(a, n), p), X(P, Nat.add(A, N), r))
        case Rn.Tools{} Rn.Abort{}:
          Nat.add(0n, X(P, Nat.add(A, N), r))
        case Rn.Prepare{} Rn.Go{reply, fin, got}:
          K.prepare(P, reply, c)
        case Rn.Call{} Rn.Go{reply, fin, got}:
          K.call(P, Nat.add(A, N), reply, r, c, a, n, p)
        case Rn.Compact{over} Rn.Go{reply, fin, got}:
          K.compact(P, Nat.add(A, N), over, got, r, c, Nat.add(a, n), p)
        case Rn.Tools{} Rn.Go{reply, fin, got}:
          K.tools(P, Nat.add(A, N), fin, r)

# the goal of dec at a phase
def FallAt(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +ph: Rn.Ph, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +e: Rn.Ev) -> Type:
  Fall(Rn.Cfg{cap, P, A, N}, Rn.St{ph, r, c, a, n, p}, K(Rn.Cfg{cap, P, A, N}, Rn.St{ph, r, c, a, n, p}, e), Rn.step(Rn.Cfg{cap, P, A, N}, Rn.St{ph, r, c, a, n, p}, e))

# every input to a live run lowers M
def dec(+cfg: Rn.Cfg, +s: Rn.St, +e: Rn.Ev, nd: {Rn.done(s) == False{} : Bool}) -> Fall(cfg, s, K(cfg, s, e), Rn.step(cfg, s, e)):
  match cfg:
    case Rn.Cfg{cap, P, A, N}:
      match s:
        case Rn.St{ph, r, c, a, n, p}:
          match ph e:
            case Rn.Answered{} e:
              absurd(FallAt(cap, P, A, N, Rn.Answered{}, r, c, a, n, p, e), Equal.sym(Bool, True{}, False{}, nd))
            case Rn.Aborted{} e:
              absurd(FallAt(cap, P, A, N, Rn.Aborted{}, r, c, a, n, p, e), Equal.sym(Bool, True{}, False{}, nd))
            case Rn.Failed{why} e:
              absurd(FallAt(cap, P, A, N, Rn.Failed{why}, r, c, a, n, p, e), Equal.sym(Bool, True{}, False{}, nd))
            case Rn.Prepare{} Rn.Abort{}:
              to_end(gen(P, Rn.Prepare{}, c, Nat.add(a, n), p), X(P, Nat.add(A, N), r))
            case Rn.Call{} Rn.Abort{}:
              call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), p)
            case Rn.Compact{over} Rn.Abort{}:
              to_end(gen(P, Rn.Compact{over}, c, Nat.add(a, n), p), X(P, Nat.add(A, N), r))
            case Rn.Tools{} Rn.Abort{}:
              to_end(0n, X(P, Nat.add(A, N), r))
            case Rn.Prepare{} Rn.Go{reply, fin, got}:
              dec_prepare(cap, P, A, N, reply, r, c, a, n, p)
            case Rn.Call{} Rn.Go{reply, fin, got}:
              dec_call(cap, P, A, N, reply, r, c, a, n, p)
            case Rn.Compact{over} Rn.Go{reply, fin, got}:
              dec_compact(cap, P, A, N, over, got, r, c, a, n, p)
            case Rn.Tools{} Rn.Go{reply, fin, got}:
              dec_tools(cap, P, A, N, fin, r, c, a, n, p)

# The run ends
# ------------

# an ended run stays as it is
def end_stays(+cfg: Rn.Cfg, s: Rn.St, e: Rn.Ev, d: {Rn.done(s) == True{} : Bool}) -> {Rn.step(cfg, s, e) == s : Rn.St}:
  match s:
    case Rn.St{ph, r, c, a, n, p}:
      match ph:
        case Rn.Answered{}:
          {==}
        case Rn.Aborted{}:
          {==}
        case Rn.Failed{why}:
          {==}
        case Rn.Prepare{}:
          absurd({Rn.step(cfg, Rn.St{Rn.Prepare{}, r, c, a, n, p}, e) == Rn.St{Rn.Prepare{}, r, c, a, n, p} : Rn.St}, d)
        case Rn.Call{}:
          absurd({Rn.step(cfg, Rn.St{Rn.Call{}, r, c, a, n, p}, e) == Rn.St{Rn.Call{}, r, c, a, n, p} : Rn.St}, d)
        case Rn.Compact{over}:
          absurd({Rn.step(cfg, Rn.St{Rn.Compact{over}, r, c, a, n, p}, e) == Rn.St{Rn.Compact{over}, r, c, a, n, p} : Rn.St}, d)
        case Rn.Tools{}:
          absurd({Rn.step(cfg, Rn.St{Rn.Tools{}, r, c, a, n, p}, e) == Rn.St{Rn.Tools{}, r, c, a, n, p} : Rn.St}, d)

def stays_done(evs: List<&2, Rn.Ev>, +cfg: Rn.Cfg, +s: Rn.St, +d: {Rn.done(s) == True{} : Bool}) -> {Rn.done(Rn.run.go(evs, cfg, s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      d
    case e <> rest:
      %Equal.sym(Rn.St, Rn.step(cfg, s, e), s, end_stays(cfg, s, e, d)) : {Rn.done(Rn.run.go(rest, cfg, _)) == True{} : Bool}
      stays_done(rest, cfg, s, d)

def succ_m(+j: Nat, +g: Nat, +X: Nat) -> {Nat.add(j, Nat.add(g, 1n+X)) == 1n+Nat.add(j, Nat.add(g, X)) : Nat}:
  %add_succ_r(g, X) : {Nat.add(j, _) == 1n+Nat.add(j, Nat.add(g, X)) : Nat}
  add_succ(j, Nat.add(g, X))

# a live run may still take an input
def pos(-T: Type, +j: Nat, +g: Nat, +X: Nat, h: {0n == Nat.add(j, Nat.add(g, 1n+X)) : Nat}) -> T:
  zero_succ(T, Nat.add(j, Nat.add(g, X)), Equal.trans(Nat, 0n, Nat.add(j, Nat.add(g, 1n+X)), 1n+Nat.add(j, Nat.add(g, X)), h, succ_m(j, g, X)))

# with no input left, the run has ended
def nil_done(+cfg: Rn.Cfg, +s: Rn.St, +j: Nat, h: {0n == Nat.add(j, M(cfg, s)) : Nat}) -> {Rn.done(s) == True{} : Bool}:
  match cfg:
    case Rn.Cfg{cap, P, A, N}:
      match s:
        case Rn.St{ph, r, c, a, n, p}:
          match ph:
            case Rn.Prepare{}:
              pos({Rn.done(Rn.St{Rn.Prepare{}, r, c, a, n, p}) == True{} : Bool}, j, gen(P, Rn.Prepare{}, c, Nat.add(a, n), p), Nat.mul(r, G(P, Nat.add(A, N))), h)
            case Rn.Call{}:
              pos({Rn.done(Rn.St{Rn.Call{}, r, c, a, n, p}) == True{} : Bool}, j, gen(P, Rn.Call{}, c, Nat.add(a, n), p), Nat.mul(r, G(P, Nat.add(A, N))), h)
            case Rn.Compact{over}:
              pos({Rn.done(Rn.St{Rn.Compact{over}, r, c, a, n, p}) == True{} : Bool}, j, gen(P, Rn.Compact{over}, c, Nat.add(a, n), p), Nat.mul(r, G(P, Nat.add(A, N))), h)
            case Rn.Tools{}:
              pos({Rn.done(Rn.St{Rn.Tools{}, r, c, a, n, p}) == True{} : Bool}, j, 0n, Nat.mul(r, G(P, Nat.add(A, N))), h)
            case Rn.Answered{}:
              {==}
            case Rn.Aborted{}:
              {==}
            case Rn.Failed{why}:
              {==}

def next_len1(-n: Nat, +j: Nat, +k: Nat, -ms: Nat, -mt: Nat, h: {1n+n == Nat.add(j, ms) : Nat}, eq: {ms == Nat.add(k, 1n+mt) : Nat}) -> {1n+n == 1n+Nat.add(Nat.add(j, k), mt) : Nat}:
  %add_succ(Nat.add(j, k), mt) : {1n+n == _ : Nat}
  %add_assoc_r(j, k, 1n+mt) : {1n+n == _ : Nat}
  %eq : {1n+n == Nat.add(j, _) : Nat}
  h

# one input later, the inputs left still cover M
def next_len(+cfg: Rn.Cfg, +s: Rn.St, +e: Rn.Ev, +j: Nat, -rest: List<&2, Rn.Ev>, h: {1n+List.length(&2, Rn.Ev, rest) == Nat.add(j, M(cfg, s)) : Nat}, nd: {Rn.done(s) == False{} : Bool}) -> {List.length(&2, Rn.Ev, rest) == Nat.add(Nat.add(j, K(cfg, s, e)), M(cfg, Rn.step(cfg, s, e))) : Nat}:
  succ_inj(List.length(&2, Rn.Ev, rest), Nat.add(Nat.add(j, K(cfg, s, e)), M(cfg, Rn.step(cfg, s, e))), next_len1(List.length(&2, Rn.Ev, rest), j, K(cfg, s, e), M(cfg, s), M(cfg, Rn.step(cfg, s, e)), h, dec(cfg, s, e, nd)))

# a run whose inputs cover M has ended after them
def ends(evs: List<&2, Rn.Ev>, +cfg: Rn.Cfg, +s: Rn.St, +j: Nat, h: {List.length(&2, Rn.Ev, evs) == Nat.add(j, M(cfg, s)) : Nat}) -> {Rn.done(Rn.run.go(evs, cfg, s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      nil_done(cfg, s, j, h)
    case +e <> rest:
      match s:
        case Rn.St{ph, r, c, a, n, p}:
          match ph:
            case Rn.Prepare{}:
              +t = {Rn.St{Rn.Prepare{}, r, c, a, n, p} : Rn.St}
              ends(rest, cfg, Rn.step(cfg, t, e), Nat.add(j, K(cfg, t, e)), next_len(cfg, t, e, j, rest, h, {==}))
            case Rn.Call{}:
              +t = {Rn.St{Rn.Call{}, r, c, a, n, p} : Rn.St}
              ends(rest, cfg, Rn.step(cfg, t, e), Nat.add(j, K(cfg, t, e)), next_len(cfg, t, e, j, rest, h, {==}))
            case Rn.Compact{over}:
              +t = {Rn.St{Rn.Compact{over}, r, c, a, n, p} : Rn.St}
              ends(rest, cfg, Rn.step(cfg, t, e), Nat.add(j, K(cfg, t, e)), next_len(cfg, t, e, j, rest, h, {==}))
            case Rn.Tools{}:
              +t = {Rn.St{Rn.Tools{}, r, c, a, n, p} : Rn.St}
              ends(rest, cfg, Rn.step(cfg, t, e), Nat.add(j, K(cfg, t, e)), next_len(cfg, t, e, j, rest, h, {==}))
            case Rn.Answered{}:
              stays_done(rest, cfg, Rn.St{Rn.Answered{}, r, c, a, n, p}, {==})
            case Rn.Aborted{}:
              stays_done(rest, cfg, Rn.St{Rn.Aborted{}, r, c, a, n, p}, {==})
            case Rn.Failed{why}:
              stays_done(rest, cfg, Rn.St{Rn.Failed{why}, r, c, a, n, p}, {==})

# ---- tree ----

# proof_tree: the session tree laws of LAWS.bend (S1), about bend/tree.bend.
#
# Lookups first: a set or an unset changes only the lookup of its own key
# (`pt.get_set_*`, `pt.get_unset_*`), and both keep a tree sorted. A put
# keeps every parent (`pt.ok_set`); a delete keeps the parent of every
# node it keeps (`pt.rooted_prune_go`, by the nodes walked so far: kept,
# or with their key gone). So every record keeps a tree sound
# (`apply_sound`). A rewind's lookup at a key follows its ops on that key
# (`pt.look`); so after diff(a, b) the tree agrees with b on every key,
# and two sorted trees that agree are equal (`pt.ext`). A delete of the
# root (key 0) changes nothing, and no node of a rooted tree is the root
# (`pt.rooted_nz`); a delete of a node removes it and its subtree only.

# Logic
# -----

def tree.pt.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pt.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : tree.pt.BD(_, Unit, A)
  Unit{}

def tree.pt.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : tree.pt.BD(_, A, Unit)
  Unit{}

def tree.pt.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      tree.pt.absurdF({False{} == True{} : Bool}, h)

def tree.pt.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      tree.pt.absurdF({b == True{} : Bool}, h)

def tree.pt.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pt.eq_comm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pt.eq_comm(p, q)

def pt.ne_comm(+a: Nat, +b: Nat, h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  %pt.eq_comm(a, b) : {_ == False{} : Bool}
  h

def pt.lt_irrefl(k: Nat) -> {Nat.is_lt(k, k) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pt.lt_irrefl(p)

# a key below another is not it
def pt.lt_ne(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case _ 0n:
      tree.pt.absurdF({Nat.is_eq(a, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      pt.lt_ne(p, q, h)

def pt.lt_ne_r(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  pt.ne_comm(a, b, pt.lt_ne(a, b, h))

def pt.not_f(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      tree.pt.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pt.not_t(+b: Bool, h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

def pt.lt_zero(-A: Type, p: Nat, lt: {Nat.is_lt(p, 0n) == True{} : Bool}) -> A:
  match p:
    case 0n:
      tree.pt.absurdF(A, lt)
    case 1n+q:
      tree.pt.absurdF(A, lt)

# Numbers

def tc.lt_le(a: Nat, b: Nat, c: Nat, +ab: {Nat.is_lt(a, b) == True{} : Bool}, +cb: {Nat.is_lt(c, b) == False{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      tree.pt.absurdF({Nat.is_lt(a, c) == True{} : Bool}, ab)
    case _ 1n+q 0n:
      pt.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, cb)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      tc.lt_le(p, q, r, ab, cb)

def tc.lt_asym(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case _ 0n:
      tree.pt.absurdF({Nat.is_lt(0n, a) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      tc.lt_asym(p, q, h)

def tc.lt_total(a: Nat, b: Nat, +nl: {Nat.is_lt(a, b) == False{} : Bool}, +ne: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      pt.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ne)
    case 0n 1n+q:
      pt.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, nl)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      tc.lt_total(p, q, nl, ne)

def tc.cmp_lt(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.cmp(a, b) == LT{} : Cmp}:
  match a b:
    case _ 0n:
      tree.pt.absurdF({Nat.cmp(a, 0n) == LT{} : Cmp}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      tc.cmp_lt(p, q, h)

def tc.cmp_gt(a: Nat, b: Nat, +h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.cmp(a, b) == GT{} : Cmp}:
  match a b:
    case 0n 0n:
      tree.pt.absurdF({Nat.cmp(0n, 0n) == GT{} : Cmp}, h)
    case 0n 1n+q:
      tree.pt.absurdF({Nat.cmp(0n, 1n+q) == GT{} : Cmp}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      tc.cmp_gt(p, q, h)

def tc.cmp_eq(a: Nat, b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {Nat.cmp(a, b) == EQ{} : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      tree.pt.absurdF({Nat.cmp(0n, 1n+q) == EQ{} : Cmp}, h)
    case 1n+p 0n:
      tree.pt.absurdF({Nat.cmp(1n+p, 0n) == EQ{} : Cmp}, h)
    case 1n+p 1n+q:
      tc.cmp_eq(p, q, h)

# Bounds

# every key of t is below b
def tc.lt(t: List<&2, Tr.Ent>, +b: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> r:
      Bool.and(Nat.is_lt(Tr.Ent.k(e), b), tc.lt(r, b))

# every key of t is b or more
def tc.ge(t: List<&2, Tr.Ent>, +b: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> r:
      Bool.and(Bool.not(Nat.is_lt(Tr.Ent.k(e), b)), tc.ge(r, b))

# a fork's left keys are below its split, its right keys at or above it
def tc.bst(m: Tr.KMap) -> Bool:
  match m:
    case Tr.KNil{}:
      True{}
    case Tr.KOne{e}:
      True{}
    case Tr.KFork{+mid, +mp, +l, +r}:
      Bool.and(tc.bst(l), Bool.and(tc.bst(r), Bool.and(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid))))

def tc.bst_l(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {tc.bst(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {tc.bst(l) == True{} : Bool}:
  tree.pt.and_l(tc.bst(l), Bool.and(tc.bst(r), Bool.and(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid))), h)

def tc.bst_rest(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {tc.bst(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {Bool.and(tc.bst(r), Bool.and(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid))) == True{} : Bool}:
  tree.pt.and_r(tc.bst(l), Bool.and(tc.bst(r), Bool.and(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid))), h)

def tc.bst_r(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {tc.bst(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {tc.bst(r) == True{} : Bool}:
  tree.pt.and_l(tc.bst(r), Bool.and(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid)), tc.bst_rest(mid, mp, l, r, h))

def tc.bst_lt(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {tc.bst(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {tc.lt(Tr.KMap.read(l), mid) == True{} : Bool}:
  +h2 = tree.pt.and_r(tc.bst(r), Bool.and(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid)), tc.bst_rest(mid, mp, l, r, h))
  tree.pt.and_l(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid), h2)

def tc.bst_ge(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {tc.bst(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {tc.ge(Tr.KMap.read(r), mid) == True{} : Bool}:
  +h2 = tree.pt.and_r(tc.bst(r), Bool.and(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid)), tc.bst_rest(mid, mp, l, r, h))
  tree.pt.and_r(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid), h2)

def tc.bst_fork(+mid: Nat, +l: Tr.KMap, +r: Tr.KMap, +bl: {tc.bst(l) == True{} : Bool}, +br: {tc.bst(r) == True{} : Bool}, +ll: {tc.lt(Tr.KMap.read(l), mid) == True{} : Bool}, +gr: {tc.ge(Tr.KMap.read(r), mid) == True{} : Bool}) -> {tc.bst(Tr.KMap.fork(mid, l, r)) == True{} : Bool}:
  tree.pt.and_t(tc.bst(l), Bool.and(tc.bst(r), Bool.and(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid))), bl, tree.pt.and_t(tc.bst(r), Bool.and(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid)), br, tree.pt.and_t(tc.lt(Tr.KMap.read(l), mid), tc.ge(Tr.KMap.read(r), mid), ll, gr)))

def tc.lt_head(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {tc.lt(e <> r, b) == True{} : Bool}) -> {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}:
  tree.pt.and_l(Nat.is_lt(Tr.Ent.k(e), b), tc.lt(r, b), h)

def tc.lt_tail(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {tc.lt(e <> r, b) == True{} : Bool}) -> {tc.lt(r, b) == True{} : Bool}:
  tree.pt.and_r(Nat.is_lt(Tr.Ent.k(e), b), tc.lt(r, b), h)

def tc.ge_head(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {tc.ge(e <> r, b) == True{} : Bool}) -> {Nat.is_lt(Tr.Ent.k(e), b) == False{} : Bool}:
  pt.not_f(Nat.is_lt(Tr.Ent.k(e), b), tree.pt.and_l(Bool.not(Nat.is_lt(Tr.Ent.k(e), b)), tc.ge(r, b), h))

def tc.ge_tail(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {tc.ge(e <> r, b) == True{} : Bool}) -> {tc.ge(r, b) == True{} : Bool}:
  tree.pt.and_r(Bool.not(Nat.is_lt(Tr.Ent.k(e), b)), tc.ge(r, b), h)

def tc.lt_cons(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}, +t: {tc.lt(r, b) == True{} : Bool}) -> {tc.lt(e <> r, b) == True{} : Bool}:
  tree.pt.and_t(Nat.is_lt(Tr.Ent.k(e), b), tc.lt(r, b), h, t)

def tc.ge_cons(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {Nat.is_lt(Tr.Ent.k(e), b) == False{} : Bool}, +t: {tc.ge(r, b) == True{} : Bool}) -> {tc.ge(e <> r, b) == True{} : Bool}:
  tree.pt.and_t(Bool.not(Nat.is_lt(Tr.Ent.k(e), b)), tc.ge(r, b), pt.not_t(Nat.is_lt(Tr.Ent.k(e), b), h), t)

# Lists

def tc.app_nil(xs: List<&2, Tr.Ent>) -> {List.append(&2, Tr.Ent, xs, Nil{}) == xs : List<&2, Tr.Ent>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => h <> ys, List.append(&2, Tr.Ent, t, Nil{}), t, tc.app_nil(t))

# a key at or above b is no key of a list below b
def tc.lt_miss(+e: Tr.Ent, +b: Nat, +x: Nat, +lk: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == False{} : Bool}) -> {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}:
  pt.lt_ne(Tr.Ent.k(e), x, tc.lt_le(Tr.Ent.k(e), b, x, lk, xb))

# a key below b is no key of a list at or above b
def tc.ge_miss(+e: Tr.Ent, +b: Nat, +x: Nat, +ge: {Nat.is_lt(Tr.Ent.k(e), b) == False{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}:
  pt.lt_ne_r(x, Tr.Ent.k(e), tc.lt_le(x, b, Tr.Ent.k(e), xb, ge))

# the first key test of a list before a list above the key
def tc.first_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +e: Tr.Ent, +gb: {tc.ge(B, b) == True{} : Bool}, +eb: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}) -> {Tr.first(Tr.Ent.k(e), List.append(&2, Tr.Ent, A, B)) == Tr.first(Tr.Ent.k(e), A) : Cmp}:
  match A:
    case Nil{}:
      match B:
        case Nil{}:
          {==}
        case +f <> s:
          tc.cmp_lt(Tr.Ent.k(e), Tr.Ent.k(f), tc.lt_le(Tr.Ent.k(e), b, Tr.Ent.k(f), eb, tc.ge_head(f, s, b, gb)))
    case a <> r:
      {==}

def tc.set_go_lt(B: List<&2, Tr.Ent>, +e: Tr.Ent) -> {Tr.set.go(B, e, LT{}) == e <> B : List<&2, Tr.Ent>}:
  match B:
    case Nil{}:
      {==}
    case f <> s:
      {==}

def tc.set_go_app_l(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +e: Tr.Ent, c: Cmp, +ec: {Tr.first(Tr.Ent.k(e), A) == c : Cmp}, +gb: {tc.ge(B, b) == True{} : Bool}, +eb: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}) -> {Tr.set.go(List.append(&2, Tr.Ent, A, B), e, c) == List.append(&2, Tr.Ent, Tr.set.go(A, e, c), B) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      %ec : {Tr.set.go(B, e, _) == List.append(&2, Tr.Ent, Tr.set.go(Nil{}, e, _), B) : List<&2, Tr.Ent>}
      tc.set_go_lt(B, e)
    case +a <> +r:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          +R = List.append(&2, Tr.Ent, r, B)
          %Equal.sym(Cmp, Tr.first(Tr.Ent.k(e), List.append(&2, Tr.Ent, r, B)), Tr.first(Tr.Ent.k(e), r), tc.first_app(r, B, b, e, gb, eb)) : {a <> Tr.set.go(R, e, _) == List.append(&2, Tr.Ent, a <> Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r)), B) : List<&2, Tr.Ent>}
          Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => a <> ys, Tr.set.go(R, e, Tr.first(Tr.Ent.k(e), r)), List.append(&2, Tr.Ent, Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r)), B), tc.set_go_app_l(r, B, b, e, Tr.first(Tr.Ent.k(e), r), {==}, gb, eb))

# a set below a bound sets the part below it
def tc.set_app_l(+A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +e: Tr.Ent, +gb: {tc.ge(B, b) == True{} : Bool}, +eb: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}) -> {Tr.set(List.append(&2, Tr.Ent, A, B), e) == List.append(&2, Tr.Ent, Tr.set(A, e), B) : List<&2, Tr.Ent>}:
  %Equal.sym(Cmp, Tr.first(Tr.Ent.k(e), List.append(&2, Tr.Ent, A, B)), Tr.first(Tr.Ent.k(e), A), tc.first_app(A, B, b, e, gb, eb)) : {Tr.set.go(List.append(&2, Tr.Ent, A, B), e, _) == List.append(&2, Tr.Ent, Tr.set(A, e), B) : List<&2, Tr.Ent>}
  tc.set_go_app_l(A, B, b, e, Tr.first(Tr.Ent.k(e), A), {==}, gb, eb)

# a set at or above a bound sets the part above it
def tc.set_app_r(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +e: Tr.Ent, +la: {tc.lt(A, b) == True{} : Bool}, +eb: {Nat.is_lt(Tr.Ent.k(e), b) == False{} : Bool}) -> {Tr.set(List.append(&2, Tr.Ent, A, B), e) == List.append(&2, Tr.Ent, A, Tr.set(B, e)) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +R = List.append(&2, Tr.Ent, r, B)
      +gt = tc.cmp_gt(Tr.Ent.k(e), Tr.Ent.k(a), tc.lt_le(Tr.Ent.k(a), b, Tr.Ent.k(e), tc.lt_head(a, r, b, la), eb))
      %Equal.sym(Cmp, Nat.cmp(Tr.Ent.k(e), Tr.Ent.k(a)), GT{}, gt) : {Tr.set.go(a <> R, e, _) == a <> List.append(&2, Tr.Ent, r, Tr.set(B, e)) : List<&2, Tr.Ent>}
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => a <> ys, Tr.set(R, e), List.append(&2, Tr.Ent, r, Tr.set(B, e)), tc.set_app_r(r, B, b, e, tc.lt_tail(a, r, b, la), eb))

# an unset of a key at or above a bound unsets the part above it
def tc.unset_app_r(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +la: {tc.lt(A, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == False{} : Bool}) -> {Tr.unset(List.append(&2, Tr.Ent, A, B), x) == List.append(&2, Tr.Ent, A, Tr.unset(B, x)) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +R = List.append(&2, Tr.Ent, r, B)
      +ne = tc.lt_miss(a, b, x, tc.lt_head(a, r, b, la), xb)
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(a), x), False{}, ne) : {Tr.unset.go(a <> R, x, _) == a <> List.append(&2, Tr.Ent, r, Tr.unset(B, x)) : List<&2, Tr.Ent>}
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => a <> ys, Tr.unset(R, x), List.append(&2, Tr.Ent, r, Tr.unset(B, x)), tc.unset_app_r(r, B, b, x, tc.lt_tail(a, r, b, la), xb))

# an unset of a key below every key changes nothing
def tc.unset_miss(B: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +gb: {tc.ge(B, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {Tr.unset(B, x) == B : List<&2, Tr.Ent>}:
  match B:
    case Nil{}:
      {==}
    case +f <> +r:
      +ne = tc.ge_miss(f, b, x, tc.ge_head(f, r, b, gb), xb)
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(f), x), False{}, ne) : {Tr.unset.go(f <> r, x, _) == f <> r : List<&2, Tr.Ent>}
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => f <> ys, Tr.unset(r, x), r, tc.unset_miss(r, b, x, tc.ge_tail(f, r, b, gb), xb))

def tc.unset_step(+a: Tr.Ent, +r: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +x: Nat, c: Bool, +ih: {Tr.unset(List.append(&2, Tr.Ent, r, B), x) == List.append(&2, Tr.Ent, Tr.unset(r, x), B) : List<&2, Tr.Ent>}) -> {Tr.unset.go(a <> List.append(&2, Tr.Ent, r, B), x, c) == List.append(&2, Tr.Ent, Tr.unset.go(a <> r, x, c), B) : List<&2, Tr.Ent>}:
  match c:
    case True{}:
      ih
    case False{}:
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => a <> ys, Tr.unset(List.append(&2, Tr.Ent, r, B), x), List.append(&2, Tr.Ent, Tr.unset(r, x), B), ih)

# an unset of a key below a bound unsets the part below it
def tc.unset_app_l(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +gb: {tc.ge(B, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {Tr.unset(List.append(&2, Tr.Ent, A, B), x) == List.append(&2, Tr.Ent, Tr.unset(A, x), B) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      tc.unset_miss(B, b, x, gb, xb)
    case +a <> +r:
      tc.unset_step(a, r, B, x, Nat.is_eq(Tr.Ent.k(a), x), tc.unset_app_l(r, B, b, x, gb, xb))

# bounds over set and unset

def tc.lt_set(t: List<&2, Tr.Ent>, +e: Tr.Ent, c: Cmp, +b: Nat, +lt: {tc.lt(t, b) == True{} : Bool}, +eb: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}) -> {tc.lt(Tr.set.go(t, e, c), b) == True{} : Bool}:
  match t:
    case Nil{}:
      tc.lt_cons(e, Nil{}, b, eb, {==})
    case +h <> +r:
      match c:
        case LT{}:
          tc.lt_cons(e, h <> r, b, eb, lt)
        case EQ{}:
          tc.lt_cons(e, r, b, eb, tc.lt_tail(h, r, b, lt))
        case GT{}:
          tc.lt_cons(h, Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r)), b, tc.lt_head(h, r, b, lt), tc.lt_set(r, e, Tr.first(Tr.Ent.k(e), r), b, tc.lt_tail(h, r, b, lt), eb))

def tc.ge_set(t: List<&2, Tr.Ent>, +e: Tr.Ent, c: Cmp, +b: Nat, +ge: {tc.ge(t, b) == True{} : Bool}, +eb: {Nat.is_lt(Tr.Ent.k(e), b) == False{} : Bool}) -> {tc.ge(Tr.set.go(t, e, c), b) == True{} : Bool}:
  match t:
    case Nil{}:
      tc.ge_cons(e, Nil{}, b, eb, {==})
    case +h <> +r:
      match c:
        case LT{}:
          tc.ge_cons(e, h <> r, b, eb, ge)
        case EQ{}:
          tc.ge_cons(e, r, b, eb, tc.ge_tail(h, r, b, ge))
        case GT{}:
          tc.ge_cons(h, Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r)), b, tc.ge_head(h, r, b, ge), tc.ge_set(r, e, Tr.first(Tr.Ent.k(e), r), b, tc.ge_tail(h, r, b, ge), eb))

def tc.lt_unset(t: List<&2, Tr.Ent>, +x: Nat, hit: Bool, +b: Nat, +lt: {tc.lt(t, b) == True{} : Bool}) -> {tc.lt(Tr.unset.go(t, x, hit), b) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          tc.lt_unset(r, x, Tr.key.at(r, x), b, tc.lt_tail(h, r, b, lt))
        case False{}:
          tc.lt_cons(h, Tr.unset.go(r, x, Tr.key.at(r, x)), b, tc.lt_head(h, r, b, lt), tc.lt_unset(r, x, Tr.key.at(r, x), b, tc.lt_tail(h, r, b, lt)))

def tc.ge_unset(t: List<&2, Tr.Ent>, +x: Nat, hit: Bool, +b: Nat, +ge: {tc.ge(t, b) == True{} : Bool}) -> {tc.ge(Tr.unset.go(t, x, hit), b) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          tc.ge_unset(r, x, Tr.key.at(r, x), b, tc.ge_tail(h, r, b, ge))
        case False{}:
          tc.ge_cons(h, Tr.unset.go(r, x, Tr.key.at(r, x)), b, tc.ge_head(h, r, b, ge), tc.ge_unset(r, x, Tr.key.at(r, x), b, tc.ge_tail(h, r, b, ge)))

# Two nodes

# a and b in the order of the test lt
def tc.pair(lt: Bool, +a: Tr.Ent, +b: Tr.Ent) -> List<&2, Tr.Ent>:
  match lt:
    case True{}:
      [a, b]
    case False{}:
      [b, a]

def tc.pair_lt(c: Bool, +a: Tr.Ent, +b: Tr.Ent, +B: Nat, +ha: {Nat.is_lt(Tr.Ent.k(a), B) == True{} : Bool}, +hb: {Nat.is_lt(Tr.Ent.k(b), B) == True{} : Bool}) -> {tc.lt(tc.pair(c, a, b), B) == True{} : Bool}:
  match c:
    case True{}:
      tc.lt_cons(a, [b], B, ha, tc.lt_cons(b, Nil{}, B, hb, {==}))
    case False{}:
      tc.lt_cons(b, [a], B, hb, tc.lt_cons(a, Nil{}, B, ha, {==}))

def tc.pair_ge(c: Bool, +a: Tr.Ent, +b: Tr.Ent, +B: Nat, +ha: {Nat.is_lt(Tr.Ent.k(a), B) == False{} : Bool}, +hb: {Nat.is_lt(Tr.Ent.k(b), B) == False{} : Bool}) -> {tc.ge(tc.pair(c, a, b), B) == True{} : Bool}:
  match c:
    case True{}:
      tc.ge_cons(a, [b], B, ha, tc.ge_cons(b, Nil{}, B, hb, {==}))
    case False{}:
      tc.ge_cons(b, [a], B, hb, tc.ge_cons(a, Nil{}, B, ha, {==}))

def tc.split_read(+a: Tr.Ent, +b: Tr.Ent, c: Bool) -> {Tr.KMap.read(Tr.KMap.split(a, b, c)) == tc.pair(c, a, b) : List<&2, Tr.Ent>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def tc.split_bst(+a: Tr.Ent, +b: Tr.Ent, c: Bool, +ec: {Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)) == c : Bool}, +ne: {Nat.is_eq(Tr.Ent.k(a), Tr.Ent.k(b)) == False{} : Bool}) -> {tc.bst(Tr.KMap.split(a, b, c)) == True{} : Bool}:
  match c:
    case True{}:
      tc.bst_fork(Tr.Ent.k(b), Tr.KOne{a}, Tr.KOne{b}, {==}, {==}, tc.lt_cons(a, Nil{}, Tr.Ent.k(b), ec, {==}), tc.ge_cons(b, Nil{}, Tr.Ent.k(b), pt.lt_irrefl(Tr.Ent.k(b)), {==}))
    case False{}:
      +ba = tc.lt_total(Tr.Ent.k(a), Tr.Ent.k(b), ec, ne)
      tc.bst_fork(Tr.Ent.k(a), Tr.KOne{b}, Tr.KOne{a}, {==}, {==}, tc.lt_cons(b, Nil{}, Tr.Ent.k(a), ba, {==}), tc.ge_cons(a, Nil{}, Tr.Ent.k(a), pt.lt_irrefl(Tr.Ent.k(a)), {==}))

def tc.two_read(hs: List<&2, Nat>, +lo: Nat, +a: Tr.Ent, +b: Tr.Ent, ca: Bool, cb: Bool, +eca: {Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, Tr.KMap.half(hs))) == ca : Bool}, +ecb: {Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, Tr.KMap.half(hs))) == cb : Bool}) -> {Tr.KMap.read(Tr.KMap.two(hs, lo, a, b, ca, cb)) == tc.pair(Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), a, b) : List<&2, Tr.Ent>}:
  match hs:
    case Nil{}:
      tc.split_read(a, b, Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)))
    case +h <> +rest:
      match ca cb:
        case True{} True{}:
          +g = Tr.KMap.half(rest)
          +X = Tr.KMap.two(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g)))
          Equal.trans(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, Tr.KMap.read(X), Nil{}), Tr.KMap.read(X), tc.pair(Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), a, b), tc.app_nil(Tr.KMap.read(X)), tc.two_read(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g)), {==}, {==}))
        case True{} False{}:
          +lt = tc.lt_le(Tr.Ent.k(a), Nat.add(lo, h), Tr.Ent.k(b), eca, ecb)
          %Equal.sym(Bool, Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), True{}, lt) : {[a, b] == tc.pair(_, a, b) : List<&2, Tr.Ent>}
          {==}
        case False{} True{}:
          +ba = tc.lt_le(Tr.Ent.k(b), Nat.add(lo, h), Tr.Ent.k(a), ecb, eca)
          +nab = tc.lt_asym(Tr.Ent.k(b), Tr.Ent.k(a), ba)
          %Equal.sym(Bool, Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), False{}, nab) : {[b, a] == tc.pair(_, a, b) : List<&2, Tr.Ent>}
          {==}
        case False{} False{}:
          +g = Tr.KMap.half(rest)
          +n = Nat.add(lo, h)
          tc.two_read(rest, n, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(n, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(n, g)), {==}, {==})

def tc.two_bst(hs: List<&2, Nat>, +lo: Nat, +a: Tr.Ent, +b: Tr.Ent, ca: Bool, cb: Bool, +eca: {Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, Tr.KMap.half(hs))) == ca : Bool}, +ecb: {Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, Tr.KMap.half(hs))) == cb : Bool}, +ne: {Nat.is_eq(Tr.Ent.k(a), Tr.Ent.k(b)) == False{} : Bool}) -> {tc.bst(Tr.KMap.two(hs, lo, a, b, ca, cb)) == True{} : Bool}:
  match hs:
    case Nil{}:
      tc.split_bst(a, b, Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), {==}, ne)
    case +h <> +rest:
      match ca cb:
        case True{} True{}:
          +g = Tr.KMap.half(rest)
          +X = Tr.KMap.two(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g)))
          +rx = tc.two_read(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g)), {==}, {==})
          +lx = tc.pair_lt(Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), a, b, Nat.add(lo, h), eca, ecb)
          +P = tc.pair(Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), a, b)
          +ll = Equal.trans(Bool, tc.lt(Tr.KMap.read(X), Nat.add(lo, h)), tc.lt(P, Nat.add(lo, h)), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, y => tc.lt(y, Nat.add(lo, h)), Tr.KMap.read(X), P, rx), lx)
          tc.bst_fork(Nat.add(lo, h), X, Tr.KNil{}, tc.two_bst(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g)), {==}, {==}, ne), {==}, ll, {==})
        case True{} False{}:
          tc.bst_fork(Nat.add(lo, h), Tr.KOne{a}, Tr.KOne{b}, {==}, {==}, tc.lt_cons(a, Nil{}, Nat.add(lo, h), eca, {==}), tc.ge_cons(b, Nil{}, Nat.add(lo, h), ecb, {==}))
        case False{} True{}:
          tc.bst_fork(Nat.add(lo, h), Tr.KOne{b}, Tr.KOne{a}, {==}, {==}, tc.lt_cons(b, Nil{}, Nat.add(lo, h), ecb, {==}), tc.ge_cons(a, Nil{}, Nat.add(lo, h), eca, {==}))
        case False{} False{}:
          +g = Tr.KMap.half(rest)
          +n = Nat.add(lo, h)
          +X = Tr.KMap.two(rest, n, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(n, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(n, g)))
          +rx = tc.two_read(rest, n, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(n, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(n, g)), {==}, {==})
          +gx = tc.pair_ge(Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), a, b, n, eca, ecb)
          +P = tc.pair(Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), a, b)
          +gg = Equal.trans(Bool, tc.ge(Tr.KMap.read(X), n), tc.ge(P, n), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, y => tc.ge(y, n), Tr.KMap.read(X), P, rx), gx)
          tc.bst_fork(n, Tr.KNil{}, X, {==}, tc.two_bst(rest, n, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(n, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(n, g)), {==}, {==}, ne), {==}, gg)

def tc.set_one(+f: Tr.Ent, +e: Tr.Ent, c: Bool, +ec: {Nat.is_lt(Tr.Ent.k(f), Tr.Ent.k(e)) == c : Bool}, +ne: {Nat.is_eq(Tr.Ent.k(f), Tr.Ent.k(e)) == False{} : Bool}) -> {Tr.set([f], e) == tc.pair(c, f, e) : List<&2, Tr.Ent>}:
  match c:
    case True{}:
      +gt = tc.cmp_gt(Tr.Ent.k(e), Tr.Ent.k(f), ec)
      %Equal.sym(Cmp, Nat.cmp(Tr.Ent.k(e), Tr.Ent.k(f)), GT{}, gt) : {Tr.set.go([f], e, _) == [f, e] : List<&2, Tr.Ent>}
      {==}
    case False{}:
      +lt = tc.cmp_lt(Tr.Ent.k(e), Tr.Ent.k(f), tc.lt_total(Tr.Ent.k(f), Tr.Ent.k(e), ec, ne))
      %Equal.sym(Cmp, Nat.cmp(Tr.Ent.k(e), Tr.Ent.k(f)), LT{}, lt) : {Tr.set.go([f], e, _) == [e, f] : List<&2, Tr.Ent>}
      {==}

def tc.put_read(m: Tr.KMap, +hs: List<&2, Nat>, +lo: Nat, +e: Tr.Ent, b: Bool, +eb: {Tr.KMap.at(m, Tr.Ent.k(e)) == b : Bool}, +bt: {tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.put(m, hs, lo, e, b)) == Tr.set(Tr.KMap.read(m), e) : List<&2, Tr.Ent>}:
  match m b:
    case Tr.KNil{} True{}:
      {==}
    case Tr.KNil{} False{}:
      {==}
    case Tr.KOne{+f} True{}:
      +eq = Equal.trans(Bool, Nat.is_eq(Tr.Ent.k(e), Tr.Ent.k(f)), Nat.is_eq(Tr.Ent.k(f), Tr.Ent.k(e)), True{}, pt.eq_comm(Tr.Ent.k(e), Tr.Ent.k(f)), eb)
      %Equal.sym(Cmp, Nat.cmp(Tr.Ent.k(e), Tr.Ent.k(f)), EQ{}, tc.cmp_eq(Tr.Ent.k(e), Tr.Ent.k(f), eq)) : {[e] == Tr.set.go([f], e, _) : List<&2, Tr.Ent>}
      {==}
    case Tr.KOne{+f} False{}:
      +c = Nat.is_lt(Tr.Ent.k(f), Tr.Ent.k(e))
      +r2 = tc.two_read(hs, lo, f, e, Nat.is_lt(Tr.Ent.k(f), Nat.add(lo, Tr.KMap.half(hs))), Nat.is_lt(Tr.Ent.k(e), Nat.add(lo, Tr.KMap.half(hs))), {==}, {==})
      Equal.trans(List<&2, Tr.Ent>, Tr.KMap.read(Tr.KMap.two(hs, lo, f, e, Nat.is_lt(Tr.Ent.k(f), Nat.add(lo, Tr.KMap.half(hs))), Nat.is_lt(Tr.Ent.k(e), Nat.add(lo, Tr.KMap.half(hs))))), tc.pair(c, f, e), Tr.set([f], e), r2, Equal.sym(List<&2, Tr.Ent>, Tr.set([f], e), tc.pair(c, f, e), tc.set_one(f, e, c, {==}, eb)))
    case Tr.KFork{+mid, +mp, +l, +r} True{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +P = Tr.KMap.put(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)))
      +ih = tc.put_read(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)), {==}, tc.bst_l(mid, mp, l, r, bt))
      +s1 = Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, y => List.append(&2, Tr.Ent, y, R), Tr.KMap.read(P), Tr.set(L, e), ih)
      Equal.trans(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, Tr.KMap.read(P), R), List.append(&2, Tr.Ent, Tr.set(L, e), R), Tr.set(List.append(&2, Tr.Ent, L, R), e), s1, Equal.sym(List<&2, Tr.Ent>, Tr.set(List.append(&2, Tr.Ent, L, R), e), List.append(&2, Tr.Ent, Tr.set(L, e), R), tc.set_app_l(L, R, mid, e, tc.bst_ge(mid, mp, l, r, bt), eb)))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +P = Tr.KMap.put(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)))
      +ih = tc.put_read(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)), {==}, tc.bst_r(mid, mp, l, r, bt))
      +s1 = Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, y => List.append(&2, Tr.Ent, L, y), Tr.KMap.read(P), Tr.set(R, e), ih)
      Equal.trans(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, L, Tr.KMap.read(P)), List.append(&2, Tr.Ent, L, Tr.set(R, e)), Tr.set(List.append(&2, Tr.Ent, L, R), e), s1, Equal.sym(List<&2, Tr.Ent>, Tr.set(List.append(&2, Tr.Ent, L, R), e), List.append(&2, Tr.Ent, L, Tr.set(R, e)), tc.set_app_r(L, R, mid, e, tc.bst_lt(mid, mp, l, r, bt), eb)))

def tc.put_bst(m: Tr.KMap, +hs: List<&2, Nat>, +lo: Nat, +e: Tr.Ent, b: Bool, +eb: {Tr.KMap.at(m, Tr.Ent.k(e)) == b : Bool}, +bt: {tc.bst(m) == True{} : Bool}) -> {tc.bst(Tr.KMap.put(m, hs, lo, e, b)) == True{} : Bool}:
  match m b:
    case Tr.KNil{} True{}:
      {==}
    case Tr.KNil{} False{}:
      {==}
    case Tr.KOne{+f} True{}:
      {==}
    case Tr.KOne{+f} False{}:
      tc.two_bst(hs, lo, f, e, Nat.is_lt(Tr.Ent.k(f), Nat.add(lo, Tr.KMap.half(hs))), Nat.is_lt(Tr.Ent.k(e), Nat.add(lo, Tr.KMap.half(hs))), {==}, {==}, eb)
    case Tr.KFork{+mid, +mp, +l, +r} True{}:
      +P = Tr.KMap.put(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)))
      +bl = tc.bst_l(mid, mp, l, r, bt)
      +rd = tc.put_read(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)), {==}, bl)
      +S = Tr.set(Tr.KMap.read(l), e)
      +ls = tc.lt_set(Tr.KMap.read(l), e, Tr.first(Tr.Ent.k(e), Tr.KMap.read(l)), mid, tc.bst_lt(mid, mp, l, r, bt), eb)
      +ll = Equal.trans(Bool, tc.lt(Tr.KMap.read(P), mid), tc.lt(S, mid), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, y => tc.lt(y, mid), Tr.KMap.read(P), S, rd), ls)
      tc.bst_fork(mid, P, r, tc.put_bst(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)), {==}, bl), tc.bst_r(mid, mp, l, r, bt), ll, tc.bst_ge(mid, mp, l, r, bt))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +P = Tr.KMap.put(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)))
      +br = tc.bst_r(mid, mp, l, r, bt)
      +rd = tc.put_read(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)), {==}, br)
      +S = Tr.set(Tr.KMap.read(r), e)
      +gs = tc.ge_set(Tr.KMap.read(r), e, Tr.first(Tr.Ent.k(e), Tr.KMap.read(r)), mid, tc.bst_ge(mid, mp, l, r, bt), eb)
      +gg = Equal.trans(Bool, tc.ge(Tr.KMap.read(P), mid), tc.ge(S, mid), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, y => tc.ge(y, mid), Tr.KMap.read(P), S, rd), gs)
      tc.bst_fork(mid, l, P, tc.bst_l(mid, mp, l, r, bt), tc.put_bst(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)), {==}, br), tc.bst_lt(mid, mp, l, r, bt), gg)

def tc.unset_read(m: Tr.KMap, +x: Nat, b: Bool, +eb: {Tr.KMap.at(m, x) == b : Bool}, +bt: {tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.unset(m, x, b)) == Tr.unset(Tr.KMap.read(m), x) : List<&2, Tr.Ent>}:
  match m b:
    case Tr.KNil{} True{}:
      {==}
    case Tr.KNil{} False{}:
      {==}
    case Tr.KOne{+e} True{}:
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), True{}, eb) : {Nil{} == Tr.unset.go([e], x, _) : List<&2, Tr.Ent>}
      {==}
    case Tr.KOne{+e} False{}:
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), False{}, eb) : {[e] == Tr.unset.go([e], x, _) : List<&2, Tr.Ent>}
      {==}
    case Tr.KFork{+mid, +mp, +l, +r} True{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +U = Tr.KMap.unset(l, x, Tr.KMap.at(l, x))
      +ih = tc.unset_read(l, x, Tr.KMap.at(l, x), {==}, tc.bst_l(mid, mp, l, r, bt))
      +s1 = Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, y => List.append(&2, Tr.Ent, y, R), Tr.KMap.read(U), Tr.unset(L, x), ih)
      Equal.trans(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, Tr.KMap.read(U), R), List.append(&2, Tr.Ent, Tr.unset(L, x), R), Tr.unset(List.append(&2, Tr.Ent, L, R), x), s1, Equal.sym(List<&2, Tr.Ent>, Tr.unset(List.append(&2, Tr.Ent, L, R), x), List.append(&2, Tr.Ent, Tr.unset(L, x), R), tc.unset_app_l(L, R, mid, x, tc.bst_ge(mid, mp, l, r, bt), eb)))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +U = Tr.KMap.unset(r, x, Tr.KMap.at(r, x))
      +ih = tc.unset_read(r, x, Tr.KMap.at(r, x), {==}, tc.bst_r(mid, mp, l, r, bt))
      +s1 = Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, y => List.append(&2, Tr.Ent, L, y), Tr.KMap.read(U), Tr.unset(R, x), ih)
      Equal.trans(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, L, Tr.KMap.read(U)), List.append(&2, Tr.Ent, L, Tr.unset(R, x)), Tr.unset(List.append(&2, Tr.Ent, L, R), x), s1, Equal.sym(List<&2, Tr.Ent>, Tr.unset(List.append(&2, Tr.Ent, L, R), x), List.append(&2, Tr.Ent, L, Tr.unset(R, x)), tc.unset_app_r(L, R, mid, x, tc.bst_lt(mid, mp, l, r, bt), eb)))

def tc.unset_bst(m: Tr.KMap, +x: Nat, b: Bool, +eb: {Tr.KMap.at(m, x) == b : Bool}, +bt: {tc.bst(m) == True{} : Bool}) -> {tc.bst(Tr.KMap.unset(m, x, b)) == True{} : Bool}:
  match m b:
    case Tr.KNil{} True{}:
      {==}
    case Tr.KNil{} False{}:
      {==}
    case Tr.KOne{+e} True{}:
      {==}
    case Tr.KOne{+e} False{}:
      {==}
    case Tr.KFork{+mid, +mp, +l, +r} True{}:
      +U = Tr.KMap.unset(l, x, Tr.KMap.at(l, x))
      +bl = tc.bst_l(mid, mp, l, r, bt)
      +rd = tc.unset_read(l, x, Tr.KMap.at(l, x), {==}, bl)
      +S = Tr.unset(Tr.KMap.read(l), x)
      +ls = tc.lt_unset(Tr.KMap.read(l), x, Tr.key.at(Tr.KMap.read(l), x), mid, tc.bst_lt(mid, mp, l, r, bt))
      +ll = Equal.trans(Bool, tc.lt(Tr.KMap.read(U), mid), tc.lt(S, mid), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, y => tc.lt(y, mid), Tr.KMap.read(U), S, rd), ls)
      tc.bst_fork(mid, U, r, tc.unset_bst(l, x, Tr.KMap.at(l, x), {==}, bl), tc.bst_r(mid, mp, l, r, bt), ll, tc.bst_ge(mid, mp, l, r, bt))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +U = Tr.KMap.unset(r, x, Tr.KMap.at(r, x))
      +br = tc.bst_r(mid, mp, l, r, bt)
      +rd = tc.unset_read(r, x, Tr.KMap.at(r, x), {==}, br)
      +S = Tr.unset(Tr.KMap.read(r), x)
      +gs = tc.ge_unset(Tr.KMap.read(r), x, Tr.key.at(Tr.KMap.read(r), x), mid, tc.bst_ge(mid, mp, l, r, bt))
      +gg = Equal.trans(Bool, tc.ge(Tr.KMap.read(U), mid), tc.ge(S, mid), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, y => tc.ge(y, mid), Tr.KMap.read(U), S, rd), gs)
      tc.bst_fork(mid, l, U, tc.bst_l(mid, mp, l, r, bt), tc.unset_bst(r, x, Tr.KMap.at(r, x), {==}, br), tc.bst_lt(mid, mp, l, r, bt), gg)

def tc.set_bst(+m: Tr.KMap, +hs: List<&2, Nat>, +e: Tr.Ent, +bt: {tc.bst(m) == True{} : Bool}) -> {tc.bst(Tr.KMap.set(m, hs, e)) == True{} : Bool}:
  tc.put_bst(m, hs, 0n, e, Tr.KMap.at(m, Tr.Ent.k(e)), {==}, bt)

def tc.del_bst(+m: Tr.KMap, +x: Nat, +bt: {tc.bst(m) == True{} : Bool}) -> {tc.bst(Tr.KMap.del(m, x)) == True{} : Bool}:
  tc.unset_bst(m, x, Tr.KMap.at(m, x), {==}, bt)

def tc.drop_bst(ks: List<&2, Nat>, +m: Tr.KMap, +bt: {tc.bst(m) == True{} : Bool}) -> {tc.bst(Tr.KMap.drop(ks, m)) == True{} : Bool}:
  match ks:
    case Nil{}:
      bt
    case +k <> rest:
      tc.drop_bst(rest, Tr.KMap.del(m, k), tc.del_bst(m, k, bt))

def tc.exact_bst(+m: Tr.KMap, +hs: List<&2, Nat>, o: Tr.Op, +bt: {tc.bst(m) == True{} : Bool}) -> {tc.bst(Tr.KMap.exact(m, hs, o)) == True{} : Bool}:
  match o:
    case Tr.Put{+k, +p, +v}:
      tc.set_bst(m, hs, Tr.Ent{k, p, v}, bt)
    case Tr.Del{+x}:
      tc.del_bst(m, x, bt)

def tc.patch_bst(ops: List<&2, Tr.Op>, +hs: List<&2, Nat>, +m: Tr.KMap, +bt: {tc.bst(m) == True{} : Bool}) -> {tc.bst(Tr.KMap.patch(ops, hs, m)) == True{} : Bool}:
  match ops:
    case Nil{}:
      bt
    case +o <> rest:
      tc.patch_bst(rest, hs, Tr.KMap.exact(m, hs, o), tc.exact_bst(m, hs, o, bt))

def tc.put_case_bst(b: Bool, +m: Tr.KMap, +hs: List<&2, Nat>, +e: Tr.Ent, +bt: {tc.bst(m) == True{} : Bool}) -> {tc.bst(Pair.fst(Tr.KMap, Tr.Ans, Tr.put.ans(b, m, hs, e))) == True{} : Bool}:
  match b:
    case True{}:
      tc.set_bst(m, hs, e, bt)
    case False{}:
      bt

def tc.keep_case_bst(b: Bool, +m: Tr.KMap, +n: Tr.KMap, +bm: {tc.bst(m) == True{} : Bool}, +bn: {tc.bst(n) == True{} : Bool}) -> {tc.bst(Pair.fst(Tr.KMap, Tr.Ans, Tr.keep.ans(b, m, n))) == True{} : Bool}:
  match b:
    case True{}:
      bn
    case False{}:
      bm

def tc.rec_bst(+m: Tr.KMap, +hs: List<&2, Nat>, r: Tr.Rec, +bt: {tc.bst(m) == True{} : Bool}) -> {tc.bst(Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r))) == True{} : Bool}:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, +v}:
          tc.put_case_bst(Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.KMap.has(m, p))), m, hs, Tr.Ent{k, p, v}, bt)
        case Tr.Del{x}:
          match x:
            case 0n:
              bt
            case 1n++y:
              +F = Tr.KMap.ups(m, 1n+y, Nil{}, Tr.KMap.gl(m, 1n+y), Tr.KMap.gr(m, 1n+y))
              tc.drop_bst(Tr.drops(F, hs, 1n+y), m, bt)
    case Tr.Rewind{+ops}:
      +n = Tr.KMap.patch(ops, hs, m)
      tc.keep_case_bst(Tr.KMap.hangs(Tr.KMap.onto(n, Nil{}), n), m, n, bt, tc.patch_bst(ops, hs, m, bt))

# Journals

def tc.go_bst(rs: List<&2, Tr.Rec>, +hs: List<&2, Nat>, +m: Tr.KMap, +bt: {tc.bst(m) == True{} : Bool}) -> {tc.bst(Tr.KMap.go(rs, hs, m)) == True{} : Bool}:
  match rs:
    case Nil{}:
      bt
    case +r <> rest:
      tc.go_bst(rest, hs, Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r)), tc.rec_bst(m, hs, r, bt))

def tc.at_bst(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>, +n: Nat) -> {tc.bst(Tr.St.at(List.reverse.go(&2, Tr.Rec, rs, Nil{}), hs, n)) == True{} : Bool}:
  tc.go_bst(List.take(&2, Tr.Rec, List.reverse(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, rs, Nil{})), n), hs, Tr.KNil{}, {==})

# ---- job ----

# proof_job: the S2 laws (docs/runtime.md) of the job model in
# bend/job.bend: output caps and drops, one end per job, ended jobs stay
# ended, a blocking call never outlives its budget, a tool call's stream
# journals one final record carrying everything, and a rewind stops
# exactly the orphan jobs. Each job lemma speaks of a job at any state,
# by induction on the events it sees.

# Logic
# -----

def pj.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pj.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pj.BD(_, A, Unit)
  Unit{}

# Arithmetic
# ----------

def pj.le0(t: Nat) -> {Nat.is_le(0n, t) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

def pj.sub_zero(c: Nat) -> {c == Nat.sub(c, 0n) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pj.min_le_r(n: Nat, m: Nat) -> {Nat.is_le(Nat.min(n, m), m) == True{} : Bool}:
  match n m:
    case 0n _:
      pj.le0(m)
    case 1n+np 0n:
      {==}
    case 1n+np 1n+mp:
      pj.min_le_r(np, mp)

def pj.min_of_le(n: Nat, m: Nat, h: {Nat.is_le(n, m) == True{} : Bool}) -> {n == Nat.min(n, m) : Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      pj.absurdF({1n+np == Nat.min(1n+np, 0n) : Nat}, h)
    case 1n+np 1n+mp:
      %pj.min_of_le(np, mp, h) : {1n+np == 1n+_ : Nat}
      {==}

# ---- cvar ----

# proof_cvar: the S4 laws (docs/control.md) of the cvar model in
# bend/cvar.bend.
#
# A layer of sets is read one set at a time (`pv.layer_cons`), so a set
# appended last acts on the value of the sets before it
# (`pv.layer_snoc`): a hit gives its value, a miss keeps the value.
# The registry adds a declaration only when its id is free and its
# default is well typed, which keeps it unique and typed; a hit is a
# valid set of the found declaration, so every layer keeps the type of
# the default. A set of a Global cvar never hits in an agent layer. The
# cfg an agent writes drops only sets that miss its persisted cvar. A
# toggle's set of x hits or misses the same way whatever its Bool, so
# a second toggle undoes the first. Expansion leaves only plain
# commands, and its depth bound turns a self-running alias into a
# cycle.

# Logic
# -----

def cvar.pv.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def cvar.pv.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : cvar.pv.BD(_, Unit, A)
  Unit{}

# ---- director ----

# proof_director: the Director stack laws (S5), about bend/director.bend.
#
# The bound: a decision under `above` layers keeps above + len(stack) at
# most cap (`pd.go_bounded`), with room telling whether above + len(s)
# is below cap (the whole stack's length, fixed for the decision). A
# layer that keeps its place keeps the length; a deferring layer, or one
# that leads and stays, goes back on the stack of the layers below
# (`pd.under_ok`), which is bounded under one more layer; a Leave, or a
# Lead that leaves, drops it (`pd.le_pred`); a Stack adds a layer only
# with room (`pd.push_ok`). Each loop step is one decision, and its kept
# stack (leads staying) is a decision too (`pd.tick_bounded`).
#
# The loop: `pd.ok(l, k)` says the loop has ended, or has fewer than k
# global steps left. A tick takes one step off (`pd.tick_ok`), so after k
# steps the loop has ended (`pd.ends_go`). An ended loop never changes.
#
# The rule: each verdict law unfolds decide.go once (`pd.on_top` matches
# the model's `under` with the spec's `dir_on_top`); each tick law settles
# one outcome (`pd.settle_cont0`, `pd.settle_hand`, `pd.settle_failed`).
#
# Leads: a decision where leads leave equals the decision on the verdicts
# with each Lead read as a Leave (`pd.leave_as`), one where they stay the
# decision with each read as a Defer (`pd.defer_as`), and both have the
# same outcome (`pd.out_stay`). A step that goes on does not read the kept
# stack (`pd.settle_on`); one that ends reads only the outcome and the
# kept stack (`pd.settle_end`).
#
# The tree: layer i of a stack (0 = bottom) is the nodes 2i + 1 and
# 2i + 2, appended after the nodes of the layers below. So every key of
# encode(s) is at most 2 len(s) (`pd.enc_lt`), the nodes stay sorted
# (`pd.enc_sorted`), and each kind node hangs under the root or the kind
# node of the layer below (`pd.parent_ok`), each budget node under its
# kind node (`pd.enc_rooted`). decode reads the pairs back in order
# (`pd.dec_go`), and a rewind reaches the encoded tree (proof_tree's
# `rewind_reaches`), so it restores the stack.

# Numbers
# -------

def pd.lt_succ(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pd.lt_succ(p)

# Lists
# -----

def pd.app_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> r:
      %pd.app_nil(A, r) : {h <> List.append(&2, A, r, Nil{}) == h <> _ : List<&2, A>}
      {==}

def pd.app_assoc(-A: Data, xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> r:
      %pd.app_assoc(A, r, ys, zs) : {h <> List.append(&2, A, List.append(&2, A, r, ys), zs) == h <> _ : List<&2, A>}
      {==}

# Resume and rewind
# -----------------

# decode reads the layers of encode(s) back onto acc, then goes on
def pd.dec_go(s: List<&2, Dr.Layer>, +B: List<&2, Tr.Ent>, +acc: List<&2, Dr.Layer>) -> {Dr.decode.go(List.append(&2, Tr.Ent, Dr.encode(s), B), acc) == Dr.decode.go(B, List.append(&2, Dr.Layer, s, acc)) : List<&2, Dr.Layer>}:
  match s:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Dr.Layer{+k, +b}:
          +n = List.length(&2, Dr.Layer, rest)
          +x = {Tr.Ent{1n+Nat.double(n), Dr.kind.parent(n), k} : Tr.Ent}
          +y = {Tr.Ent{2n+Nat.double(n), 1n+Nat.double(n), b} : Tr.Ent}
          +E = Dr.encode(rest)
          %Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, E, [x, y]), B), List.append(&2, Tr.Ent, E, x <> y <> B), pd.app_assoc(Tr.Ent, E, [x, y], B)) : {Dr.decode.go(_, acc) == Dr.decode.go(B, Dr.Layer{k, b} <> List.append(&2, Dr.Layer, rest, acc)) : List<&2, Dr.Layer>}
          pd.dec_go(rest, x <> y <> B, acc)

def pd.dir_resume_restores(+s: List<&2, Dr.Layer>) -> {Dr.decode(Dr.encode(s)) == s : List<&2, Dr.Layer>}:
  %pd.app_nil(Tr.Ent, Dr.encode(s)) : {Dr.decode.go(_, Nil{}) == s : List<&2, Dr.Layer>}
  %pd.app_nil(Dr.Layer, s) : {Dr.decode.go(List.append(&2, Tr.Ent, Dr.encode(s), Nil{}), Nil{}) == _ : List<&2, Dr.Layer>}
  pd.dec_go(s, Nil{}, Nil{})

# ---- infer ----

# proof_infer: the inference layer laws of S6 (forced calls, the strict
# schema budget, the repetition guard, early compaction), about
# bend/infer.bend.
#
# A forced call: by induction on the replies and the retries; a retry's
# tries all carry the provider's support (`pi.flags_sup`). The budget:
# a take and its drop split every count (`pi.count_split`), ranking keeps
# every count (`pi.count_rank`) and sorts by priority (`pi.sorted_rank`),
# and a sorted list's take dominates its drop (`pi.dom_split`). The guard:
# the counter of period p is at least m exactly when the first m chunks
# each equal the chunk p before them (`pi.each_cycle`), so the guard fires
# exactly at a periodic window (`pi.fires_periodic`, `pi.cut_go`,
# `pi.keep_go`), and k equal chunks in a row end in one (`pi.run_loops`,
# `pi.rep_go`). Compaction:
# while below the threshold the next size stays within the limit
# (`pi.compact_go`).

# Logic
# -----

def pi.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pi.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pi.BD(_, A, Unit)
  Unit{}

def pi.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pi.le_add(+a: Nat, +s: Nat) -> {Nat.is_le(a, Nat.add(a, s)) == True{} : Bool}:
  match a:
    case 0n:
      pi.le0(s)
    case 1n+p:
      pi.le_add(p, s)

def pi.lt_nle(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      pi.absurdF({Nat.is_le(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      pi.absurdF({Nat.is_le(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      pi.lt_nle(p, q, h)

# ---- quirks ----

# proof_quirks: the quirks rulebook laws of S6, about bend/infer.bend.
#
# Compile: an unknown directive fails known_all (`pq.ka_app`); a clash
# makes the rulebook ambiguous (`pq.amb_app`); a swap of two neighbours
# changes neither known_all (`pq.ka_swap`) nor ambiguous (`pq.amb_swap`,
# clash is symmetric).
# Lookup: with no rule that applies the scan keeps None (`pq.none_go`);
# once a rule applies the best stays Some (`pq.stay_k`). Two rules that
# both apply and do not clash give the same best in either order
# (`pq.better_swap`: at one rank they agree on the value). In a rulebook
# that compiles, before r the best is below r's rank or equal to r
# (`pq.pre_ok`), and from r on it is r's rank and value (`pq.good`).
# The thinking ladder: the chosen ladder is a plain case split
# (reflexivity). A level is in the offer of a map exactly when the map
# keeps it (`pq.lad_has_keep`, from the S10 filter lemmas), and the filled
# map keeps a level exactly when the ladder rule does (`pq.lad_fill_keep`).
# With the shipped default ladders the ladder rule keeps what the S10
# rule keeps (`pq.lad_ship_e`), so the offers agree (`pq.lad_offer_fill`,
# by induction on the list).

# Logic
# -----

def pq.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pq.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pq.BD(_, Unit, A)
  Unit{}

def pq.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pq.BD(_, A, Unit)
  Unit{}

def pq.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pq.absurdF({False{} == True{} : Bool}, h)

def pq.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pq.absurdF({b == True{} : Bool}, h)

def pq.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pq.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      pq.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pq.eq_true(p, q, h))

def pq.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pq.lad_kb(+l: Ef.Lv, b: Bool) -> {Ef.keep.e(l, If.lad.ent(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pq.lad_kf(+l: Ef.Lv, e: Ef.Ent, +dl: List<&2, Ef.Lv>) -> {Ef.keep.e(l, If.lad.fill.e(l, e, dl)) == If.lad.keep(l, e, dl) : Bool}:
  match e:
    case Ef.Missing{}:
      pq.lad_kb(l, Ef.has(dl, l))
    case Ef.Null{}:
      {==}
    case Ef.Wire{}:
      {==}

# the filled map keeps a level exactly when the ladder rule does
def pq.lad_fill_keep(map: Ef.LvMap, +dl: List<&2, Ef.Lv>, l: Ef.Lv) -> {Ef.keep(If.lad.fill(map, dl), l) == If.lad.keep(l, Ef.entry(l, map), dl) : Bool}:
  match map:
    case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
      match l:
        case Ef.Off{}:
          pq.lad_kf(Ef.Off{}, o, dl)
        case Ef.Minimal{}:
          pq.lad_kf(Ef.Minimal{}, mi, dl)
        case Ef.Low{}:
          pq.lad_kf(Ef.Low{}, lo, dl)
        case Ef.Medium{}:
          pq.lad_kf(Ef.Medium{}, me, dl)
        case Ef.High{}:
          pq.lad_kf(Ef.High{}, hi, dl)
        case Ef.Xhigh{}:
          pq.lad_kf(Ef.Xhigh{}, xh, dl)
        case Ef.Max{}:
          pq.lad_kf(Ef.Max{}, mx, dl)

# ---- tools ----

# proof_tools: the S7 laws (docs/tools.md) of the tool surface model in
# bend/tools.bend. An event never touches the roster, and a turn sends
# the session's roster (`pl.sent_go`, by induction on the events). A join
# puts the tool in front of `dyn`; a quit drops every copy (`pl.drop_go`, with the head
# test as a parameter). `build` adds the intent parameter only when it is
# missing, and lifts the version to at least 1. A walk keeps its depth
# equal to the names it holds (`pl.esc`, `pl.ins`). The gate lemmas speak
# of `exec.go` at any head test: what ran is a prefix, a gated step that
# ran used one approval, a denial stops at the denied step, and a script
# that finished ran every step.

# Logic
# -----

def tools.pl.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def tools.pl.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : tools.pl.BD(_, A, Unit)
  Unit{}

def pl.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      tools.pl.absurdF({False{} == True{} : Bool}, h)

def pl.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      tools.pl.absurdF({b == True{} : Bool}, h)

# ---- screen ----

# proof_screen: the S8 laws (docs/interface.md) of the interface model in
# bend/screen.bend: the scrollback has no gap and only grows, a resize and
# a flush keep it in order, the pacer never runs ahead nor back and drains
# a backlog, only checked frames reach the terminal, and a vertical stack
# keeps its children inside the viewport, apart, and whole when they fit.

# Logic
# -----

def screen.ps.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def screen.ps.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : screen.ps.BD(_, A, Unit)
  Unit{}

def ps.le0(t: Nat) -> {Nat.is_le(0n, t) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

def screen.ps.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      screen.ps.le_refl(p)

def screen.ps.le_succ(n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      screen.ps.le_succ(p)

def screen.ps.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      ps.le0(c)
    case 1n+ap 0n _:
      screen.ps.absurdF({Nat.is_le(1n+ap, c) == True{} : Bool}, ab)
    case 1n+ap 1n+bp 0n:
      screen.ps.absurdF({Nat.is_le(1n+ap, 0n) == True{} : Bool}, bc)
    case 1n+ap 1n+bp 1n+cp:
      screen.ps.le_trans(ap, bp, cp, ab, bc)

# ---- semver ----

# proof_semver: the R1 laws (LAWS.bend section release, release versions) of the
# model in bend/semver.bend.
#
# Numbers: incrementing the digits adds one to their value, so the digits
# Num.dec writes for n have the value n; Num.read takes them back, as they
# are the digits of their own value. Num.str writes digits that Sym.of
# reads back as those digits, so reading Ver.show(v) gives back the three
# fields of v. The order compares major, then minor, then patch: each
# level is reflexive, transitive, total and antisymmetric when the level
# below it is. The next release takes 1 + a patch at least as high as the
# patch of each tag of the series, under the same major and minor, so it
# is newer than each; a tag of another series never names it, and adds no
# patch to the highest one. A release passed its guard: it is newer than
# every version tag; with only tags of the series, the guard passes.
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters), with an equation that names it.

# Logic
# -----

def semver.ps.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def semver.ps.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : semver.ps.BD(_, Unit, A)
  Unit{}

def semver.ps.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : semver.ps.BD(_, A, Unit)
  Unit{}

def semver.ps.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      semver.ps.absurdF({False{} == True{} : Bool}, h)

def semver.ps.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      semver.ps.absurdF({b == True{} : Bool}, h)

def semver.ps.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      semver.ps.eq_refl(p)

def semver.ps.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      semver.ps.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      semver.ps.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, semver.ps.eq_true(p, q, h))

def ps.digs_refl(+ds: List<&2, Sv.Dig>) -> {True{} == Sv.Num.digs_eq(ds, ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> r:
      %semver.ps.eq_refl(Sv.Dig.val(d)) : {True{} == Bool.and(_, Sv.Num.digs_eq(r, r)) : Bool}
      ps.digs_refl(r)

# ---- auth_flight ----

# proof_auth_flight: the laws of LAWS.bend section auth_flight (A1). Every event
# keeps an invariant of the reachable states (`pf.Inv`): the callers that
# lead a flight are as many as the flights in flight (one or none); a
# leader leads the flight that lands next; a leader about to land a
# credential finds it stored, or a newer one; and a finished caller of a
# flight holds the outcome that flight landed with. The laws follow from
# it.

# Logic and numbers
# -----------------

def auth_flight.pf.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pf.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : auth_flight.pf.BD(_, Unit, A)
  Unit{}

def pf.ND(n: Nat, z: Type, s: Type) -> Type:
  match n:
    case 0n:
      z
    case 1n+p:
      s

def pf.succ_ne_zero(-A: Type, -n: Nat, e: {1n+n == 0n : Nat}) -> A:
  %e : pf.ND(_, A, Unit)
  Unit{}

# a + b == 0: both are 0
def auth_flight.pf.add_zero(a: Nat, -b: Nat, e: {Nat.add(a, b) == 0n : Nat}) -> ({a == 0n : Nat} & {b == 0n : Nat}):
  match a:
    case 0n:
      ({==}, e)
    case 1n+p:
      pf.succ_ne_zero(({1n+p == 0n : Nat} & {b == 0n : Nat}), Nat.add(p, b), e)

def pf.snd(-A: Type, -B: Type, p: (A & B)) -> B:
  (a, b) = p
  b

# ---- themes ----

# proof_themes: the T1 laws (docs/interface.md Themes) of the theme model
# in bend/theme.bend.
#
# Resolution scans the candidates in order: a candidate that does not
# resolve the name passes the scan on, so before the first one that does
# the scan finds nothing, and with none at all it ends at the default
# theme with a warning. A loaded file passed the validity check. The
# validity check asks of each token what its fill needs, so the fill of
# every token of a valid file has a value. The mode and the palette read
# only the colors and the export page, never the name. The shipped
# themes' contrasts and 256-color indices are finite: the checker
# computes them.

# Logic
# -----

def themes.pt.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def themes.pt.none_some(-A: Type, -B: Data, -b: B, e: {None{} == Some{b} : Maybe<&2, B>}) -> A:
  %e : themes.pt.BD(Maybe.is_some(&2, B, _), A, Unit)
  Unit{}

# adding an act the ledger does not hold puts it in front
def pp.add_new(+s: List<&2, Nat>, +x: Nat, m: {Pr.mem(x, s) == False{} : Bool}) -> {Pr.add(s, x) == x <> s : List<&2, Nat>}:
  %Equal.sym(Bool, Pr.mem(x, s), False{}, m) : {Pr.add.put(_, x, s) == x <> s : List<&2, Nat>}
  {==}

# ---- progress_report ----

# proof_progress_report: lemmas for the laws that a harness failure is
# reported (LAWS.bend section progress): the auxiliary-model fallback of
# bend/aux_fallback.bend and the skill and template loading of
# bend/skill_load.bend.
#
# Fallbacks. The events of a session come from one pass at a time
# (`Af.go`), so each law is an induction over the passes with any set of
# shown keys. A substitution event of key k comes with a notice of k
# unless the session showed k before; a key joins the shown set only with
# its notice. So every substituted key is shown or noticed, and from an
# empty set, noticed. The other way is simpler: a notice of k comes only
# right after the substitution event of k.
#
# Loading. Each candidate file adds its path to the loaded list when it is
# good, and a diagnostic with its path when it is not. So each candidate's
# path is on one of the two lists. A loaded path and a reported path are
# each the path of some candidate; when no two candidates share a path, no
# path is on both.
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters), with an equation that names it.

# Logic
# -----

def ppr.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ppr.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : ppr.BD(_, Unit, A)
  Unit{}

def ppr.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ppr.BD(_, A, Unit)
  Unit{}

def ppr.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ppr.absurdF({False{} == True{} : Bool}, h)

def ppr.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      ppr.absurdF({b == True{} : Bool}, h)

# a true right side makes the or true
def ppr.or_r(a: Bool, +b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def ppr.or_l(a: Bool, b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ppr.absurdF({b == True{} : Bool}, h)

def ppr.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      ppr.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def ppr.nat_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ppr.nat_eq_refl(p)

def ppr.nat_eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ppr.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      ppr.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, ppr.nat_eq_true(p, q, h))

# Loading
# -------

# a head of a true or keeps it true: or(a, or(A, B)) from or(A, B), in the
# loaded place and in the reported place
def ppr.or_in_l(a: Bool, +x: Bool, +y: Bool, h: {Bool.or(x, y) == True{} : Bool}) -> {Bool.or(Bool.or(a, x), y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def ppr.or_in_r(a: Bool, x: Bool, +y: Bool, h: {Bool.or(x, y) == True{} : Bool}) -> {Bool.or(x, Bool.or(a, y)) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      ppr.or_r(a, y, h)

# a true or with a false-making implication
def ppr.or_mono(a: Bool, +x: Bool, +y: Bool, f: {x == True{} : Bool} -> {y == True{} : Bool}, h: {Bool.or(a, x) == True{} : Bool}) -> {Bool.or(a, y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(h)

# ---- supervisor ----

# proof_supervisor: the D1 laws of LAWS.bend section supervisor.
#
# - restart_gives_up: the failures of a crash loop stay in the window, so
#   their count only grows (`ps.block`), up to the give-up.
# - timeouts_ordered: each timeout is a sum that contains the timeouts it
#   waits for.
# - revive_after_refresh: the time since the last record stays below the
#   refresh period (`ps.since_lt`), so a boot within the boot window
#   finds the evidence within the max age.
# - orphan_never_aborts_resumable: every exit is sound (`ps.exit_sound`)
#   and an exit is final.
# - idle_shutdown_never_aborts: a closed gate never holds a run
#   (`ps.Inv`), so a commit, which needs every gate closed, stops no run.
# - adopt_same_build: an adoption reads equal build numbers.

# Logic
# -----

def supervisor.ps.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def supervisor.ps.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : supervisor.ps.BD(_, Unit, A)
  Unit{}

def supervisor.ps.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : supervisor.ps.BD(_, A, Unit)
  Unit{}

def supervisor.ps.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      supervisor.ps.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

# Numbers
# -------

def supervisor.ps.le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      supervisor.ps.le_refl(p)

def ps.le_zero(b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

def supervisor.ps.le_succ(a: Nat) -> {Nat.is_le(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      supervisor.ps.le_succ(p)

def supervisor.ps.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      ps.le_zero(c)
    case 1n+p 0n _:
      supervisor.ps.absurdF({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      supervisor.ps.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      supervisor.ps.le_trans(p, q, r, ab, bc)

# x is at most g + x
def supervisor.ps.le_add_l(+g: Nat, +x: Nat) -> {Nat.is_le(x, Nat.add(g, x)) == True{} : Bool}:
  match g:
    case 0n:
      supervisor.ps.le_refl(x)
    case 1n+p:
      supervisor.ps.le_trans(x, Nat.add(p, x), 1n+Nat.add(p, x), supervisor.ps.le_add_l(p, x), supervisor.ps.le_succ(Nat.add(p, x)))

# adding g on the left keeps the order
def ps.le_mono(g: Nat, -a: Nat, -x: Nat, h: {Nat.is_le(a, x) == True{} : Bool}) -> {Nat.is_le(Nat.add(g, a), Nat.add(g, x)) == True{} : Bool}:
  match g:
    case 0n:
      h
    case 1n+p:
      ps.le_mono(p, a, x, h)

def supervisor.ps.eq_of_is_eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      supervisor.ps.absurdF({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      supervisor.ps.absurdF({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, supervisor.ps.eq_of_is_eq(p, q, e))

# The rank's field reader against semver.bend's Num.read
# -------------------------------------------------------

def rk.ten_mul(v: Nat) -> {Sv.Num.ten(v) == Nat.mul(v, 10n) : Nat}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      %rk.ten_mul(p) : {Nat.add(10n, Sv.Num.ten(p)) == Nat.add(10n, _) : Nat}
      {==}

def rk.fval(ds: List<&2, Sv.Dig>) -> {Rp.fval(ds) == Sv.Num.val(ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case d <> +rest:
      %rk.fval(rest) : {Nat.add(Sv.Dig.val(d), Nat.mul(Rp.fval(rest), 10n)) == Nat.add(Sv.Dig.val(d), Sv.Num.ten(_)) : Nat}
      %rk.ten_mul(Rp.fval(rest)) : {Nat.add(Sv.Dig.val(d), _) == Nat.add(Sv.Dig.val(d), Sv.Num.ten(Rp.fval(rest))) : Nat}
      {==}

def rk.I10(ds: List<&2, Sv.Dig>) -> List<&2, Sv.Dig>:
  Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(ds))))))))))

# ten increments carry once and leave the last digit as it was
def rk.inc10(d: Sv.Dig, -r: List<&2, Sv.Dig>) -> {rk.I10(d <> r) == d <> Sv.Num.inc(r) : List<&2, Sv.Dig>}:
  match d:
    case Sv.D0{}:
      {==}
    case Sv.D1{}:
      {==}
    case Sv.D2{}:
      {==}
    case Sv.D3{}:
      {==}
    case Sv.D4{}:
      {==}
    case Sv.D5{}:
      {==}
    case Sv.D6{}:
      {==}
    case Sv.D7{}:
      {==}
    case Sv.D8{}:
      {==}
    case Sv.D9{}:
      {==}

def rk.dec10(m: Nat) -> {Sv.Num.dec(Nat.add(10n, m)) == rk.I10(Sv.Num.dec(m)) : List<&2, Sv.Dig>}:
  {==}

def rk.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %rk.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# b + (a + c) == a + (b + c)
def rk.add_swap(a: Nat, +b: Nat, -c: Nat) -> {Nat.add(b, Nat.add(a, c)) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %rk.add_swap(p, b, c) : {Nat.add(b, 1n+Nat.add(p, c)) == 1n+_ : Nat}
      rk.add_succ(b, Nat.add(p, c))

def rk.dec_step0(d: Sv.Dig) -> {Sv.Num.dec(Nat.add(Sv.Dig.val(d), Sv.Num.ten(1n))) == d <> Sv.Num.dec(1n) : List<&2, Sv.Dig>}:
  match d:
    case Sv.D0{}:
      {==}
    case Sv.D1{}:
      {==}
    case Sv.D2{}:
      {==}
    case Sv.D3{}:
      {==}
    case Sv.D4{}:
      {==}
    case Sv.D5{}:
      {==}
    case Sv.D6{}:
      {==}
    case Sv.D7{}:
      {==}
    case Sv.D8{}:
      {==}
    case Sv.D9{}:
      {==}

# d + 10 * (1 + u) is written as d after the digits of 1 + u
def rk.dec_step(+d: Sv.Dig, u: Nat) -> {Sv.Num.dec(Nat.add(Sv.Dig.val(d), Sv.Num.ten(1n+u))) == d <> Sv.Num.dec(1n+u) : List<&2, Sv.Dig>}:
  match u:
    case 0n:
      rk.dec_step0(d)
    case 1n++w:
      +X = Sv.Num.ten(1n+w)
      +v = Sv.Dig.val(d)
      Equal.trans(List<&2, Sv.Dig>, Sv.Num.dec(Nat.add(v, Nat.add(10n, X))), Sv.Num.dec(Nat.add(10n, Nat.add(v, X))), d <> Sv.Num.inc(Sv.Num.dec(1n+w)), Equal.cong(Nat, List<&2, Sv.Dig>, Sv.Num.dec, Nat.add(v, Nat.add(10n, X)), Nat.add(10n, Nat.add(v, X)), rk.add_swap(10n, v, X)), Equal.trans(List<&2, Sv.Dig>, Sv.Num.dec(Nat.add(10n, Nat.add(v, X))), rk.I10(Sv.Num.dec(Nat.add(v, X))), d <> Sv.Num.inc(Sv.Num.dec(1n+w)), rk.dec10(Nat.add(v, X)), Equal.trans(List<&2, Sv.Dig>, rk.I10(Sv.Num.dec(Nat.add(v, X))), rk.I10(d <> Sv.Num.dec(1n+w)), d <> Sv.Num.inc(Sv.Num.dec(1n+w)), Equal.cong(List<&2, Sv.Dig>, List<&2, Sv.Dig>, rk.I10, Sv.Num.dec(Nat.add(v, X)), d <> Sv.Num.dec(1n+w), rk.dec_step(d, w)), rk.inc10(d, Sv.Num.dec(1n+w)))))

def rk.ten_zero(v: Nat, e: {Sv.Num.ten(v) == 0n : Nat}) -> {v == 0n : Nat}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      pf.succ_ne_zero({1n+p == 0n : Nat}, Nat.add(9n, Sv.Num.ten(p)), e)

# digits whose most significant digit is not 0 have a value above 0
def rk.pos(rr: List<&2, Sv.Dig>, +r: Sv.Dig, h: {Bool.not(Rp.zero(Rp.top(rr, r))) == True{} : Bool}, e: {Sv.Num.val(r <> rr) == 0n : Nat}) -> Empty:
  match rr:
    case Nil{}:
      match r:
        case Sv.D0{}:
          semver.ps.absurdF(Empty, h)
        case Sv.D1{}:
          pf.succ_ne_zero(Empty, 0n, e)
        case Sv.D2{}:
          pf.succ_ne_zero(Empty, 1n, e)
        case Sv.D3{}:
          pf.succ_ne_zero(Empty, 2n, e)
        case Sv.D4{}:
          pf.succ_ne_zero(Empty, 3n, e)
        case Sv.D5{}:
          pf.succ_ne_zero(Empty, 4n, e)
        case Sv.D6{}:
          pf.succ_ne_zero(Empty, 5n, e)
        case Sv.D7{}:
          pf.succ_ne_zero(Empty, 6n, e)
        case Sv.D8{}:
          pf.succ_ne_zero(Empty, 7n, e)
        case Sv.D9{}:
          pf.succ_ne_zero(Empty, 8n, e)
    case +r2 <> +rr2:
      rk.pos(rr2, r2, h, rk.ten_zero(Sv.Num.val(r2 <> rr2), pf.snd({Sv.Dig.val(r) == 0n : Nat}, {Sv.Num.ten(Sv.Num.val(r2 <> rr2)) == 0n : Nat}, auth_flight.pf.add_zero(Sv.Dig.val(r), Sv.Num.ten(Sv.Num.val(r2 <> rr2)), e))))

def rk.canon_tail(rr: List<&2, Sv.Dig>, -r: Sv.Dig, h: {Bool.not(Rp.zero(Rp.top(rr, r))) == True{} : Bool}) -> {Rp.canon(r <> rr) == True{} : Bool}:
  match rr:
    case Nil{}:
      {==}
    case r2 <> rr2:
      h

def rk.dcons(-d: Sv.Dig, -a: List<&2, Sv.Dig>, -b: List<&2, Sv.Dig>, e: {a == b : List<&2, Sv.Dig>}) -> {d <> a == d <> b : List<&2, Sv.Dig>}:
  %e : {d <> a == d <> _ : List<&2, Sv.Dig>}
  {==}

def rk.h1_at(+d: Sv.Dig, +rest: List<&2, Sv.Dig>, V: Nat, +eV: {Sv.Num.val(rest) == V : Nat}, nz: {Sv.Num.val(rest) == 0n : Nat} -> Empty, ih: {Sv.Num.dec(Sv.Num.val(rest)) == rest : List<&2, Sv.Dig>}) -> {Sv.Num.dec(Nat.add(Sv.Dig.val(d), Sv.Num.ten(V))) == d <> rest : List<&2, Sv.Dig>}:
  match V:
    case 0n:
      Empty.absurd({Sv.Num.dec(Nat.add(Sv.Dig.val(d), Sv.Num.ten(0n))) == d <> rest : List<&2, Sv.Dig>}, nz(eV))
    case 1n++u:
      Equal.trans(List<&2, Sv.Dig>, Sv.Num.dec(Nat.add(Sv.Dig.val(d), Sv.Num.ten(1n+u))), d <> Sv.Num.dec(1n+u), d <> rest, rk.dec_step(d, u), rk.dcons(d, Sv.Num.dec(1n+u), rest, Equal.trans(List<&2, Sv.Dig>, Sv.Num.dec(1n+u), Sv.Num.dec(Sv.Num.val(rest)), rest, Equal.cong(Nat, List<&2, Sv.Dig>, Sv.Num.dec, 1n+u, Sv.Num.val(rest), Equal.sym(Nat, Sv.Num.val(rest), 1n+u, eV)), ih)))

def rk.h1_one(d: Sv.Dig) -> {Sv.Num.dec(Sv.Num.val([d])) == [d] : List<&2, Sv.Dig>}:
  match d:
    case Sv.D0{}:
      {==}
    case Sv.D1{}:
      {==}
    case Sv.D2{}:
      {==}
    case Sv.D3{}:
      {==}
    case Sv.D4{}:
      {==}
    case Sv.D5{}:
      {==}
    case Sv.D6{}:
      {==}
    case Sv.D7{}:
      {==}
    case Sv.D8{}:
      {==}
    case Sv.D9{}:
      {==}

# canonical digits are the digits semver.bend writes for their value
def rk.h1(ds: List<&2, Sv.Dig>, +h: {Rp.canon(ds) == True{} : Bool}) -> {Sv.Num.dec(Sv.Num.val(ds)) == ds : List<&2, Sv.Dig>}:
  match ds:
    case Nil{}:
      semver.ps.absurdF({Sv.Num.dec(Sv.Num.val(Nil{})) == Nil{} : List<&2, Sv.Dig>}, h)
    case +d <> rest:
      match rest:
        case Nil{}:
          rk.h1_one(d)
        case +r <> +rr:
          rk.h1_at(d, r <> rr, Sv.Num.val(r <> rr), {==}, e => rk.pos(rr, r, h, e), rk.h1(r <> rr, rk.canon_tail(rr, r, h)))

def rk.ofv(n: Nat) -> Sv.Dig:
  match n:
    case 0n:
      Sv.D0{}
    case 1n+n0:
      match n0:
        case 0n:
          Sv.D1{}
        case 1n+n1:
          match n1:
            case 0n:
              Sv.D2{}
            case 1n+n2:
              match n2:
                case 0n:
                  Sv.D3{}
                case 1n+n3:
                  match n3:
                    case 0n:
                      Sv.D4{}
                    case 1n+n4:
                      match n4:
                        case 0n:
                          Sv.D5{}
                        case 1n+n5:
                          match n5:
                            case 0n:
                              Sv.D6{}
                            case 1n+n6:
                              match n6:
                                case 0n:
                                  Sv.D7{}
                                case 1n+n7:
                                  match n7:
                                    case 0n:
                                      Sv.D8{}
                                    case 1n+n8:
                                      Sv.D9{}

def rk.ofv_val(d: Sv.Dig) -> {rk.ofv(Sv.Dig.val(d)) == d : Sv.Dig}:
  match d:
    case Sv.D0{}:
      {==}
    case Sv.D1{}:
      {==}
    case Sv.D2{}:
      {==}
    case Sv.D3{}:
      {==}
    case Sv.D4{}:
      {==}
    case Sv.D5{}:
      {==}
    case Sv.D6{}:
      {==}
    case Sv.D7{}:
      {==}
    case Sv.D8{}:
      {==}
    case Sv.D9{}:
      {==}

def rk.dig_sound(+a: Sv.Dig, +b: Sv.Dig, h: {Sv.Dig.eq(a, b) == True{} : Bool}) -> {a == b : Sv.Dig}:
  Equal.trans(Sv.Dig, a, rk.ofv(Sv.Dig.val(a)), b, Equal.sym(Sv.Dig, rk.ofv(Sv.Dig.val(a)), a, rk.ofv_val(a)), Equal.trans(Sv.Dig, rk.ofv(Sv.Dig.val(a)), rk.ofv(Sv.Dig.val(b)), b, Equal.cong(Nat, Sv.Dig, rk.ofv, Sv.Dig.val(a), Sv.Dig.val(b), semver.ps.eq_true(Sv.Dig.val(a), Sv.Dig.val(b), h)), rk.ofv_val(b)))

def rk.digs_sound(xs: List<&2, Sv.Dig>, ys: List<&2, Sv.Dig>, +h: {Sv.Num.digs_eq(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, Sv.Dig>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      semver.ps.absurdF({Nil{} == y <> yr : List<&2, Sv.Dig>}, h)
    case x <> xr Nil{}:
      semver.ps.absurdF({x <> xr == Nil{} : List<&2, Sv.Dig>}, h)
    case +x <> +xr +y <> +yr:
      %rk.dig_sound(x, y, semver.ps.and_l(Sv.Dig.eq(x, y), Sv.Num.digs_eq(xr, yr), h)) : {x <> xr == _ <> yr : List<&2, Sv.Dig>}
      %rk.digs_sound(xr, yr, semver.ps.and_r(Sv.Dig.eq(x, y), Sv.Num.digs_eq(xr, yr), h)) : {x <> xr == x <> _ : List<&2, Sv.Dig>}
      {==}

# the most significant of the digits is not 0 (there is one)
def rk.nz(ds: List<&2, Sv.Dig>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> rest:
      Bool.not(Rp.zero(Rp.top(rest, d)))

def rk.canon_of_nz(ds: List<&2, Sv.Dig>, h: {rk.nz(ds) == True{} : Bool}) -> {Rp.canon(ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      semver.ps.absurdF({Rp.canon(Nil{}) == True{} : Bool}, h)
    case d <> rest:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h

def rk.nz_d0(X: List<&2, Sv.Dig>, h: {rk.nz(X) == True{} : Bool}) -> {rk.nz(Sv.D0{} <> X) == True{} : Bool}:
  match X:
    case Nil{}:
      semver.ps.absurdF({rk.nz(Sv.D0{} <> Nil{}) == True{} : Bool}, h)
    case x <> xs:
      h

def rk.inc_nz_cons(d: Sv.Dig, rest: List<&2, Sv.Dig>, +h: {Rp.canon(d <> rest) == True{} : Bool}, ih: {Rp.canon(rest) == True{} : Bool} -> {rk.nz(Sv.Num.inc(rest)) == True{} : Bool}) -> {rk.nz(Sv.Num.inc(d <> rest)) == True{} : Bool}:
  match d:
    case Sv.D0{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D1{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D2{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D3{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D4{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D5{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D6{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D7{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D8{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D9{}:
      match rest:
        case Nil{}:
          {==}
        case +r <> +rr:
          rk.nz_d0(Sv.Num.inc(r <> rr), ih(rk.canon_tail(rr, r, h)))

# the next number of canonical digits has a most significant digit that is not 0
def rk.inc_nz(ds: List<&2, Sv.Dig>, h: {Rp.canon(ds) == True{} : Bool}) -> {rk.nz(Sv.Num.inc(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      semver.ps.absurdF({rk.nz(Sv.Num.inc(Nil{})) == True{} : Bool}, h)
    case d <> +rest:
      rk.inc_nz_cons(d, rest, h, c => rk.inc_nz(rest, c))

def rk.canon_dec(n: Nat) -> {Rp.canon(Sv.Num.dec(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      rk.canon_of_nz(Sv.Num.inc(Sv.Num.dec(p)), rk.inc_nz(Sv.Num.dec(p), rk.canon_dec(p)))

# digits semver.bend reads back as written are canonical
def rk.h2(+ds: List<&2, Sv.Dig>, h: {Sv.Num.digs_eq(Sv.Num.dec(Sv.Num.val(ds)), ds) == True{} : Bool}) -> {Rp.canon(ds) == True{} : Bool}:
  %rk.digs_sound(Sv.Num.dec(Sv.Num.val(ds)), ds, h) : {Rp.canon(_) == True{} : Bool}
  rk.canon_dec(Sv.Num.val(ds))

def rk.keepm(ok: Bool, x: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{x}
    case False{}:
      None{}

# a number semver.bend reads, kept when it has at most 14 digits
def rk.guard(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{+x}:
      rk.keepm(LawsBase.rank_spec.short(x), x)

def rk.fp(L: Bool, +ds: List<&2, Sv.Dig>) -> {Rp.field.put(Bool.and(L, True{}), ds) == rk.keepm(L, Sv.Num.val(ds)) : Maybe<&2, Nat>}:
  match L:
    case True{}:
      %rk.fval(ds) : {Some{Rp.fval(ds)} == Some{_} : Maybe<&2, Nat>}
      {==}
    case False{}:
      {==}

def rk.fp0(L: Bool, -ds: List<&2, Sv.Dig>) -> {Rp.field.put(Bool.and(L, False{}), ds) == None{} : Maybe<&2, Nat>}:
  match L:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.not_true(b: Bool, f: {b == True{} : Bool} -> Empty) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, f({==}))
    case False{}:
      {==}

def rk.field_at(+ds: List<&2, Sv.Dig>, c: Bool, ec: {Rp.canon(ds) == c : Bool}) -> {Rp.field.put(Bool.and(Nat.is_le(List.length(&2, Sv.Dig, ds), 14n), c), ds) == rk.guard(Sv.Num.read(ds)) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      +L = Nat.is_le(List.length(&2, Sv.Dig, ds), 14n)
      +V = Sv.Num.val(ds)
      +E = Equal.sym(List<&2, Sv.Dig>, Sv.Num.dec(V), ds, rk.h1(ds, ec))
      %E : {Rp.field.put(Bool.and(L, True{}), ds) == rk.guard(Sv.Num.read.ok(V, Sv.Num.digs_eq(_, ds))) : Maybe<&2, Nat>}
      %ps.digs_refl(ds) : {Rp.field.put(Bool.and(L, True{}), ds) == rk.guard(Sv.Num.read.ok(V, _)) : Maybe<&2, Nat>}
      %E : {Rp.field.put(Bool.and(L, True{}), ds) == rk.keepm(Nat.is_le(List.length(&2, Sv.Dig, _), 14n), V) : Maybe<&2, Nat>}
      rk.fp(L, ds)
    case False{}:
      +L = Nat.is_le(List.length(&2, Sv.Dig, ds), 14n)
      +V = Sv.Num.val(ds)
      +D = rk.not_true(Sv.Num.digs_eq(Sv.Num.dec(V), ds), t => semver.ps.absurdF(Empty, Equal.trans(Bool, False{}, Rp.canon(ds), True{}, Equal.sym(Bool, Rp.canon(ds), False{}, ec), rk.h2(ds, t))))
      %Equal.sym(Bool, Sv.Num.digs_eq(Sv.Num.dec(V), ds), False{}, D) : {Rp.field.put(Bool.and(L, False{}), ds) == rk.guard(Sv.Num.read.ok(V, _)) : Maybe<&2, Nat>}
      rk.fp0(L, ds)

def rk.field(+ds: List<&2, Sv.Dig>) -> {Rp.field(ds) == rk.guard(Sv.Num.read(ds)) : Maybe<&2, Nat>}:
  rk.field_at(ds, Rp.canon(ds), {==})

def rk.t1(p: Bool, -x: Nat, -gc: Maybe<&2, Nat>, -t: Nat) -> {Rp.rank.of3(rk.keepm(p, x), None{}, gc, t) == Nil{} : List<&2, Nat>}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.t2(p: Bool, q: Bool, -x: Nat, -y: Nat, -t: Nat) -> {Rp.rank.of3(rk.keepm(p, x), rk.keepm(q, y), None{}, t) == Nil{} : List<&2, Nat>}:
  match p q:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def rk.t3(p: Bool, q: Bool, r: Bool, -x: Nat, -y: Nat, -z: Nat, -t: Nat) -> {Rp.rank.of3(rk.keepm(p, x), rk.keepm(q, y), rk.keepm(r, z), t) == Replace.rank_spec.keep(Bool.and(p, Bool.and(q, r)), x, y, t, z) : List<&2, Nat>}:
  match p q r:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def rk.three(ra: Maybe<&2, Nat>, rb: Maybe<&2, Nat>, rc: Maybe<&2, Nat>, +t: Nat) -> {Rp.rank.of3(rk.guard(ra), rk.guard(rb), rk.guard(rc), t) == Replace.rank_spec.of(Sv.Ver.of3(ra, rb, rc), t) : List<&2, Nat>}:
  match ra rb rc:
    case None{} _ _:
      {==}
    case Some{+x} None{} _:
      rk.t1(LawsBase.rank_spec.short(x), x, rk.guard(rc), t)
    case Some{+x} Some{+y} None{}:
      rk.t2(LawsBase.rank_spec.short(x), LawsBase.rank_spec.short(y), x, y, t)
    case Some{+x} Some{+y} Some{+z}:
      rk.t3(LawsBase.rank_spec.short(x), LawsBase.rank_spec.short(y), LawsBase.rank_spec.short(z), x, y, z, t)

def rk.fields(m: Maybe<&2, List<&2, List<&2, Sv.Dig>>>, +t: Nat) -> {Rp.rank.fields(m, t) == Replace.rank_spec.of(Sv.Ver.of_fields(m), t) : List<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{fs}:
      match fs:
        case Nil{}:
          {==}
        case c <> Nil{}:
          {==}
        case c <> b <> Nil{}:
          {==}
        case +c <> +b <> +a <> Nil{}:
          %Equal.sym(Maybe<&2, Nat>, Rp.field(a), rk.guard(Sv.Num.read(a)), rk.field(a)) : {Rp.rank.of3(_, Rp.field(b), Rp.field(c), t) == Replace.rank_spec.of(Sv.Ver.of3(Sv.Num.read(a), Sv.Num.read(b), Sv.Num.read(c)), t) : List<&2, Nat>}
          %Equal.sym(Maybe<&2, Nat>, Rp.field(b), rk.guard(Sv.Num.read(b)), rk.field(b)) : {Rp.rank.of3(rk.guard(Sv.Num.read(a)), _, Rp.field(c), t) == Replace.rank_spec.of(Sv.Ver.of3(Sv.Num.read(a), Sv.Num.read(b), Sv.Num.read(c)), t) : List<&2, Nat>}
          %Equal.sym(Maybe<&2, Nat>, Rp.field(c), rk.guard(Sv.Num.read(c)), rk.field(c)) : {Rp.rank.of3(rk.guard(Sv.Num.read(a)), rk.guard(Sv.Num.read(b)), _, t) == Replace.rank_spec.of(Sv.Ver.of3(Sv.Num.read(a), Sv.Num.read(b), Sv.Num.read(c)), t) : List<&2, Nat>}
          rk.three(Sv.Num.read(a), Sv.Num.read(b), Sv.Num.read(c), t)
        case c <> b <> a <> d <> more:
          {==}

def rk.core_at(b: Bool, -c: Char, -rest: String) -> {Rp.core.at(b, c, rest) == Replace.rank_spec.core.at(b, c, rest) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.core_eq(s: String) -> {Rp.core(s) == Replace.rank_spec.core(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      %rk.core_eq(r) : {Rp.core.at(Char.is_eq(c, '-'), c, Rp.core(r)) == Replace.rank_spec.core.at(Char.is_eq(c, '-'), c, _) : String}
      rk.core_at(Char.is_eq(c, '-'), c, Rp.core(r))

def rk.tier_at(b: Bool, -rest: Nat) -> {Rp.tier.at(b, rest) == Replace.rank_spec.tier.at(b, rest) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.tier_eq(s: String) -> {Rp.tier(s) == Replace.rank_spec.tier(s) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      %rk.tier_eq(r) : {Rp.tier.at(Char.is_eq(c, '-'), Rp.tier(r)) == Replace.rank_spec.tier.at(Char.is_eq(c, '-'), _) : Nat}
      rk.tier_at(Char.is_eq(c, '-'), Rp.tier(r))

def rk.rank_read(+s: String) -> {Rp.rank.fields(Sv.Ver.fields(Sv.Sym.list(Rp.core(s)), Nil{}, Nil{}), Rp.tier(s)) == Replace.rank_spec.of(Sv.Ver.parse(Replace.rank_spec.core(s)), Replace.rank_spec.tier(s)) : List<&2, Nat>}:
  %rk.core_eq(s) : {Rp.rank.fields(Sv.Ver.fields(Sv.Sym.list(Rp.core(s)), Nil{}, Nil{}), Rp.tier(s)) == Replace.rank_spec.of(Sv.Ver.of_fields(Sv.Ver.fields(Sv.Sym.list(_), Nil{}, Nil{})), Replace.rank_spec.tier(s)) : List<&2, Nat>}
  %rk.tier_eq(s) : {Rp.rank.fields(Sv.Ver.fields(Sv.Sym.list(Rp.core(s)), Nil{}, Nil{}), Rp.tier(s)) == Replace.rank_spec.of(Sv.Ver.of_fields(Sv.Ver.fields(Sv.Sym.list(Rp.core(s)), Nil{}, Nil{})), _) : List<&2, Nat>}
  rk.fields(Sv.Ver.fields(Sv.Sym.list(Rp.core(s)), Nil{}, Nil{}), Rp.tier(s))

def rk.rank_cap(short: Bool, +s: String) -> {Rp.rank.cap(short, s) == Replace.rank_spec.cap(short, s) : List<&2, Nat>}:
  match short:
    case True{}:
      rk.rank_read(s)
    case False{}:
      {==}

def rk.rank(+s: String) -> {Rp.rank(s) == Replace.rank_spec(s) : List<&2, Nat>}:
  rk.rank_cap(Nat.is_le(String.length(s), 64n), s)

# ---- tui_color ----

# proof_tui_color: the T3 laws (docs/interface.md "Terminal colors") of
# the model in bend/tui_color.bend.
#
# Nat.divmod adds one to q * n + r per step and keeps r below n, so n
# times the quotient is at most x, and every q with n * q at most x is at
# most the quotient. So
# adding d to x never lowers the quotient, and raises it when d is at
# least n. A rung moves each channel from the last rung by such a step:
# the rising channels count the weight up, the falling ones count it
# down. So every channel moves toward the high end, and the widest
# channel, at least n wide, moves at each rung: a rung differs from all
# the rungs after it. A band is reached when w * num <= t * den; more
# tokens keep it reached, and a factor 1 + k on both t and w cancels.

# Logic
# -----

def pu.BD(+b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pu.absurd_ft(-A: Type, +e: {False{} == True{} : Bool}) -> A:
  %e : pu.BD(_, A, Unit)
  Unit{}

def pu.and_t(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# Numbers
# -------

def pu.le_zero(+n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pu.le_refl(+n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pu.le_refl(p)

def pu.le_trans(+a: Nat, +b: Nat, +c: Nat, +ab: {Nat.is_le(a, b) == True{} : Bool}, +bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n q r:
      pu.le_zero(r)
    case 1n+p 0n r:
      pu.absurd_ft({Nat.is_le(1n+p, r) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      pu.absurd_ft({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pu.le_trans(p, q, r, ab, bc)

def pu.le_succ_r(+a: Nat, +b: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n q:
      {==}
    case 1n+p 0n:
      pu.absurd_ft({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pu.le_succ_r(p, q, e)

def pu.lt_zero_f(+q: Nat) -> {False{} == Nat.is_lt(q, 0n) : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a <= a + c
def pu.le_add_r(+a: Nat, +c: Nat) -> {Nat.is_le(a, Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      pu.le_zero(c)
    case 1n+p:
      pu.le_add_r(p, c)

# n + (x - n) = x when n <= x
def pu.sub_add(+n: Nat, +x: Nat, +e: {Nat.is_le(n, x) == True{} : Bool}) -> {Nat.add(n, Nat.sub(x, n)) == x : Nat}:
  match n x:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      pu.absurd_ft({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, e)
    case 1n+p 1n+q:
      %pu.sub_add(p, q, e) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

# z <= x - n when n + z <= x
def pu.le_sub(+n: Nat, +z: Nat, +x: Nat, +e: {Nat.is_le(Nat.add(n, z), x) == True{} : Bool}) -> {Nat.is_le(z, Nat.sub(x, n)) == True{} : Bool}:
  match n x:
    case 0n 0n:
      e
    case 0n 1n+q:
      e
    case 1n+p 0n:
      pu.absurd_ft({Nat.is_le(z, Nat.sub(0n, 1n+p)) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pu.le_sub(p, z, q, e)

def pu.le_add_left(+n: Nat, +z: Nat, +x: Nat, +e: {Nat.is_le(Nat.add(n, z), x) == True{} : Bool}) -> {Nat.is_le(n, x) == True{} : Bool}:
  pu.le_trans(n, Nat.add(n, z), x, pu.le_add_r(n, z), e)

def pu.sub_le_self(+x: Nat, +n: Nat) -> {Nat.is_le(Nat.sub(x, n), x) == True{} : Bool}:
  match x n:
    case 0n q:
      {==}
    case 1n+p 0n:
      pu.le_refl(1n+p)
    case 1n+p 1n+q:
      pu.le_succ_r(Nat.sub(p, q), p, pu.sub_le_self(p, q))

# x - n <= f when x <= 1 + f and n >= 1
def pu.sub_fuel(+x: Nat, +f: Nat, +n: Nat, +ex: {Nat.is_le(x, 1n+f) == True{} : Bool}, +en: {Nat.is_le(1n, n) == True{} : Bool}) -> {Nat.is_le(Nat.sub(x, n), f) == True{} : Bool}:
  match x n:
    case p 0n:
      pu.absurd_ft({Nat.is_le(Nat.sub(p, 0n), f) == True{} : Bool}, en)
    case 0n 1n+q:
      pu.le_zero(f)
    case 1n+p 1n+q:
      pu.le_trans(Nat.sub(p, q), p, f, pu.sub_le_self(p, q), ex)

def pf.OD(v: Fs.Open, A: Type) -> Type:
  match v:
    case Fs.Opened{p}:
      A
    case Fs.NeedsCwd{}:
      Unit
    case Fs.Gone{p}:
      Unit
    case Fs.NotDir{p}:
      Unit

def pf.needs_opened(-A: Type, +p: Nat, e: {Fs.NeedsCwd{} == Fs.Opened{p} : Fs.Open}) -> A:
  %e : pf.OD(_, A)
  Unit{}

def pf.gone_opened(-A: Type, +q: Nat, +p: Nat, e: {Fs.Gone{q} == Fs.Opened{p} : Fs.Open}) -> A:
  %e : pf.OD(_, A)
  Unit{}

def pf.notdir_opened(-A: Type, +q: Nat, +p: Nat, e: {Fs.NotDir{q} == Fs.Opened{p} : Fs.Open}) -> A:
  %e : pf.OD(_, A)
  Unit{}

# The working dir of a session
# ----------------------------

def pf.opened_p(o: Fs.Open) -> Nat:
  match o:
    case Fs.Opened{p}:
      p
    case Fs.NeedsCwd{}:
      0n
    case Fs.Gone{p}:
      0n
    case Fs.NotDir{p}:
      0n

def explicit(c: Fs.Cwd, +p: Nat, ok: {Fs.open(c) == Fs.Opened{p} : Fs.Open}) -> {c == Fs.DirCwd{p} : Fs.Cwd}:
  match c:
    case Fs.NoCwd{}:
      pf.needs_opened({Fs.NoCwd{} == Fs.DirCwd{p} : Fs.Cwd}, p, ok)
    case Fs.GoneCwd{q}:
      pf.gone_opened({Fs.GoneCwd{q} == Fs.DirCwd{p} : Fs.Cwd}, q, p, ok)
    case Fs.FileCwd{q}:
      pf.notdir_opened({Fs.FileCwd{q} == Fs.DirCwd{p} : Fs.Cwd}, q, p, ok)
    case Fs.DirCwd{q}:
      Equal.cong(Nat, Fs.Cwd, n => Fs.DirCwd{n}, q, p, Equal.cong(Fs.Open, Nat, pf.opened_p, Fs.Opened{q}, Fs.Opened{p}, ok))

# ---- path_policy ----

# proof_path_policy: the (G1) laws (LAWS.bend section path_policy) of the path
# policy model in bend/path_policy.bend.
#
# A resolution keeps its invariant `looped or linkfree(at)`: a name it
# pushes is no link (the link test is the `look` it carries), `..` keeps
# a prefix, and a link's target starts from `/` or from the link's
# directory (`pp.go_lf`). The class picks Secret first and Inside last
# (`pp.pick_inside`, `pp.pick_guarded`); `demote` only moves Inside to
# Outside. A gated effect (outside, protected, secret: code 4 and up) is
# never grantable, so a write that is not Inside, or a read of a secret,
# reduces to the user's answer. A write that runs without a yes is Inside,
# so its real location is not guarded, and a write there leaves every
# guarded cell as it was (`pp.guarded_set`).

# Logic
# -----

def path_policy.pp.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pp.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : path_policy.pp.BD(_, Unit, A)
  Unit{}

# A at Inside, Unit elsewhere: refutes {c == Inside} for c not Inside
def pp.CM(c: Pp.Cls, A: Type) -> Type:
  match c:
    case Pp.Inside{}:
      A
    case Pp.Outside{}:
      Unit
    case Pp.Protected{}:
      Unit
    case Pp.Secret{}:
      Unit

def pp.not_inside(-A: Type, c: Pp.Cls, n: {Pp.Cls.inside(c) == False{} : Bool}, e: {c == Pp.Inside{} : Pp.Cls}) -> A:
  match c:
    case Pp.Inside{}:
      pp.absurd(A, n)
    case Pp.Outside{}:
      %e : pp.CM(_, A)
      Unit{}
    case Pp.Protected{}:
      %e : pp.CM(_, A)
      Unit{}
    case Pp.Secret{}:
      %e : pp.CM(_, A)
      Unit{}

# ---- approvals ----

# proof_approvals: the lemmas PROOF.bend proves the (G5) laws with
# (LAWS.bend section approvals), about the model in bend/approvals.bend.

# Logic
# -----

def approvals.pa.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def approvals.pa.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : approvals.pa.BD(_, A, Unit)
  Unit{}

# ---- retry_policy ----

# proof_retry_policy: the laws of LAWS.bend section retry over the model in
# bend/retry.bend. Most decisions are a match on their inputs, so most
# laws follow by case analysis. A clash of two values is refuted with a
# motive that sends the expected value to the goal and the other to Unit.
#
# - retry_never_parked, retry_never_limit, retry_status_first: the park
#   and the limit are matched first; then each side computes to the same
#   value.
# - retry_never_client_error, retry_server_errors, retry_only_retryable:
#   a helper takes the result of `Nat.is_lt(s, 500n)` as a Bool with its
#   equation, and matches on it. Below 500, the status must be listed;
#   at 500 or more, the status is a server error.
# - retry_kind_before_text: a known kind has a class that is not Unsure,
#   so the text is not read.
# - retry_after_respected: the wait is `Nat.max(jitter, s)`, and
#   `Nat.max_ge_r` gives that it is at least s. A refused wait sends no
#   retry.
# - retry_refuses_past_cap: the two premises make the refusal test True.
# - The failover laws: each pick (`pick.fresh`, `pick.back`) is shown, by
#   induction on its order list, to give only a switch that satisfies its
#   own Bool condition (the equation of the condition goes into
#   `pick.sel`); its switch is never the last provider, since the order
#   holds no last (`rp.order_notin`: the order's first part is above
#   last, its second part below it). `next` then goes through `next.last`, `next.budget` and
#   `next.mode` with the equations of the last attempt, the budget and
#   the all-seen test. From these facts, `good` gets the five `Switch`
#   checks together; each failover law takes one of them.
# - deferred_pays_once, deferred_bounded_in_time: a step never sends
#   while the job is live, and never polls a live job with 0 ms left.
#   Induction over the replies, with any start tally, shows that the run
#   adds 0 to each count.
# - deferred_failed_poll_repolls: the two premises make the repoll test
#   True.
# - stall_retry_extends: idle < idle + idle when idle > 0.
# - stall_detection_bounded: induction over the events, with any start
#   time: a stall ends at the last event plus the deadline, a close at
#   the last event, which is at most it plus the deadline.
# - stall_silent_ends_at_deadline: by computation.
# - The exact laws (retry_classifier_exact, retry_wait_*, retry_step_exact,
#   retry_jitter_*, failover_exact, the saturation laws, the anchors):
#   each model helper is shown equal to its spec helper of LAWS.bend by
#   induction (rx.tried, rx.wait, rx.fresh, rx.back, ...). The bounded
#   doubling `R.double` is min(rs.twice, cap) (rx.double): a halted step
#   has b + b past cap, and twice(j, b + b) >= b + b. A saturated server
#   wait (min(w, c), c above max) keeps every wait at most max and keeps
#   every wait past max past max (rx.cw_sel); a saturated base at or past
#   max doubles to max either way (rx.base_sat).

# Clashes
# -------

def rp.BD(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      Unit

def rp.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : rp.BD(_, A)
  Unit{}

def rp.ND(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      A

def rp.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : rp.ND(_, A)
  Unit{}

# Bools
# -----

def rp.or_l(a: Bool, -b: Bool, ea: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      rp.absurdF({Bool.or(False{}, b) == True{} : Bool}, ea)

def rp.or_r(a: Bool, -b: Bool, eb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      eb

def rp.and_tt(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      rp.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

def rp.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      rp.absurdF({False{} == True{} : Bool}, e)

def rp.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      rp.absurdF({b == True{} : Bool}, e)

# Numbers
# -------

def rp.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      rp.eq_refl(p)

def rp.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      rp.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      rp.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, rp.eq_true(p, q, h))

def rp.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (R3) The failover walk
# ----------------------

# what pick.fresh guarantees of its switch: no wait, not the last
# provider, not tried
def rp.fresh_ok(m: Maybe<&2, R.Switch>, +last: Nat, +ts: List<&2, R.Tried>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      match s:
        case R.Switch{+to, d}:
          Bool.and(Nat.is_eq(d, 0n), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts))))

# Order
# -----

# last is no element of xs
def rp.notin(+last: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest))

def rp.not_of_false(b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      rp.absurdT({Bool.not(True{}) == True{} : Bool}, e)
    case False{}:
      {==}

def rp.ne_of_lt(+last: Nat, +a: Nat, h: {Nat.is_lt(last, a) == True{} : Bool}) -> {Nat.is_eq(a, last) == False{} : Bool}:
  match last a:
    case 0n 0n:
      rp.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+p:
      {==}
    case 1n+q 0n:
      rp.absurdF({Nat.is_eq(0n, 1n+q) == False{} : Bool}, h)
    case 1n+q 1n+p:
      rp.ne_of_lt(q, p, h)

def rp.lt_succ(+last: Nat, +a: Nat, h: {Nat.is_lt(last, a) == True{} : Bool}) -> {Nat.is_lt(last, 1n+a) == True{} : Bool}:
  match last a:
    case 0n a:
      {==}
    case 1n+q 0n:
      rp.absurdF({Nat.is_lt(1n+q, 1n) == True{} : Bool}, h)
    case 1n+q 1n+p:
      rp.lt_succ(q, p, h)

def rp.lt_self(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      rp.lt_self(p)

# every element of upto(k, a) is at least a, so above last
def rp.notin_above(k: Nat, +a: Nat, +last: Nat, +h: {Nat.is_lt(last, a) == True{} : Bool}) -> {rp.notin(last, R.upto(k, a)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      rp.and_tt(Bool.not(Nat.is_eq(a, last)), rp.notin(last, R.upto(j, 1n+a)), rp.not_of_false(Nat.is_eq(a, last), rp.ne_of_lt(last, a, h)), rp.notin_above(j, 1n+a, last, rp.lt_succ(last, a, h)))

# shifting the list and last by one keeps the answer
def rp.notin_shift(k: Nat, +a: Nat, +last: Nat) -> {rp.notin(1n+last, R.upto(k, 1n+a)) == rp.notin(last, R.upto(k, a)) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %rp.notin_shift(j, 1n+a, last) : {Bool.and(Bool.not(Nat.is_eq(a, last)), rp.notin(1n+last, R.upto(j, 2n+a))) == Bool.and(Bool.not(Nat.is_eq(a, last)), _) : Bool}
      {==}

# every element of upto(k, 0) is below k, so below last when k <= last
def rp.notin_below(+k: Nat, +last: Nat, h: {Nat.is_le(k, last) == True{} : Bool}) -> {rp.notin(last, R.upto(k, 0n)) == True{} : Bool}:
  match k last:
    case 0n l:
      {==}
    case 1n+j 0n:
      rp.absurdF({rp.notin(0n, R.upto(1n+j, 0n)) == True{} : Bool}, h)
    case 1n+j 1n+q:
      %Equal.sym(Bool, rp.notin(1n+q, R.upto(j, 1n)), rp.notin(q, R.upto(j, 0n)), rp.notin_shift(j, 0n, q)) : {_ == True{} : Bool}
      rp.notin_below(j, q, h)

def rp.min_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rp.min_le(p, q)

def rp.notin_append(+last: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>, +hx: {rp.notin(last, xs) == True{} : Bool}, hy: {rp.notin(last, ys) == True{} : Bool}) -> {rp.notin(last, List.append(&2, Nat, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      ne = rp.and_l(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest), hx)
      nr = rp.and_r(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest), hx)
      rp.and_tt(Bool.not(Nat.is_eq(x, last)), rp.notin(last, List.append(&2, Nat, rest, ys)), ne, rp.notin_append(last, rest, ys, nr, hy))

# the chain order after last never holds last
def rp.order_notin(+last: Nat, +len: Nat) -> {rp.notin(last, R.order(last, len)) == True{} : Bool}:
  rp.notin_append(last, R.upto(Nat.sub(len, 1n+last), 1n+last), R.upto(Nat.min(last, len), 0n), rp.notin_above(Nat.sub(len, 1n+last), 1n+last, last, rp.lt_self(last)), rp.notin_below(Nat.min(last, len), last, rp.min_le(last, len)))

# The picks
# ---------

def rp.fresh_sel(c: Bool, +x: Nat, +last: Nat, +ts: List<&2, R.Tried>, r: Maybe<&2, R.Switch>, ec: {Bool.not(R.seen(x, ts)) == c : Bool}, ne: {Bool.not(Nat.is_eq(x, last)) == True{} : Bool}, ih: {rp.fresh_ok(r, last, ts) == True{} : Bool}) -> {rp.fresh_ok(R.pick.sel(c, R.Switch{x, 0n}, r), last, ts) == True{} : Bool}:
  match c:
    case True{}:
      rp.and_tt(Bool.not(Nat.is_eq(x, last)), Bool.not(R.seen(x, ts)), ne, ec)
    case False{}:
      ih

def rp.fresh_inv(xs: List<&2, Nat>, +last: Nat, +ts: List<&2, R.Tried>, +nin: {rp.notin(last, xs) == True{} : Bool}) -> {rp.fresh_ok(R.pick.fresh(xs, ts), last, ts) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      ne = rp.and_l(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest), nin)
      nr = rp.and_r(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest), nin)
      rp.fresh_sel(Bool.not(R.seen(x, ts)), x, last, ts, R.pick.fresh(rest, ts), {==}, ne, rp.fresh_inv(rest, last, ts, nr))

# what pick.back guarantees of its switch: the wait is the backoff, and
# never less than its server's wait; not the last provider; the wait is
# positive and at most max
def rp.back_ok(m: Maybe<&2, R.Switch>, +last: Nat, +ts: List<&2, R.Tried>, +backoff: Nat, +max: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      match s:
        case R.Switch{+to, +d}:
          Bool.and(Nat.is_eq(Nat.max(backoff, R.server(to, ts)), d), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, max))))

def rp.back_sel(c: Bool, +x: Nat, +last: Nat, +ts: List<&2, R.Tried>, +backoff: Nat, +max: Nat, r: Maybe<&2, R.Switch>, ec: {Bool.and(Nat.is_gt(Nat.max(backoff, R.server(x, ts)), 0n), Nat.is_le(Nat.max(backoff, R.server(x, ts)), max)) == c : Bool}, ne: {Bool.not(Nat.is_eq(x, last)) == True{} : Bool}, ih: {rp.back_ok(r, last, ts, backoff, max) == True{} : Bool}) -> {rp.back_ok(R.pick.sel(c, R.Switch{x, Nat.max(backoff, R.server(x, ts))}, r), last, ts, backoff, max) == True{} : Bool}:
  match c:
    case True{}:
      +w = Nat.max(backoff, R.server(x, ts))
      rp.and_tt(Nat.is_eq(w, w), Bool.and(Bool.not(Nat.is_eq(x, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, max))), Equal.sym(Bool, True{}, Nat.is_eq(w, w), rp.eq_refl(w)), rp.and_tt(Bool.not(Nat.is_eq(x, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, max)), ne, ec))
    case False{}:
      ih

def rp.back_inv(xs: List<&2, Nat>, +last: Nat, +ts: List<&2, R.Tried>, +backoff: Nat, +max: Nat, +nin: {rp.notin(last, xs) == True{} : Bool}) -> {rp.back_ok(R.pick.back(xs, ts, backoff, max), last, ts, backoff, max) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      ne = rp.and_l(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest), nin)
      nr = rp.and_r(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest), nin)
      rp.back_sel(Bool.and(Nat.is_gt(Nat.max(backoff, R.server(x, ts)), 0n), Nat.is_le(Nat.max(backoff, R.server(x, ts)), max)), x, last, ts, backoff, max, R.pick.back(rest, ts, backoff, max), {==}, ne, rp.back_inv(rest, last, ts, backoff, max, nr))

# the five checks of a switch together
def rp.Good(m: Maybe<&2, R.Switch>, len: Nat, ts: List<&2, R.Tried>, p: R.Policy) -> Type:
  {R.Switch.not_last(m, ts) == True{} : Bool} & ({R.Switch.fresh_first(m, len, ts) == True{} : Bool} & ({R.Switch.return_waits(m, ts) == True{} : Bool} & ({R.Switch.capped(m, R.Policy.max(p)) == True{} : Bool} & {R.Switch.within(m, ts, p) == True{} : Bool})))

def rp.good_none(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> rp.Good(None{}, len, ts, p):
  ({==}, ({==}, ({==}, ({==}, {==}))))

def rp.not_eq_move(+to: Nat, -a: Nat, -b: Nat, e: {a == b : Nat}, h: {Bool.not(Nat.is_eq(to, a)) == True{} : Bool}) -> {Bool.not(Nat.is_eq(to, b)) == True{} : Bool}:
  %e : {Bool.not(Nat.is_eq(to, _)) == True{} : Bool}
  h

def rp.ge_move(-a: Nat, -b: Nat, +c: Nat, e: {a == b : Nat}, h: {Nat.is_ge(a, c) == True{} : Bool}) -> {Nat.is_ge(b, c) == True{} : Bool}:
  %e : {Nat.is_ge(_, c) == True{} : Bool}
  h

def rp.fresh_good(m: Maybe<&2, R.Switch>, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, +hf: {rp.fresh_ok(m, last, ts) == True{} : Bool}, elast: {last == R.last_at(ts) : Nat}, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == True{} : Bool}) -> rp.Good(m, len, ts, p):
  match m:
    case None{}:
      rp.good_none(len, ts, p)
    case Some{s}:
      match s:
        case R.Switch{+to, d}:
          match d:
            case 0n:
              nl = rp.and_l(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), hf)
              +fr = rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), hf)
              nl2 = rp.not_eq_move(to, last, R.last_at(ts), elast, nl)
              ff = rp.or_l(Bool.not(R.seen(to, ts)), R.all_seen(len, ts), fr)
              rw = rp.or_l(Bool.not(R.seen(to, ts)), Bool.and(Nat.is_gt(0n, 0n), Nat.is_ge(0n, R.server(to, ts))), fr)
              (nl2, (ff, (rw, (rp.le_zero(R.Policy.max(p)), eok))))
            case 1n+k:
              rp.absurdF(rp.Good(Some{R.Switch{to, 1n+k}}, len, ts, p), hf)

def rp.back_good(m: Maybe<&2, R.Switch>, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, +backoff: Nat, +hb: {rp.back_ok(m, last, ts, backoff, R.Policy.max(p)) == True{} : Bool}, eall: {R.all_seen(len, ts) == True{} : Bool}, elast: {last == R.last_at(ts) : Nat}, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == True{} : Bool}) -> rp.Good(m, len, ts, p):
  match m:
    case None{}:
      rp.good_none(len, ts, p)
    case Some{s}:
      match s:
        case R.Switch{+to, +d}:
          +rest = rp.and_r(Nat.is_eq(Nat.max(backoff, R.server(to, ts)), d), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)))), hb)
          deq = rp.eq_true(Nat.max(backoff, R.server(to, ts)), d, rp.and_l(Nat.is_eq(Nat.max(backoff, R.server(to, ts)), d), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)))), hb))
          nl = rp.and_l(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p))), rest)
          +wc = rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p))), rest)
          pos = rp.and_l(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)), wc)
          cap = rp.and_r(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)), wc)
          nl2 = rp.not_eq_move(to, last, R.last_at(ts), elast, nl)
          ge = rp.ge_move(Nat.max(backoff, R.server(to, ts)), d, R.server(to, ts), deq, Nat.max_ge_r(backoff, R.server(to, ts)))
          ff = rp.or_r(Bool.not(R.seen(to, ts)), R.all_seen(len, ts), eall)
          rw = rp.or_r(Bool.not(R.seen(to, ts)), Bool.and(Nat.is_gt(d, 0n), Nat.is_ge(d, R.server(to, ts))), rp.and_tt(Nat.is_gt(d, 0n), Nat.is_ge(d, R.server(to, ts)), pos, ge))
          (nl2, (ff, (rw, (cap, eok))))

def rp.mode_good(all: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, eall: {R.all_seen(len, ts) == all : Bool}, elast: {last == R.last_at(ts) : Nat}, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == True{} : Bool}) -> rp.Good(R.next.mode(all, last, len, ts, p), len, ts, p):
  match all:
    case True{}:
      rp.back_good(R.pick.back(R.order(last, len), ts, R.backoff(p, len, ts), R.Policy.max(p)), last, len, ts, p, R.backoff(p, len, ts), rp.back_inv(R.order(last, len), last, ts, R.backoff(p, len, ts), R.Policy.max(p), rp.order_notin(last, len)), eall, elast, eok)
    case False{}:
      rp.fresh_good(R.pick.fresh(R.order(last, len), ts), last, len, ts, p, rp.fresh_inv(R.order(last, len), last, ts, rp.order_notin(last, len)), elast, eok)

def rp.budget_good(ok: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == ok : Bool}, elast: {last == R.last_at(ts) : Nat}) -> rp.Good(R.next.budget(ok, last, len, ts, p), len, ts, p):
  match ok:
    case True{}:
      rp.mode_good(R.all_seen(len, ts), last, len, ts, p, {==}, elast, eok)
    case False{}:
      rp.good_none(len, ts, p)

def rp.last_good(m: Maybe<&2, R.Tried>, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, em: {m == R.last(ts) : Maybe<&2, R.Tried>}) -> rp.Good(R.next.last(m, len, ts, p), len, ts, p):
  match m:
    case None{}:
      rp.good_none(len, ts, p)
    case Some{+t}:
      rp.budget_good(Nat.is_le(R.length(ts), R.Policy.switches(p)), R.Tried.at(t), len, ts, p, {==}, Equal.cong(Maybe<&2, R.Tried>, Nat, R.at_of, Some{t}, R.last(ts), em))

def good(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> rp.Good(R.next(len, ts, p), len, ts, p):
  rp.last_good(R.last(ts), len, ts, p, {==})

def documents.ps.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

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
