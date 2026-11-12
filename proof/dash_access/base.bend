# eukhe: lemmas shared by the proofs of area dash_access: what the code
# reads from a written authority (dab.split_spell: a well-formed writing
# reads as its host and port) and what a text the code reads as an
# authority is (dab.split_inv: the writing of a well-formed authority), the
# same for the origin's "://" cut and its scheme, and the code's name test
# against the spec's ASCII-case comparison

import Base
import ../../bend/dash_access.bend as Ac
import ../../laws/dash_access.bend as DashAccess
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../base/nat.bend as LNat
import ../base/staging.bend as LStg

# every length fits, as the doc_commit spec says it (its list lemmas are
# reused)
def dab.fits(xs: List<&2, String>) -> {DashAccess.sp_fit_strs(xs) == DocCommit.sp_fit_strs(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %dab.fits(t) : {Bool.and(LawsBase.wire_fits(String.length(x)), DashAccess.sp_fit_strs(t)) == Bool.and(LawsBase.wire_fits(String.length(x)), _) : Bool}
      {==}

# Logic
# -----

def dab.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def dab.absurdF(-A: Type, +e: {False{} == True{} : Bool}) -> A:
  %e : dab.BD(_, A, Unit)
  Unit{}

def dab.absurdT(-A: Type, +e: {True{} == False{} : Bool}) -> A:
  %e : dab.BD(_, Unit, A)
  Unit{}

def dab.and_l(+a: Bool, -b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def dab.and_r(+a: Bool, -b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      dab.absurdF({b == True{} : Bool}, e)

def dab.or_l(+a: Bool, -b: Bool, +e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

def dab.or_r(+a: Bool, -b: Bool, +e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      dab.absurdT({b == False{} : Bool}, e)
    case False{}:
      e

def dab.not_t(+a: Bool, +e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Equal.sym(Bool, False{}, True{}, e)
    case False{}:
      {==}

def dab.not_f(+a: Bool, +e: {a == False{} : Bool}) -> {Bool.not(a) == True{} : Bool}:
  %Equal.sym(Bool, a, False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

def dab.and_tt(-a: Bool, -b: Bool, +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def dab.or_ff(-a: Bool, -b: Bool, +ea: {a == False{} : Bool}, +eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ea) : {Bool.or(_, b) == False{} : Bool}
  eb

def dab.or_true_r(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def dab.or_true_r_eq(a: Bool, -b: Bool, +e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, b, True{}, e) : {Bool.or(a, _) == True{} : Bool}
  dab.or_true_r(a)

# the head of a text, d if empty
def dab.head(s: String, d: Char) -> Char:
  match s:
    case SNil{}:
      d
    case SCon{+c, +t}:
      c

def dab.tail(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      t

# Chars
# -----

# a digit is not k when k is no digit
def dab.dig_ne.at(+c: Char, +k: Char, b: Bool, +eb: {Char.is_eq(c, k) == b : Bool}, +hd: {Char.is_digit(c) == True{} : Bool}, +hk: {Char.is_digit(k) == False{} : Bool}) -> {Char.is_eq(c, k) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +eck = LStg.stg.char_sound(c, k, eb)
      +t1 = Equal.trans(Bool, True{}, Char.is_digit(c), Char.is_digit(k), Equal.sym(Bool, Char.is_digit(c), True{}, hd), Equal.cong(Char, Bool, z => Char.is_digit(z), c, k, eck))
      dab.absurdT({Char.is_eq(c, k) == False{} : Bool}, Equal.trans(Bool, True{}, Char.is_digit(k), False{}, t1, hk))

def dab.dig_ne(+c: Char, +k: Char, +hd: {Char.is_digit(c) == True{} : Bool}, +hk: {Char.is_digit(k) == False{} : Bool}) -> {Char.is_eq(c, k) == False{} : Bool}:
  dab.dig_ne.at(c, k, Char.is_eq(c, k), {==}, hd, hk)

# Scans: the code's are the spec's
# -------------------------------

def dab.stops(s: String) -> {Ac.stops(s) == DashAccess.sp_holds(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %dab.stops(t) : {Bool.or(Ac.stop(c), Ac.stops(t)) == Bool.or(DashAccess.sp_forbidden(c), _) : Bool}
      {==}

def dab.colons(s: String) -> {Ac.colons(s) == DashAccess.sp_has(s, ':') : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %dab.colons(t) : {Bool.or(Char.is_eq(c, ':'), Ac.colons(t)) == Bool.or(Char.is_eq(c, ':'), _) : Bool}
      {==}

def dab.same(a: String, b: String) -> {Ac.same(a, b) == DashAccess.sp_ci(a, b) : Bool}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, v}:
      {==}
    case SCon{+x, +u} SNil{}:
      {==}
    case SCon{+x, +u} SCon{y, v}:
      %dab.same(u, v) : {Bool.and(Char.is_eq(Char.to_lower(x), Char.to_lower(y)), Ac.same(u, v)) == Bool.and(Char.is_eq(Char.to_lower(x), Char.to_lower(y)), _) : Bool}
      {==}

def dab.among(+n: String, xs: List<&2, String>) -> {Ac.among(n, xs) == DashAccess.sp_any_ci(n, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %dab.same(x, n) : {Bool.or(Ac.same(x, n), Ac.among(n, t)) == Bool.or(_, DashAccess.sp_any_ci(n, t)) : Bool}
      %dab.among(n, t) : {Bool.or(Ac.same(x, n), Ac.among(n, t)) == Bool.or(Ac.same(x, n), _) : Bool}
      {==}

def dab.or3(a: Bool, b: Bool, c: Bool, -d: Bool) -> {Bool.or(Bool.or(a, Bool.or(b, Bool.or(c, False{}))), d) == Bool.or(a, Bool.or(b, Bool.or(c, d))) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}

# the code's host test is R2's
def dab.named(+n: String, -p: Maybe<&2, Nat>, +al: List<&2, String>) -> {Ac.host_allowed.of(Ac.HostPort{n, p}, al) == DashAccess.sp_named(n, al) : Bool}:
  %Equal.sym(Bool, Ac.among(n, Ac.loopback()), DashAccess.sp_any_ci(n, Ac.loopback()), dab.among(n, Ac.loopback())) : {Bool.or(_, Ac.among(n, al)) == DashAccess.sp_named(n, al) : Bool}
  %Equal.sym(Bool, Ac.among(n, al), DashAccess.sp_any_ci(n, al), dab.among(n, al)) : {Bool.or(DashAccess.sp_any_ci(n, Ac.loopback()), _) == DashAccess.sp_named(n, al) : Bool}
  dab.or3(DashAccess.sp_ci("127.0.0.1", n), DashAccess.sp_ci("localhost", n), DashAccess.sp_ci("[::1]", n), DashAccess.sp_any_ci(n, al))

def dab.port_or(m: Maybe<&2, Nat>, d: Nat) -> {Ac.port_or(m, d) == DashAccess.sp_port_or(m, d) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{+n}:
      {==}

def dab.append_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.cong(String, String, z => SCon{c, z}, String.append(t, SNil{}), t, dab.append_nil(t))

# Numbers
# -------

# acc is at most 10 acc + d
def dab.le10(+acc: Nat, +d: Nat) -> {Nat.is_le(acc, Nat.add(Nat.mul(10n, acc), d)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(acc, Nat.mul(9n, acc)), d), Nat.add(acc, Nat.add(Nat.mul(9n, acc), d)), LNat.add_assoc(acc, Nat.mul(9n, acc), d)) : {Nat.is_le(acc, _) == True{} : Bool}
  LNat.pu.le_add_r(acc, Nat.add(Nat.mul(9n, acc), d))

# the value after acc is at least acc
def dab.mono.go(s: String, +acc: Nat) -> {Nat.is_le(acc, DashAccess.sp_value(acc, s)) == True{} : Bool}:
  match s:
    case SNil{}:
      LNat.pu.le_refl(acc)
    case SCon{+c, +t}:
      +x = Nat.add(Nat.mul(10n, acc), Ac.digit(c))
      LNat.pu.le_trans(acc, x, DashAccess.sp_value(x, t), dab.le10(acc, Ac.digit(c)), dab.mono.go(t, x))

def dab.mono(+acc: Nat, s: String) -> {Nat.is_le(acc, DashAccess.sp_value(acc, s)) == True{} : Bool}:
  dab.mono.go(s, acc)

def dab.cap_id(+x: Nat, +h: {Nat.is_le(x, 65535n) == True{} : Bool}) -> {Ac.cap(x) == x : Nat}:
  %Equal.sym(Bool, Nat.is_le(x, 65535n), True{}, h) : {Ac.cap.at(_, x) == x : Nat}
  {==}

def dab.cap_le.at(b: Bool, +x: Nat, +e: {Nat.is_le(x, 65535n) == b : Bool}) -> {Nat.is_le(Ac.cap.at(b, x), 65536n) == True{} : Bool}:
  match b:
    case True{}:
      LNat.pu.le_succ_r(x, 65535n, e)
    case False{}:
      {==}

# the cap stays within 65536
def dab.cap_le(+x: Nat) -> {Nat.is_le(Ac.cap(x), 65536n) == True{} : Bool}:
  dab.cap_le.at(Nat.is_le(x, 65535n), x, {==})

def dab.cap_ge.at(+b: Bool, +y: Nat, +x: Nat, +e: {Nat.is_le(x, 65535n) == b : Bool}, +hx: {Nat.is_le(y, x) == True{} : Bool}, +hy: {Nat.is_le(y, 65536n) == True{} : Bool}) -> {Nat.is_le(y, Ac.cap.at(b, x)) == True{} : Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the cap keeps every bound up to 65536
def dab.cap_ge(+y: Nat, +x: Nat, +hx: {Nat.is_le(y, x) == True{} : Bool}, +hy: {Nat.is_le(y, 65536n) == True{} : Bool}) -> {Nat.is_le(y, Ac.cap(x)) == True{} : Bool}:
  dab.cap_ge.at(Nat.is_le(x, 65535n), y, x, {==}, hx, hy)

def dab.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      dab.eq_refl(p)

def dab.eq_sound(a: Nat, b: Nat, +e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      dab.absurdF({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      dab.absurdF({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, p, q, dab.eq_sound(p, q, e))

# a + 1 <= b: a < b
def dab.lt_of_le(a: Nat, b: Nat, +e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      dab.absurdF({Nat.is_lt(0n, 0n) == True{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      dab.absurdF({Nat.is_lt(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      dab.lt_of_le(p, q, e)

# Ports, read forth
# -----------------

# well-formed digits read as their value
def dab.digits(s: String, +acc: Nat, +hd: {DashAccess.sp_all_digits(s) == True{} : Bool}, +hv: {Nat.is_le(DashAccess.sp_value(acc, s), 65535n) == True{} : Bool}) -> {Ac.digits(s, acc) == Some{DashAccess.sp_value(acc, s)} : Maybe<&2, Nat>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +x = Nat.add(Nat.mul(10n, acc), Ac.digit(c))
      +hd2 = hd
      +hx = LNat.pu.le_trans(x, DashAccess.sp_value(x, t), 65535n, dab.mono(x, t), hv)
      %Equal.sym(Bool, Char.is_digit(c), True{}, dab.and_l(Char.is_digit(c), DashAccess.sp_all_digits(t), hd2)) : {Ac.digits.keep(_, Ac.digits(t, Ac.cap(x))) == Some{DashAccess.sp_value(x, t)} : Maybe<&2, Nat>}
      %Equal.sym(Nat, Ac.cap(x), x, dab.cap_id(x, hx)) : {Ac.digits(t, _) == Some{DashAccess.sp_value(x, t)} : Maybe<&2, Nat>}
      dab.digits(t, x, dab.and_r(Char.is_digit(c), DashAccess.sp_all_digits(t), hd2), hv)

def dab.num(+c: Char, +t: String, +hd: {DashAccess.sp_all_digits(SCon{c, t}) == True{} : Bool}, +hv: {Nat.is_le(DashAccess.sp_value(0n, SCon{c, t}), 65535n) == True{} : Bool}) -> {Ac.num(SCon{c, t}) == Some{DashAccess.sp_value(0n, SCon{c, t})} : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, Ac.digits(SCon{c, t}, 0n), Some{DashAccess.sp_value(0n, SCon{c, t})}, dab.digits(SCon{c, t}, 0n, hd, hv)) : {Ac.num.fit(_) == Some{DashAccess.sp_value(0n, SCon{c, t})} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Nat.is_le(DashAccess.sp_value(0n, SCon{c, t}), 65535n), True{}, hv) : {Ac.num.fit.at(_, DashAccess.sp_value(0n, SCon{c, t})) == Some{DashAccess.sp_value(0n, SCon{c, t})} : Maybe<&2, Nat>}
  {==}

def dab.port.pl(plus: Bool, +c: Char, +t: String, +hd: {DashAccess.sp_all_digits(SCon{c, t}) == True{} : Bool}, +hv: {Nat.is_le(DashAccess.sp_value(0n, SCon{c, t}), 65535n) == True{} : Bool}) -> {Ac.port(DashAccess.sp_sign(plus, SCon{c, t})) == Some{DashAccess.sp_value(0n, SCon{c, t})} : Maybe<&2, Nat>}:
  match plus:
    case True{}:
      dab.num(c, t, hd, hv)
    case False{}:
      +hc = dab.and_l(Char.is_digit(c), DashAccess.sp_all_digits(t), hd)
      %Equal.sym(Bool, Char.is_eq(c, '+'), False{}, dab.dig_ne(c, '+', hc, {==})) : {Ac.port.sign(_, c, t) == Some{DashAccess.sp_value(0n, SCon{c, t})} : Maybe<&2, Nat>}
      dab.num(c, t, hd, hv)

# a well-formed port reads as its value
def dab.port(+plus: Bool, +ds: String, +ok: {DashAccess.sp_port_ok(Some{DashAccess.SpPort{plus, ds}}) == True{} : Bool}) -> {Ac.port(DashAccess.sp_sign(plus, ds)) == Some{DashAccess.sp_value(0n, ds)} : Maybe<&2, Nat>}:
  match ds:
    case SNil{}:
      dab.absurdF({Ac.port(DashAccess.sp_sign(plus, SNil{})) == Some{DashAccess.sp_value(0n, SNil{})} : Maybe<&2, Nat>}, ok)
    case SCon{+c, +t}:
      +ok2 = dab.and_r(Bool.not(String.is_empty(SCon{c, t})), Bool.and(DashAccess.sp_all_digits(SCon{c, t}), Nat.is_le(DashAccess.sp_value(0n, SCon{c, t}), 65535n)), ok)
      +hd = dab.and_l(DashAccess.sp_all_digits(SCon{c, t}), Nat.is_le(DashAccess.sp_value(0n, SCon{c, t}), 65535n), ok2)
      +hv = dab.and_r(DashAccess.sp_all_digits(SCon{c, t}), Nat.is_le(DashAccess.sp_value(0n, SCon{c, t}), 65535n), ok2)
      dab.port.pl(plus, c, t, hd, hv)

# a text without ':' has no last ':'
def dab.last_none(s: String, +h: {DashAccess.sp_has(s, ':') == False{} : Bool}) -> {Ac.last(s) == None{} : Maybe<&2, Ac.Cut>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h2 = h
      %Equal.sym(Maybe<&2, Ac.Cut>, Ac.last(t), None{}, dab.last_none(t, dab.or_r(Char.is_eq(c, ':'), DashAccess.sp_has(t, ':'), h2))) : {Ac.last.at(c, t, _) == None{} : Maybe<&2, Ac.Cut>}
      %Equal.sym(Bool, Char.is_eq(c, ':'), False{}, dab.or_l(Char.is_eq(c, ':'), DashAccess.sp_has(t, ':'), h2)) : {Ac.last.here(_, t) == None{} : Maybe<&2, Ac.Cut>}
      {==}

# digits hold no ':'
def dab.digits_nocolon(s: String, +hd: {DashAccess.sp_all_digits(s) == True{} : Bool}) -> {DashAccess.sp_has(s, ':') == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +hd2 = hd
      dab.or_ff(Char.is_eq(c, ':'), DashAccess.sp_has(t, ':'), dab.dig_ne(c, ':', dab.and_l(Char.is_digit(c), DashAccess.sp_all_digits(t), hd2), {==}), dab.digits_nocolon(t, dab.and_r(Char.is_digit(c), DashAccess.sp_all_digits(t), hd2)))

def dab.sign_nocolon(plus: Bool, +ds: String, +hd: {DashAccess.sp_all_digits(ds) == True{} : Bool}) -> {DashAccess.sp_has(DashAccess.sp_sign(plus, ds), ':') == False{} : Bool}:
  match plus:
    case True{}:
      dab.digits_nocolon(ds, hd)
    case False{}:
      dab.digits_nocolon(ds, hd)

# the last ':' is the one before the port
def dab.last_any(+n: String, +p: String, +np: {Ac.last(p) == None{} : Maybe<&2, Ac.Cut>}) -> {Ac.last(String.append(n, SCon{':', p})) == Some{Ac.Cut{n, p}} : Maybe<&2, Ac.Cut>}:
  match n:
    case SNil{}:
      %Equal.sym(Maybe<&2, Ac.Cut>, Ac.last(p), None{}, np) : {Ac.last.at(':', p, _) == Some{Ac.Cut{SNil{}, p}} : Maybe<&2, Ac.Cut>}
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, Ac.Cut>, Ac.last(String.append(t, SCon{':', p})), Some{Ac.Cut{t, p}}, dab.last_any(t, p, np)) : {Ac.last.at(c, String.append(t, SCon{':', p}), _) == Some{Ac.Cut{SCon{c, t}, p}} : Maybe<&2, Ac.Cut>}
      {==}

# an inside without ']' closes at the ']' after it
def dab.close_app(i: String, +r: String, +h: {DashAccess.sp_has(i, ']') == False{} : Bool}) -> {Ac.close(String.append(i, SCon{']', r})) == Some{Ac.Cut{String.append(i, "]"), r}} : Maybe<&2, Ac.Cut>}:
  match i:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h2 = h
      +x = String.append(t, SCon{']', r})
      %Equal.sym(Maybe<&2, Ac.Cut>, Ac.close(x), Some{Ac.Cut{String.append(t, "]"), r}}, dab.close_app(t, r, dab.or_r(Char.is_eq(c, ']'), DashAccess.sp_has(t, ']'), h2))) : {Ac.close.at(Char.is_eq(c, ']'), c, x, _) == Some{Ac.Cut{SCon{c, String.append(t, "]")}, r}} : Maybe<&2, Ac.Cut>}
      %Equal.sym(Bool, Char.is_eq(c, ']'), False{}, dab.or_l(Char.is_eq(c, ']'), DashAccess.sp_has(t, ']'), h2)) : {Ac.close.at(_, c, x, Some{Ac.Cut{String.append(t, "]"), r}}) == Some{Ac.Cut{SCon{c, String.append(t, "]")}, r}} : Maybe<&2, Ac.Cut>}
      {==}

# Authorities, read forth
# -----------------------

def dab.after_port(+n: String, p: Maybe<&2, DashAccess.SpPort>, +ok: {DashAccess.sp_port_ok(p) == True{} : Bool}) -> {Ac.after(n, DashAccess.sp_port_text(p)) == Ac.HostPort{n, DashAccess.sp_port_of(p)} : Ac.Authority}:
  match p:
    case None{}:
      {==}
    case Some{+q}:
      match q:
        case DashAccess.SpPort{+plus, +ds}:
          %Equal.sym(Maybe<&2, Nat>, Ac.port(DashAccess.sp_sign(plus, ds)), Some{DashAccess.sp_value(0n, ds)}, dab.port(plus, ds, ok)) : {Ac.with_port(n, _) == Ac.HostPort{n, Some{DashAccess.sp_value(0n, ds)}} : Ac.Authority}
          {==}

def dab.plain_port(+h: String, p: Maybe<&2, DashAccess.SpPort>, +ok: {DashAccess.sp_port_ok(p) == True{} : Bool}, +hc: {DashAccess.sp_has(h, ':') == False{} : Bool}, +he: {String.is_empty(h) == False{} : Bool}) -> {Ac.plain(String.append(h, DashAccess.sp_port_text(p)), Ac.last(String.append(h, DashAccess.sp_port_text(p)))) == Ac.HostPort{h, DashAccess.sp_port_of(p)} : Ac.Authority}:
  match p:
    case None{}:
      %Equal.sym(String, String.append(h, SNil{}), h, dab.append_nil(h)) : {Ac.plain(_, Ac.last(_)) == Ac.HostPort{h, None{}} : Ac.Authority}
      %Equal.sym(Maybe<&2, Ac.Cut>, Ac.last(h), None{}, dab.last_none(h, hc)) : {Ac.plain(h, _) == Ac.HostPort{h, None{}} : Ac.Authority}
      %Equal.sym(Bool, Ac.colons(h), False{}, Equal.trans(Bool, Ac.colons(h), DashAccess.sp_has(h, ':'), False{}, dab.colons(h), hc)) : {Ac.plain.host(Bool.or(String.is_empty(h), _), h, None{}) == Ac.HostPort{h, None{}} : Ac.Authority}
      %Equal.sym(Bool, String.is_empty(h), False{}, he) : {Ac.plain.host(Bool.or(_, False{}), h, None{}) == Ac.HostPort{h, None{}} : Ac.Authority}
      {==}
    case Some{+q}:
      match q:
        case DashAccess.SpPort{+plus, +ds}:
          +ok2 = ok
          +hd = dab.and_l(DashAccess.sp_all_digits(ds), Nat.is_le(DashAccess.sp_value(0n, ds), 65535n), dab.and_r(Bool.not(String.is_empty(ds)), Bool.and(DashAccess.sp_all_digits(ds), Nat.is_le(DashAccess.sp_value(0n, ds), 65535n)), ok2))
          +pt = DashAccess.sp_sign(plus, ds)
          %Equal.sym(Maybe<&2, Ac.Cut>, Ac.last(String.append(h, SCon{':', pt})), Some{Ac.Cut{h, pt}}, dab.last_any(h, pt, dab.last_none(pt, dab.sign_nocolon(plus, ds, hd)))) : {Ac.plain(String.append(h, SCon{':', pt}), _) == Ac.HostPort{h, Some{DashAccess.sp_value(0n, ds)}} : Ac.Authority}
          %Equal.sym(Bool, Ac.colons(h), False{}, Equal.trans(Bool, Ac.colons(h), DashAccess.sp_has(h, ':'), False{}, dab.colons(h), hc)) : {Ac.plain.host(Bool.or(String.is_empty(h), _), h, Some{pt}) == Ac.HostPort{h, Some{DashAccess.sp_value(0n, ds)}} : Ac.Authority}
          %Equal.sym(Bool, String.is_empty(h), False{}, he) : {Ac.plain.host(Bool.or(_, False{}), h, Some{pt}) == Ac.HostPort{h, Some{DashAccess.sp_value(0n, ds)}} : Ac.Authority}
          %Equal.sym(Maybe<&2, Nat>, Ac.port(pt), Some{DashAccess.sp_value(0n, ds)}, dab.port(plus, ds, ok2)) : {Ac.with_port(h, _) == Ac.HostPort{h, Some{DashAccess.sp_value(0n, ds)}} : Ac.Authority}
          {==}

def dab.split_parts(a: DashAccess.SpAuth, +hs: {Ac.stops(DashAccess.sp_spell(a)) == False{} : Bool}, +hp: {DashAccess.sp_well.parts(a) == True{} : Bool}) -> {Ac.split(DashAccess.sp_spell(a)) == Ac.HostPort{DashAccess.sp_name(a), DashAccess.sp_port(a)} : Ac.Authority}:
  match a:
    case DashAccess.SpPlain{+h, +p}:
      match h:
        case SNil{}:
          dab.absurdF({Ac.split(DashAccess.sp_spell(DashAccess.SpPlain{SNil{}, p})) == Ac.HostPort{SNil{}, DashAccess.sp_port_of(p)} : Ac.Authority}, hp)
        case SCon{+c, +t}:
          +hp2 = hp
          +hk = dab.and_l(DashAccess.sp_plain_ok(SCon{c, t}), DashAccess.sp_port_ok(p), hp2)
          +hq = dab.and_r(DashAccess.sp_plain_ok(SCon{c, t}), DashAccess.sp_port_ok(p), hp2)
          +hb = dab.not_t(Char.is_eq(c, '['), dab.and_l(Bool.not(Char.is_eq(c, '[')), Bool.not(DashAccess.sp_has(SCon{c, t}, ':')), hk))
          +hc = dab.not_t(DashAccess.sp_has(SCon{c, t}, ':'), dab.and_r(Bool.not(Char.is_eq(c, '[')), Bool.not(DashAccess.sp_has(SCon{c, t}, ':')), hk))
          +r = String.append(t, DashAccess.sp_port_text(p))
          %Equal.sym(Bool, Ac.stops(SCon{c, r}), False{}, hs) : {Ac.split.ok(_, c, r) == Ac.HostPort{SCon{c, t}, DashAccess.sp_port_of(p)} : Ac.Authority}
          %Equal.sym(Bool, Char.is_eq(c, '['), False{}, hb) : {Ac.split.form(_, SCon{c, r}) == Ac.HostPort{SCon{c, t}, DashAccess.sp_port_of(p)} : Ac.Authority}
          dab.plain_port(SCon{c, t}, p, hq, hc, {==})
    case DashAccess.SpBracket{+i, +p}:
      +hp2 = hp
      +hi = dab.not_t(DashAccess.sp_has(i, ']'), dab.and_l(Bool.not(DashAccess.sp_has(i, ']')), DashAccess.sp_port_ok(p), hp2))
      +hq = dab.and_r(Bool.not(DashAccess.sp_has(i, ']')), DashAccess.sp_port_ok(p), hp2)
      +r = String.append(i, SCon{']', DashAccess.sp_port_text(p)})
      %Equal.sym(Bool, Ac.stops(SCon{'[', r}), False{}, hs) : {Ac.split.ok(_, '[', r) == Ac.HostPort{SCon{'[', String.append(i, "]")}, DashAccess.sp_port_of(p)} : Ac.Authority}
      %Equal.sym(Maybe<&2, Ac.Cut>, Ac.close(r), Some{Ac.Cut{String.append(i, "]"), DashAccess.sp_port_text(p)}}, dab.close_app(i, DashAccess.sp_port_text(p), hi)) : {Ac.bracket(Ac.cons('[', _)) == Ac.HostPort{SCon{'[', String.append(i, "]")}, DashAccess.sp_port_of(p)} : Ac.Authority}
      dab.after_port(SCon{'[', String.append(i, "]")}, p, hq)

# a well-formed authority reads as its host and port
def dab.split_spell(+a: DashAccess.SpAuth, +ok: {DashAccess.sp_well(a) == True{} : Bool}) -> {Ac.split(DashAccess.sp_spell(a)) == Ac.HostPort{DashAccess.sp_name(a), DashAccess.sp_port(a)} : Ac.Authority}:
  +ok2 = ok
  +hn = dab.not_t(DashAccess.sp_holds(DashAccess.sp_spell(a)), dab.and_l(Bool.not(DashAccess.sp_holds(DashAccess.sp_spell(a))), DashAccess.sp_well.parts(a), ok2))
  +hp = dab.and_r(Bool.not(DashAccess.sp_holds(DashAccess.sp_spell(a))), DashAccess.sp_well.parts(a), ok2)
  +hs = Equal.trans(Bool, Ac.stops(DashAccess.sp_spell(a)), DashAccess.sp_holds(DashAccess.sp_spell(a)), False{}, dab.stops(DashAccess.sp_spell(a)), hn)
  dab.split_parts(a, hs, hp)


# Ports, read back
# ----------------

# what the digits read from s after acc are: all digits, and below 65536
# only their value; never below acc (acc at most 65536)
def dab.DgP(s: String, +acc: Nat, m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{+w}:
      {DashAccess.sp_all_digits(s) == True{} : Bool} & {Bool.or(Nat.is_lt(65535n, w), Nat.is_eq(DashAccess.sp_value(acc, s), w)) == True{} : Bool} & {Nat.is_le(acc, w) == True{} : Bool}

def dab.dg.cap(kx: Bool, +x: Nat, -t: String, +w: Nat, +ex: {Nat.is_le(x, 65535n) == kx : Bool}, +ok: {Bool.or(Nat.is_lt(65535n, w), Nat.is_eq(DashAccess.sp_value(Ac.cap.at(kx, x), t), w)) == True{} : Bool}, +lw: {Nat.is_le(Ac.cap.at(kx, x), w) == True{} : Bool}) -> {Bool.or(Nat.is_lt(65535n, w), Nat.is_eq(DashAccess.sp_value(x, t), w)) == True{} : Bool}:
  match kx:
    case True{}:
      ok
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(65535n, w), True{}, dab.lt_of_le(65535n, w, lw)) : {Bool.or(_, Nat.is_eq(DashAccess.sp_value(x, t), w)) == True{} : Bool}
      {==}

def dab.dg.some3(+c: Char, -t: String, +acc: Nat, +hacc: {Nat.is_le(acc, 65536n) == True{} : Bool}, +hc: {Char.is_digit(c) == True{} : Bool}, +w: Nat, ht: {DashAccess.sp_all_digits(t) == True{} : Bool}, ok: {Bool.or(Nat.is_lt(65535n, w), Nat.is_eq(DashAccess.sp_value(Ac.cap(Nat.add(Nat.mul(10n, acc), Ac.digit(c))), t), w)) == True{} : Bool}, +lw: {Nat.is_le(Ac.cap(Nat.add(Nat.mul(10n, acc), Ac.digit(c))), w) == True{} : Bool}) -> dab.DgP(SCon{c, t}, acc, Some{w}):
  +x = Nat.add(Nat.mul(10n, acc), Ac.digit(c))
  +a1 = Equal.trans(Bool, Bool.and(Char.is_digit(c), DashAccess.sp_all_digits(t)), Bool.and(True{}, DashAccess.sp_all_digits(t)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, DashAccess.sp_all_digits(t)), Char.is_digit(c), True{}, hc), ht)
  +le = LNat.pu.le_trans(acc, Ac.cap(x), w, dab.cap_ge(acc, x, dab.le10(acc, Ac.digit(c)), hacc), lw)
  (a1, (dab.dg.cap(Nat.is_le(x, 65535n), x, t, w, {==}, ok, lw), le))

def dab.dg.some(+c: Char, -t: String, +acc: Nat, +hacc: {Nat.is_le(acc, 65536n) == True{} : Bool}, +hc: {Char.is_digit(c) == True{} : Bool}, m: Maybe<&2, Nat>, ih: dab.DgP(t, Ac.cap(Nat.add(Nat.mul(10n, acc), Ac.digit(c))), m)) -> dab.DgP(SCon{c, t}, acc, m):
  match m:
    case None{}:
      Unit{}
    case Some{+w}:
      (ht, (ok, lw)) = ih
      dab.dg.some3(c, t, acc, hacc, hc, w, ht, ok, lw)

def dab.dg.step(+c: Char, -t: String, +acc: Nat, +hacc: {Nat.is_le(acc, 65536n) == True{} : Bool}, kd: Bool, +ekd: {Char.is_digit(c) == kd : Bool}, m: Maybe<&2, Nat>, ih: dab.DgP(t, Ac.cap(Nat.add(Nat.mul(10n, acc), Ac.digit(c))), m)) -> dab.DgP(SCon{c, t}, acc, Ac.digits.keep(kd, m)):
  match kd:
    case True{}:
      dab.dg.some(c, t, acc, hacc, ekd, m, ih)
    case False{}:
      Unit{}

def dab.dig_inv(s: String, +acc: Nat, +hacc: {Nat.is_le(acc, 65536n) == True{} : Bool}) -> dab.DgP(s, acc, Ac.digits(s, acc)):
  match s:
    case SNil{}:
      ({==}, (dab.or_true_r_eq(Nat.is_lt(65535n, acc), Nat.is_eq(acc, acc), dab.eq_refl(acc)), LNat.pu.le_refl(acc)))
    case SCon{+c, +t}:
      +x = Nat.add(Nat.mul(10n, acc), Ac.digit(c))
      dab.dg.step(c, t, acc, hacc, Char.is_digit(c), {==}, Ac.digits(t, Ac.cap(x)), dab.dig_inv(t, Ac.cap(x), dab.cap_le(x)))

# what num reads from s: one or more digits worth at most 65535
def dab.NP(s: String, m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{+v}:
      {DashAccess.sp_port_ok(Some{DashAccess.SpPort{False{}, s}}) == True{} : Bool}

def dab.np.val(+v: Nat, +w: Nat, kl: Bool, +ekl: {Nat.is_lt(65535n, w) == kl : Bool}, +lw: {Nat.is_le(w, 65535n) == True{} : Bool}, +ok: {Bool.or(kl, Nat.is_eq(v, w)) == True{} : Bool}) -> {Nat.is_le(v, 65535n) == True{} : Bool}:
  match kl:
    case True{}:
      dab.absurdF({Nat.is_le(v, 65535n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_le(w, 65535n), True{}, Equal.sym(Bool, Nat.is_le(w, 65535n), False{}, LNat.pc.lt_not_le(65535n, w, ekl)), lw))
    case False{}:
      %Equal.sym(Nat, v, w, dab.eq_sound(v, w, ok)) : {Nat.is_le(_, 65535n) == True{} : Bool}
      lw

def dab.np.fit(+s: String, kw: Bool, +w: Nat, +ekw: {Nat.is_le(w, 65535n) == kw : Bool}, +hs: {String.is_empty(s) == False{} : Bool}, dp: dab.DgP(s, 0n, Some{w})) -> dab.NP(s, Ac.num.fit.at(kw, w)):
  match kw:
    case False{}:
      Unit{}
    case True{}:
      (ha, (ok, lw)) = dp
      +hv = dab.np.val(DashAccess.sp_value(0n, s), w, Nat.is_lt(65535n, w), {==}, ekw, ok)
      %Equal.sym(Bool, String.is_empty(s), False{}, hs) : {Bool.and(Bool.not(_), Bool.and(DashAccess.sp_all_digits(s), Nat.is_le(DashAccess.sp_value(0n, s), 65535n))) == True{} : Bool}
      dab.and_tt(DashAccess.sp_all_digits(s), Nat.is_le(DashAccess.sp_value(0n, s), 65535n), ha, hv)

def dab.np.digits(+s: String, +hs: {String.is_empty(s) == False{} : Bool}, m: Maybe<&2, Nat>, dp: dab.DgP(s, 0n, m)) -> dab.NP(s, Ac.num.fit(m)):
  match m:
    case None{}:
      Unit{}
    case Some{+w}:
      dab.np.fit(s, Nat.is_le(w, 65535n), w, {==}, hs, dp)

def dab.num_inv(+s: String) -> dab.NP(s, Ac.num(s)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+c, +t}:
      dab.np.digits(SCon{c, t}, {==}, Ac.digits(SCon{c, t}, 0n), dab.dig_inv(SCon{c, t}, 0n, {==}))

# what port reads from q: an optional '+', then a well-formed port
def dab.PP(q: String, m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{+v}:
      Sigma<&1, &1, Bool, plus => Sigma<&1, &1, String, ds => {q == DashAccess.sp_sign(plus, ds) : String} & {DashAccess.sp_port_ok(Some{DashAccess.SpPort{plus, ds}}) == True{} : Bool}>>

def dab.pp.plus(-c: Char, +t: String, +ec: {c == '+' : Char}, m: Maybe<&2, Nat>, np: dab.NP(t, m)) -> dab.PP(SCon{c, t}, m):
  match m:
    case None{}:
      Unit{}
    case Some{+v}:
      (True{}, (t, (Equal.cong(Char, String, z => SCon{z, t}, c, '+', ec), np)))

def dab.pp.bare(+s: String, m: Maybe<&2, Nat>, np: dab.NP(s, m)) -> dab.PP(s, m):
  match m:
    case None{}:
      Unit{}
    case Some{+v}:
      (False{}, (s, ({==}, np)))

def dab.pp.sign(kp: Bool, +c: Char, +t: String, +ekp: {Char.is_eq(c, '+') == kp : Bool}) -> dab.PP(SCon{c, t}, Ac.port.sign(kp, c, t)):
  match kp:
    case True{}:
      dab.pp.plus(c, t, LStg.stg.char_sound(c, '+', ekp), Ac.num(t), dab.num_inv(t))
    case False{}:
      dab.pp.bare(SCon{c, t}, Ac.num(SCon{c, t}), dab.num_inv(SCon{c, t}))

def dab.port_inv(+q: String) -> dab.PP(q, Ac.port(q)):
  match q:
    case SNil{}:
      Unit{}
    case SCon{+c, +t}:
      dab.pp.sign(Char.is_eq(c, '+'), c, t, {==})

# Cuts, read back
# ---------------

# what close cut: the inside, ']' and the rest
def dab.CP(t: String, m: Maybe<&2, Ac.Cut>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{+p}:
      match p:
        case Ac.Cut{+x, +r}:
          Sigma<&1, &1, String, i => {x == String.append(i, "]") : String} & {t == String.append(i, SCon{']', r}) : String} & {DashAccess.sp_has(i, ']') == False{} : Bool}>

def dab.cp.cons(+c: Char, -t: String, kc: Bool, +ekc: {Char.is_eq(c, ']') == kc : Bool}, m: Maybe<&2, Ac.Cut>, ih: dab.CP(t, m)) -> dab.CP(SCon{c, t}, Ac.close.at(kc, c, t, m)):
  match kc:
    case True{}:
      +ec = LStg.stg.char_sound(c, ']', ekc)
      (SNil{}, (Equal.cong(Char, String, z => SCon{z, SNil{}}, c, ']', ec), (Equal.cong(Char, String, z => SCon{z, t}, c, ']', ec), {==})))
    case False{}:
      match m:
        case None{}:
          Unit{}
        case Some{+p}:
          match p:
            case Ac.Cut{+x, +r}:
              (i, (ex, (et, hi))) = ih
              (SCon{c, i}, (Equal.cong(String, String, z => SCon{c, z}, x, String.append(i, "]"), ex), (Equal.cong(String, String, z => SCon{c, z}, t, String.append(i, SCon{']', r}), et), dab.or_ff(Char.is_eq(c, ']'), DashAccess.sp_has(i, ']'), ekc, hi))))

def dab.close_inv(t: String) -> dab.CP(t, Ac.close(t)):
  match t:
    case SNil{}:
      Unit{}
    case SCon{+c, +u}:
      dab.cp.cons(c, u, Char.is_eq(c, ']'), {==}, Ac.close(u), dab.close_inv(u))

# what last cut: the text before the last ':', and after it
def dab.LP(s: String, m: Maybe<&2, Ac.Cut>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{+p}:
      match p:
        case Ac.Cut{+h, +q}:
          {s == String.append(h, SCon{':', q}) : String}

def dab.lp.here(+c: Char, +t: String, kc: Bool, +ekc: {Char.is_eq(c, ':') == kc : Bool}) -> dab.LP(SCon{c, t}, Ac.last.here(kc, t)):
  match kc:
    case True{}:
      Equal.cong(Char, String, z => SCon{z, t}, c, ':', LStg.stg.char_sound(c, ':', ekc))
    case False{}:
      Unit{}

def dab.lp.at(+c: Char, +t: String, m: Maybe<&2, Ac.Cut>, ih: dab.LP(t, m)) -> dab.LP(SCon{c, t}, Ac.last.at(c, t, m)):
  match m:
    case Some{+p}:
      match p:
        case Ac.Cut{+h, +q}:
          Equal.cong(String, String, z => SCon{c, z}, t, String.append(h, SCon{':', q}), ih)
    case None{}:
      dab.lp.here(c, t, Char.is_eq(c, ':'), {==})

def dab.last_inv(s: String) -> dab.LP(s, Ac.last(s)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+c, +t}:
      dab.lp.at(c, t, Ac.last(t), dab.last_inv(t))

# Authorities, read back
# ----------------------

# what split read: the writing of a well-formed authority
def dab.SP(s: String, a: Ac.Authority) -> Type:
  match a:
    case Ac.HostPort{+n, +p}:
      Sigma<&1, &1, DashAccess.SpAuth, w => {s == DashAccess.sp_spell(w) : String} & {DashAccess.sp_well(w) == True{} : Bool}>
    case Ac.NoAuthority{}:
      Unit

# a witness: s is its writing, s holds no forbidden char, its parts are
# well formed
def dab.sp.mk(-s: String, +w: DashAccess.SpAuth, +es: {s == DashAccess.sp_spell(w) : String}, +hn: {DashAccess.sp_holds(s) == False{} : Bool}, +hp: {DashAccess.sp_well.parts(w) == True{} : Bool}) -> Sigma<&1, &1, DashAccess.SpAuth, w2 => {s == DashAccess.sp_spell(w2) : String} & {DashAccess.sp_well(w2) == True{} : Bool}>:
  +es2 = es
  +hn2 = Equal.trans(Bool, DashAccess.sp_holds(DashAccess.sp_spell(w)), DashAccess.sp_holds(s), False{}, Equal.cong(String, Bool, z => DashAccess.sp_holds(z), DashAccess.sp_spell(w), s, Equal.sym(String, s, DashAccess.sp_spell(w), es2)), hn)
  (w, (es2, dab.and_tt(Bool.not(DashAccess.sp_holds(DashAccess.sp_spell(w))), DashAccess.sp_well.parts(w), dab.not_f(DashAccess.sp_holds(DashAccess.sp_spell(w)), hn2), hp)))

def dab.has_of_colons(+h: String, +e: {Ac.colons(h) == False{} : Bool}) -> {DashAccess.sp_has(h, ':') == False{} : Bool}:
  Equal.trans(Bool, DashAccess.sp_has(h, ':'), Ac.colons(h), False{}, Equal.sym(Bool, Ac.colons(h), DashAccess.sp_has(h, ':'), dab.colons(h)), e)

def dab.holds_of_stops(+s: String, +e: {Ac.stops(s) == False{} : Bool}) -> {DashAccess.sp_holds(s) == False{} : Bool}:
  Equal.trans(Bool, DashAccess.sp_holds(s), Ac.stops(s), False{}, Equal.sym(Bool, Ac.stops(s), DashAccess.sp_holds(s), dab.stops(s)), e)

# a bracketed reading with a port
def dab.si.wp(-t: String, +i: String, -d: Char, -q: String, +et: {t == String.append(i, SCon{']', SCon{d, q}}) : String}, ed: {d == ':' : Char}, hn: {DashAccess.sp_holds(SCon{'[', t}) == False{} : Bool}, +hi: {DashAccess.sp_has(i, ']') == False{} : Bool}, -n: String, m: Maybe<&2, Nat>, pp: dab.PP(q, m)) -> dab.SP(SCon{'[', t}, Ac.with_port(n, m)):
  match m:
    case None{}:
      Unit{}
    case Some{+v}:
      (+plus, (+ds, (eq, okp))) = pp
      +okp2 = okp
      +e1 = Equal.trans(String, t, String.append(i, SCon{']', SCon{d, q}}), String.append(i, SCon{']', SCon{':', q}}), et, Equal.cong(Char, String, z => String.append(i, SCon{']', SCon{z, q}}), d, ':', ed))
      +e2 = Equal.trans(String, t, String.append(i, SCon{']', SCon{':', q}}), String.append(i, SCon{']', SCon{':', DashAccess.sp_sign(plus, ds)}}), e1, Equal.cong(String, String, z => String.append(i, SCon{']', SCon{':', z}}), q, DashAccess.sp_sign(plus, ds), eq))
      dab.sp.mk(SCon{'[', t}, DashAccess.SpBracket{i, Some{DashAccess.SpPort{plus, ds}}}, Equal.cong(String, String, z => SCon{'[', z}, t, String.append(i, SCon{']', SCon{':', DashAccess.sp_sign(plus, ds)}}), e2), hn, dab.and_tt(Bool.not(DashAccess.sp_has(i, ']')), DashAccess.sp_port_ok(Some{DashAccess.SpPort{plus, ds}}), dab.not_f(DashAccess.sp_has(i, ']'), hi), okp2))

def dab.si.colon(kd: Bool, +d: Char, +q: String, +ekd: {Char.is_eq(d, ':') == kd : Bool}, -t: String, +i: String, +et: {t == String.append(i, SCon{']', SCon{d, q}}) : String}, hn: {DashAccess.sp_holds(SCon{'[', t}) == False{} : Bool}, +hi: {DashAccess.sp_has(i, ']') == False{} : Bool}, +n: String) -> dab.SP(SCon{'[', t}, Ac.after.colon(kd, n, q)):
  match kd:
    case True{}:
      dab.si.wp(t, i, d, q, et, LStg.stg.char_sound(d, ':', ekd), hn, hi, n, Ac.port(q), dab.port_inv(q))
    case False{}:
      Unit{}

# a bracketed reading: nothing, or ':' and a port, after the ']'
def dab.si.after(-t: String, +i: String, r: String, +n: String, +et: {t == String.append(i, SCon{']', r}) : String}, hn: {DashAccess.sp_holds(SCon{'[', t}) == False{} : Bool}, +hi: {DashAccess.sp_has(i, ']') == False{} : Bool}) -> dab.SP(SCon{'[', t}, Ac.after(n, r)):
  match r:
    case SNil{}:
      dab.sp.mk(SCon{'[', t}, DashAccess.SpBracket{i, None{}}, Equal.cong(String, String, z => SCon{'[', z}, t, String.append(i, SCon{']', SNil{}}), et), hn, dab.and_tt(Bool.not(DashAccess.sp_has(i, ']')), True{}, dab.not_f(DashAccess.sp_has(i, ']'), hi), {==}))
    case SCon{+d, +q}:
      dab.si.colon(Char.is_eq(d, ':'), d, q, {==}, t, i, et, hn, hi, n)

def dab.si.br(-t: String, m: Maybe<&2, Ac.Cut>, cp: dab.CP(t, m), +hn: {DashAccess.sp_holds(SCon{'[', t}) == False{} : Bool}) -> dab.SP(SCon{'[', t}, Ac.bracket(Ac.cons('[', m))):
  match m:
    case None{}:
      Unit{}
    case Some{+p}:
      match p:
        case Ac.Cut{+x, +r}:
          (+i, (ex, (et, hi))) = cp
          dab.si.after(t, i, r, SCon{'[', x}, et, hn, hi)

# a host that is not bracketed, starting where the text starts
def dab.si.hostok(+h: String, -c: Char, -t: String, -y: String, +ek: {Char.is_eq(c, '[') == False{} : Bool}, eh: {SCon{c, t} == String.append(h, y) : String}, he: {String.is_empty(h) == False{} : Bool}, hc: {Ac.colons(h) == False{} : Bool}) -> {DashAccess.sp_plain_ok(h) == True{} : Bool}:
  match h:
    case SNil{}:
      dab.absurdT({DashAccess.sp_plain_ok(SNil{}) == True{} : Bool}, he)
    case SCon{+c2, +t2}:
      +ecc = Equal.cong(String, Char, z => dab.head(z, c), SCon{c, t}, SCon{c2, String.append(t2, y)}, eh)
      +ek2 = Equal.trans(Bool, Char.is_eq(c2, '['), Char.is_eq(c, '['), False{}, Equal.cong(Char, Bool, z => Char.is_eq(z, '['), c2, c, Equal.sym(Char, c, c2, ecc)), ek)
      dab.and_tt(Bool.not(Char.is_eq(c2, '[')), Bool.not(DashAccess.sp_has(SCon{c2, t2}, ':')), dab.not_f(Char.is_eq(c2, '['), ek2), dab.not_f(DashAccess.sp_has(SCon{c2, t2}, ':'), dab.has_of_colons(SCon{c2, t2}, hc)))

def dab.si.pwp(-c: Char, -t: String, +h: String, -q: String, +es: {SCon{c, t} == String.append(h, SCon{':', q}) : String}, +ek: {Char.is_eq(c, '[') == False{} : Bool}, he: {String.is_empty(h) == False{} : Bool}, hc: {Ac.colons(h) == False{} : Bool}, hn: {DashAccess.sp_holds(SCon{c, t}) == False{} : Bool}, m: Maybe<&2, Nat>, pp: dab.PP(q, m)) -> dab.SP(SCon{c, t}, Ac.with_port(h, m)):
  match m:
    case None{}:
      Unit{}
    case Some{+v}:
      (+plus, (+ds, (eq, okp))) = pp
      +okp2 = okp
      +es2 = es
      +e2 = Equal.trans(String, SCon{c, t}, String.append(h, SCon{':', q}), String.append(h, SCon{':', DashAccess.sp_sign(plus, ds)}), es2, Equal.cong(String, String, z => String.append(h, SCon{':', z}), q, DashAccess.sp_sign(plus, ds), eq))
      dab.sp.mk(SCon{c, t}, DashAccess.SpPlain{h, Some{DashAccess.SpPort{plus, ds}}}, e2, hn, dab.and_tt(DashAccess.sp_plain_ok(h), DashAccess.sp_port_ok(Some{DashAccess.SpPort{plus, ds}}), dab.si.hostok(h, c, t, SCon{':', q}, ek, es2, he, hc), okp2))

def dab.si.pguard(kg: Bool, +h: String, +q: String, +eg: {Bool.or(String.is_empty(h), Ac.colons(h)) == kg : Bool}, -c: Char, -t: String, +es: {SCon{c, t} == String.append(h, SCon{':', q}) : String}, +ek: {Char.is_eq(c, '[') == False{} : Bool}, hn: {DashAccess.sp_holds(SCon{c, t}) == False{} : Bool}) -> dab.SP(SCon{c, t}, Ac.plain.host(kg, h, Some{q})):
  match kg:
    case True{}:
      Unit{}
    case False{}:
      +eg2 = eg
      dab.si.pwp(c, t, h, q, es, ek, dab.or_l(String.is_empty(h), Ac.colons(h), eg2), dab.or_r(String.is_empty(h), Ac.colons(h), eg2), hn, Ac.port(q), dab.port_inv(q))

def dab.si.bare(kc: Bool, +c: Char, +t: String, +ekc: {Ac.colons(SCon{c, t}) == kc : Bool}, +ek: {Char.is_eq(c, '[') == False{} : Bool}, hn: {DashAccess.sp_holds(SCon{c, t}) == False{} : Bool}) -> dab.SP(SCon{c, t}, Ac.plain.host(kc, SCon{c, t}, None{})):
  match kc:
    case True{}:
      Unit{}
    case False{}:
      +hc = dab.has_of_colons(SCon{c, t}, ekc)
      dab.sp.mk(SCon{c, t}, DashAccess.SpPlain{SCon{c, t}, None{}}, Equal.sym(String, String.append(SCon{c, t}, SNil{}), SCon{c, t}, dab.append_nil(SCon{c, t})), hn, dab.and_tt(DashAccess.sp_plain_ok(SCon{c, t}), True{}, dab.and_tt(Bool.not(Char.is_eq(c, '[')), Bool.not(DashAccess.sp_has(SCon{c, t}, ':')), dab.not_f(Char.is_eq(c, '['), ek), dab.not_f(DashAccess.sp_has(SCon{c, t}, ':'), hc)), {==}))

def dab.si.plain(+c: Char, +t: String, m: Maybe<&2, Ac.Cut>, lp: dab.LP(SCon{c, t}, m), +ek: {Char.is_eq(c, '[') == False{} : Bool}, hn: {DashAccess.sp_holds(SCon{c, t}) == False{} : Bool}) -> dab.SP(SCon{c, t}, Ac.plain(SCon{c, t}, m)):
  match m:
    case None{}:
      dab.si.bare(Ac.colons(SCon{c, t}), c, t, {==}, ek, hn)
    case Some{+p}:
      match p:
        case Ac.Cut{+h, +q}:
          dab.si.pguard(Bool.or(String.is_empty(h), Ac.colons(h)), h, q, {==}, c, t, lp, ek, hn)

def dab.si.form(kk: Bool, +c: Char, +t: String, +ekk: {Char.is_eq(c, '[') == kk : Bool}, +hn: {DashAccess.sp_holds(SCon{c, t}) == False{} : Bool}) -> dab.SP(SCon{c, t}, Ac.split.form(kk, SCon{c, t})):
  match kk:
    case True{}:
      +ec = LStg.stg.char_sound(c, '[', ekk)
      +hn2 = Equal.trans(Bool, DashAccess.sp_holds(SCon{'[', t}), DashAccess.sp_holds(SCon{c, t}), False{}, Equal.cong(Char, Bool, z => DashAccess.sp_holds(SCon{z, t}), '[', c, Equal.sym(Char, c, '[', ec)), hn)
      %Equal.sym(Char, c, '[', ec) : dab.SP(SCon{_, t}, Ac.bracket(Ac.close(SCon{_, t})))
      dab.si.br(t, Ac.close(t), dab.close_inv(t), hn2)
    case False{}:
      dab.si.plain(c, t, Ac.last(SCon{c, t}), dab.last_inv(SCon{c, t}), ekk, hn)

def dab.si.ok(kb: Bool, +c: Char, +t: String, +ekb: {Ac.stops(SCon{c, t}) == kb : Bool}) -> dab.SP(SCon{c, t}, Ac.split.ok(kb, c, t)):
  match kb:
    case True{}:
      Unit{}
    case False{}:
      dab.si.form(Char.is_eq(c, '['), c, t, {==}, dab.holds_of_stops(SCon{c, t}, ekb))

# every text the code reads as an authority is a well-formed writing
def dab.split_inv(s: String) -> dab.SP(s, Ac.split(s)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+c, +t}:
      dab.si.ok(Ac.stops(SCon{c, t}), c, t, {==})

# Origins
# -------

def dab.scheme.of(x: Bool, y: Bool) -> {Ac.scheme.of(x, y) == DashAccess.sp_scheme.at(x, 80n, DashAccess.sp_scheme.at(y, 443n, None{})) : Maybe<&2, Nat>}:
  match x:
    case True{}:
      {==}
    case False{}:
      match y:
        case True{}:
          {==}
        case False{}:
          {==}

# the code's default port is the spec's
def dab.scheme(+sc: String) -> {Ac.scheme(sc) == DashAccess.sp_scheme(sc) : Maybe<&2, Nat>}:
  %dab.same(sc, "http") : {Ac.scheme.of(Ac.same(sc, "http"), Ac.same(sc, "https")) == DashAccess.sp_scheme.at(_, 80n, DashAccess.sp_scheme.at(DashAccess.sp_ci(sc, "https"), 443n, None{})) : Maybe<&2, Nat>}
  %dab.same(sc, "https") : {Ac.scheme.of(Ac.same(sc, "http"), Ac.same(sc, "https")) == DashAccess.sp_scheme.at(Ac.same(sc, "http"), 80n, DashAccess.sp_scheme.at(_, 443n, None{})) : Maybe<&2, Nat>}
  dab.scheme.of(Ac.same(sc, "http"), Ac.same(sc, "https"))

def dab.MN.If(m: Maybe<&2, Nat>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{+x}:
      G

def dab.none_some(-G: Type, -d: Nat, +e: {None{} == Some{d} : Maybe<&2, Nat>}) -> G:
  %e : dab.MN.If(_, G)
  Unit{}

# a char that lowers to k is no ':' when k is none
def dab.cn.c(+c: Char, +k: Char, kc: Bool, +ekc: {Char.is_eq(c, ':') == kc : Bool}, +el: {Char.is_eq(Char.to_lower(c), k) == True{} : Bool}, +nk: {Char.is_eq(k, ':') == False{} : Bool}) -> {Char.is_eq(c, ':') == False{} : Bool}:
  match kc:
    case False{}:
      ekc
    case True{}:
      +ec = LStg.stg.char_sound(c, ':', ekc)
      +e1 = Equal.trans(Bool, Char.is_eq(Char.to_lower(':'), k), Char.is_eq(Char.to_lower(c), k), True{}, Equal.cong(Char, Bool, z => Char.is_eq(Char.to_lower(z), k), ':', c, Equal.sym(Char, c, ':', ec)), el)
      +ek = LStg.stg.char_sound(':', k, e1)
      +e2 = Equal.trans(Bool, Char.is_eq(':', ':'), Char.is_eq(k, ':'), False{}, Equal.cong(Char, Bool, z => Char.is_eq(z, ':'), ':', k, ek), nk)
      dab.absurdT({Char.is_eq(c, ':') == False{} : Bool}, e2)

# a text equal, but for case, to one without ':' holds none
def dab.cn(sc: String, lw: String, +e: {LawsBase.text_same(DashAccess.sp_lower(sc), lw) == True{} : Bool}, +nw: {DashAccess.sp_has(lw, ':') == False{} : Bool}) -> {DashAccess.sp_has(sc, ':') == False{} : Bool}:
  match sc lw:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{k, u}:
      dab.absurdF({DashAccess.sp_has(SNil{}, ':') == False{} : Bool}, e)
    case SCon{+c, +t} SNil{}:
      dab.absurdF({DashAccess.sp_has(SCon{c, t}, ':') == False{} : Bool}, e)
    case SCon{+c, +t} SCon{+k, +u}:
      +e2 = e
      +nw2 = nw
      +hc = dab.cn.c(c, k, Char.is_eq(c, ':'), {==}, dab.and_l(Char.is_eq(Char.to_lower(c), k), LawsBase.text_same(DashAccess.sp_lower(t), u), e2), dab.or_l(Char.is_eq(k, ':'), DashAccess.sp_has(u, ':'), nw2))
      dab.or_ff(Char.is_eq(c, ':'), DashAccess.sp_has(t, ':'), hc, dab.cn(t, u, dab.and_r(Char.is_eq(Char.to_lower(c), k), LawsBase.text_same(DashAccess.sp_lower(t), u), e2), dab.or_r(Char.is_eq(k, ':'), DashAccess.sp_has(u, ':'), nw2)))

def dab.sn(+sc: String, -d: Nat, k1: Bool, +e1: {DashAccess.sp_ci(sc, "http") == k1 : Bool}, k2: Bool, +e2: {DashAccess.sp_ci(sc, "https") == k2 : Bool}, +e: {DashAccess.sp_scheme.at(k1, 80n, DashAccess.sp_scheme.at(k2, 443n, None{})) == Some{d} : Maybe<&2, Nat>}) -> {DashAccess.sp_has(sc, ':') == False{} : Bool}:
  match k1:
    case True{}:
      dab.cn(sc, "http", e1, {==})
    case False{}:
      match k2:
        case True{}:
          dab.cn(sc, "https", e2, {==})
        case False{}:
          dab.none_some({DashAccess.sp_has(sc, ':') == False{} : Bool}, d, e)

# a scheme with a default port holds no ':'
def dab.scheme_nocolon(+sc: String, -d: Nat, +e: {DashAccess.sp_scheme(sc) == Some{d} : Maybe<&2, Nat>}) -> {DashAccess.sp_has(sc, ':') == False{} : Bool}:
  dab.sn(sc, d, DashAccess.sp_ci(sc, "http"), {==}, DashAccess.sp_ci(sc, "https"), {==}, e)

# an origin as written cuts at the "://" after its scheme
def dab.sep_text(sc: String, +x: String, +h: {DashAccess.sp_has(sc, ':') == False{} : Bool}) -> {Ac.sep(String.append(sc, SCon{':', SCon{'/', SCon{'/', x}}})) == Some{Ac.Cut{sc, x}} : Maybe<&2, Ac.Cut>}:
  match sc:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h2 = h
      +r = String.append(t, SCon{':', SCon{'/', SCon{'/', x}}})
      %Equal.sym(Maybe<&2, Ac.Cut>, Ac.sep(r), Some{Ac.Cut{t, x}}, dab.sep_text(t, x, dab.or_r(Char.is_eq(c, ':'), DashAccess.sp_has(t, ':'), h2))) : {Ac.sep.at(Char.is_eq(c, ':'), c, r, _) == Some{Ac.Cut{SCon{c, t}, x}} : Maybe<&2, Ac.Cut>}
      %Equal.sym(Bool, Char.is_eq(c, ':'), False{}, dab.or_l(Char.is_eq(c, ':'), DashAccess.sp_has(t, ':'), h2)) : {Ac.sep.at(_, c, r, Some{Ac.Cut{t, x}}) == Some{Ac.Cut{SCon{c, t}, x}} : Maybe<&2, Ac.Cut>}
      {==}

# what the "://" cut read: scheme, "://", the rest
def dab.SepP(o: String, m: Maybe<&2, Ac.Cut>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{+p}:
      match p:
        case Ac.Cut{+sc, +au}:
          {o == String.append(sc, SCon{':', SCon{'/', SCon{'/', au}}}) : String}

def dab.RP(t: String, m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{+x}:
      {t == SCon{'/', SCon{'/', x}} : String}

def dab.rs(k: Bool, +a: Char, +b2: Char, +r: String, +ek: {Bool.and(Char.is_eq(a, '/'), Char.is_eq(b2, '/')) == k : Bool}) -> dab.RP(SCon{a, SCon{b2, r}}, Ac.sep.slashes(k, r)):
  match k:
    case True{}:
      +ek2 = ek
      +ea = LStg.stg.char_sound(a, '/', dab.and_l(Char.is_eq(a, '/'), Char.is_eq(b2, '/'), ek2))
      +eb = LStg.stg.char_sound(b2, '/', dab.and_r(Char.is_eq(a, '/'), Char.is_eq(b2, '/'), ek2))
      Equal.trans(String, SCon{a, SCon{b2, r}}, SCon{'/', SCon{b2, r}}, SCon{'/', SCon{'/', r}}, Equal.cong(Char, String, z => SCon{z, SCon{b2, r}}, a, '/', ea), Equal.cong(Char, String, z => SCon{'/', SCon{z, r}}, b2, '/', eb))
    case False{}:
      Unit{}

def dab.rest_inv(t: String) -> dab.RP(t, Ac.sep.rest(t)):
  match t:
    case SNil{}:
      Unit{}
    case SCon{+a, +u}:
      match u:
        case SNil{}:
          Unit{}
        case SCon{+b2, +r}:
          dab.rs(Bool.and(Char.is_eq(a, '/'), Char.is_eq(b2, '/')), a, b2, r, {==})

def dab.se.cons(+c: Char, -t: String, m: Maybe<&2, Ac.Cut>, ih: dab.SepP(t, m)) -> dab.SepP(SCon{c, t}, Ac.cons(c, m)):
  match m:
    case None{}:
      Unit{}
    case Some{+p}:
      match p:
        case Ac.Cut{+sc, +au}:
          Equal.cong(String, String, z => SCon{c, z}, t, String.append(sc, SCon{':', SCon{'/', SCon{'/', au}}}), ih)

def dab.se.found(+c: Char, -t: String, +ec: {c == ':' : Char}, mr: Maybe<&2, String>, rp: dab.RP(t, mr), m: Maybe<&2, Ac.Cut>, ih: dab.SepP(t, m)) -> dab.SepP(SCon{c, t}, Ac.sep.found(mr, c, m)):
  match mr:
    case Some{+x}:
      Equal.trans(String, SCon{c, t}, SCon{':', t}, SCon{':', SCon{'/', SCon{'/', x}}}, Equal.cong(Char, String, z => SCon{z, t}, c, ':', ec), Equal.cong(String, String, z => SCon{':', z}, t, SCon{'/', SCon{'/', x}}, rp))
    case None{}:
      dab.se.cons(c, t, m, ih)

def dab.se.at(kc: Bool, +c: Char, +t: String, +ekc: {Char.is_eq(c, ':') == kc : Bool}, m: Maybe<&2, Ac.Cut>, ih: dab.SepP(t, m)) -> dab.SepP(SCon{c, t}, Ac.sep.at(kc, c, t, m)):
  match kc:
    case True{}:
      dab.se.found(c, t, LStg.stg.char_sound(c, ':', ekc), Ac.sep.rest(t), dab.rest_inv(t), m, ih)
    case False{}:
      dab.se.cons(c, t, m, ih)

# every cut origin is scheme "://" rest
def dab.sep_inv(o: String) -> dab.SepP(o, Ac.sep(o)):
  match o:
    case SNil{}:
      Unit{}
    case SCon{+c, +t}:
      dab.se.at(Char.is_eq(c, ':'), c, t, {==}, Ac.sep(t), dab.sep_inv(t))
