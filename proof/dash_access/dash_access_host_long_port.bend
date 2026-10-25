# eukhe: the proof of LAW dash_access_host_long_port
#
# PROOF: the digit run has no ':' or ']', so the text splits at the ':'
# before the run (dlp.last_any) and a bracketed host ends before it
# (dlp.bracket_any); either way the authority needs the run, or text
# with a ':' in it, as a port. A port with a ':' is none (dlp.num_colon).
# The run's value, capped at 65536, is at least 1, 10, 100, 1000, 10000
# after its first five digits (dlp.grow, by monotony of 10 * v + d and of
# the cap), so the sixth digit makes it 65536, and 65536 stays 65536 for
# every further digit (dlp.big_run, by induction over the run): no port.

import Base
import ../../bend/dash_access.bend as Ac
import ../../laws/dash_access.bend as DashAccess
import ../base/nat.bend as LNat

# Absurd cases
# ------------

def dlp.Au.If(a: Ac.Authority, G: Type) -> Type:
  match a:
    case Ac.HostPort{n, p}:
      Unit
    case Ac.NoAuthority{}:
      G

def dlp.au_absurd(-G: Type, -n: String, -p: Maybe<&2, Nat>, +e: {Ac.HostPort{n, p} == Ac.NoAuthority{} : Ac.Authority}) -> G:
  %e : dlp.Au.If(_, G)
  Unit{}

def dlp.B.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def dlp.b_absurd(-G: Type, +e: {False{} == True{} : Bool}) -> G:
  %e : dlp.B.If(_, G)
  Unit{}

# Digits, one by one
# ------------------

# the value of a digit
def dlp.val(+d: DashAccess.PortDigit) -> Nat:
  match d:
    case DashAccess.P0{}:
      0n
    case DashAccess.P1{}:
      1n
    case DashAccess.P2{}:
      2n
    case DashAccess.P3{}:
      3n
    case DashAccess.P4{}:
      4n
    case DashAccess.P5{}:
      5n
    case DashAccess.P6{}:
      6n
    case DashAccess.P7{}:
      7n
    case DashAccess.P8{}:
      8n
    case DashAccess.P9{}:
      9n

# the capped value after one more digit
def dlp.nx(+v: Nat, +d: DashAccess.PortDigit) -> Nat:
  Ac.cap(Nat.add(Nat.mul(10n, v), dlp.val(d)))

def dlp.step(+d: DashAccess.PortDigit, +t: String, +v: Nat) -> {Ac.digits(t, dlp.nx(v, d)) == Ac.digits(SCon{DashAccess.sp_digit(d), t}, v) : Maybe<&2, Nat>}:
  match d:
    case DashAccess.P0{}:
      {==}
    case DashAccess.P1{}:
      {==}
    case DashAccess.P2{}:
      {==}
    case DashAccess.P3{}:
      {==}
    case DashAccess.P4{}:
      {==}
    case DashAccess.P5{}:
      {==}
    case DashAccess.P6{}:
      {==}
    case DashAccess.P7{}:
      {==}
    case DashAccess.P8{}:
      {==}
    case DashAccess.P9{}:
      {==}

def dlp.no_close(+d: DashAccess.PortDigit) -> {Char.is_eq(DashAccess.sp_digit(d), ']') == False{} : Bool}:
  match d:
    case DashAccess.P0{}:
      {==}
    case DashAccess.P1{}:
      {==}
    case DashAccess.P2{}:
      {==}
    case DashAccess.P3{}:
      {==}
    case DashAccess.P4{}:
      {==}
    case DashAccess.P5{}:
      {==}
    case DashAccess.P6{}:
      {==}
    case DashAccess.P7{}:
      {==}
    case DashAccess.P8{}:
      {==}
    case DashAccess.P9{}:
      {==}

def dlp.no_colon(+d: DashAccess.PortDigit) -> {Char.is_eq(DashAccess.sp_digit(d), ':') == False{} : Bool}:
  match d:
    case DashAccess.P0{}:
      {==}
    case DashAccess.P1{}:
      {==}
    case DashAccess.P2{}:
      {==}
    case DashAccess.P3{}:
      {==}
    case DashAccess.P4{}:
      {==}
    case DashAccess.P5{}:
      {==}
    case DashAccess.P6{}:
      {==}
    case DashAccess.P7{}:
      {==}
    case DashAccess.P8{}:
      {==}
    case DashAccess.P9{}:
      {==}

# 65536 stays 65536 for every further digit
def dlp.top(+d: DashAccess.PortDigit) -> {dlp.nx(65536n, d) == 65536n : Nat}:
  match d:
    case DashAccess.P0{}:
      {==}
    case DashAccess.P1{}:
      {==}
    case DashAccess.P2{}:
      {==}
    case DashAccess.P3{}:
      {==}
    case DashAccess.P4{}:
      {==}
    case DashAccess.P5{}:
      {==}
    case DashAccess.P6{}:
      {==}
    case DashAccess.P7{}:
      {==}
    case DashAccess.P8{}:
      {==}
    case DashAccess.P9{}:
      {==}

# The leading digit
# -----------------

def dlp.lval(+a: DashAccess.PortLead) -> Nat:
  match a:
    case DashAccess.L1{}:
      1n
    case DashAccess.L2{}:
      2n
    case DashAccess.L3{}:
      3n
    case DashAccess.L4{}:
      4n
    case DashAccess.L5{}:
      5n
    case DashAccess.L6{}:
      6n
    case DashAccess.L7{}:
      7n
    case DashAccess.L8{}:
      8n
    case DashAccess.L9{}:
      9n

# the lead read alone: a port's text is its digits (no '+'), and the
# value after it is at least 1
def dlp.lead(+a: DashAccess.PortLead, +t: String) -> {Ac.num.fit(Ac.digits(t, dlp.lval(a))) == Ac.port(SCon{DashAccess.sp_lead(a), t}) : Maybe<&2, Nat>}:
  match a:
    case DashAccess.L1{}:
      {==}
    case DashAccess.L2{}:
      {==}
    case DashAccess.L3{}:
      {==}
    case DashAccess.L4{}:
      {==}
    case DashAccess.L5{}:
      {==}
    case DashAccess.L6{}:
      {==}
    case DashAccess.L7{}:
      {==}
    case DashAccess.L8{}:
      {==}
    case DashAccess.L9{}:
      {==}

def dlp.lead_one(+a: DashAccess.PortLead) -> {Nat.is_le(1n, dlp.lval(a)) == True{} : Bool}:
  match a:
    case DashAccess.L1{}:
      {==}
    case DashAccess.L2{}:
      {==}
    case DashAccess.L3{}:
      {==}
    case DashAccess.L4{}:
      {==}
    case DashAccess.L5{}:
      {==}
    case DashAccess.L6{}:
      {==}
    case DashAccess.L7{}:
      {==}
    case DashAccess.L8{}:
      {==}
    case DashAccess.L9{}:
      {==}

def dlp.lead_no_close(+a: DashAccess.PortLead) -> {Char.is_eq(DashAccess.sp_lead(a), ']') == False{} : Bool}:
  match a:
    case DashAccess.L1{}:
      {==}
    case DashAccess.L2{}:
      {==}
    case DashAccess.L3{}:
      {==}
    case DashAccess.L4{}:
      {==}
    case DashAccess.L5{}:
      {==}
    case DashAccess.L6{}:
      {==}
    case DashAccess.L7{}:
      {==}
    case DashAccess.L8{}:
      {==}
    case DashAccess.L9{}:
      {==}

def dlp.lead_no_colon(+a: DashAccess.PortLead) -> {Char.is_eq(DashAccess.sp_lead(a), ':') == False{} : Bool}:
  match a:
    case DashAccess.L1{}:
      {==}
    case DashAccess.L2{}:
      {==}
    case DashAccess.L3{}:
      {==}
    case DashAccess.L4{}:
      {==}
    case DashAccess.L5{}:
      {==}
    case DashAccess.L6{}:
      {==}
    case DashAccess.L7{}:
      {==}
    case DashAccess.L8{}:
      {==}
    case DashAccess.L9{}:
      {==}

# Order
# -----

# 10 * m <= 10 * v when m <= v
def dlp.mul_le(+m: Nat, +v: Nat, +h: {Nat.is_le(m, v) == True{} : Bool}) -> {Nat.is_le(Nat.mul(10n, m), Nat.mul(10n, v)) == True{} : Bool}:
  match m v:
    case 0n _:
      LNat.compactor.pc.le_zero(Nat.mul(10n, v))
    case 1n+p 0n:
      dlp.b_absurd({Nat.is_le(Nat.mul(10n, 1n+p), Nat.mul(10n, 0n)) == True{} : Bool}, h)
    case 1n++p 1n++q:
      %Equal.sym(Nat, Nat.mul(10n, 1n+p), Nat.add(10n, Nat.mul(10n, p)), LNat.wn_mul_succ_r(10n, p)) : {Nat.is_le(_, Nat.mul(10n, 1n+q)) == True{} : Bool}
      %Equal.sym(Nat, Nat.mul(10n, 1n+q), Nat.add(10n, Nat.mul(10n, q)), LNat.wn_mul_succ_r(10n, q)) : {Nat.is_le(Nat.add(10n, Nat.mul(10n, p)), _) == True{} : Bool}
      LNat.ps.le_mono(10n, Nat.mul(10n, p), Nat.mul(10n, q), dlp.mul_le(p, q, h))

def dlp.cap_ge.at(+b: Bool, +y: Nat, +x: Nat, +e: {Nat.is_le(x, 65535n) == b : Bool}, +hx: {Nat.is_le(y, x) == True{} : Bool}, +hy: {Nat.is_le(y, 65536n) == True{} : Bool}) -> {Nat.is_le(y, Ac.cap.at(b, x)) == True{} : Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the cap keeps every bound up to 65536
def dlp.cap_ge(+y: Nat, +x: Nat, +hx: {Nat.is_le(y, x) == True{} : Bool}, +hy: {Nat.is_le(y, 65536n) == True{} : Bool}) -> {Nat.is_le(y, Ac.cap(x)) == True{} : Bool}:
  dlp.cap_ge.at(Nat.is_le(x, 65535n), y, x, {==}, hx, hy)

def dlp.cap_top.at(+b: Bool, +x: Nat, +e: {Nat.is_le(x, 65535n) == b : Bool}, +h: {Nat.is_le(Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, 1n))))), x) == True{} : Bool}) -> {Ac.cap.at(b, x) == 65536n : Nat}:
  match b:
    case True{}:
      dlp.b_absurd({Ac.cap.at(True{}, x) == 65536n : Nat}, LNat.wn_le_trans(Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, 1n))))), x, 65535n, h, e))
    case False{}:
      {==}

# a value of at least 100000 caps to 65536
def dlp.cap_top(+x: Nat, +h: {Nat.is_le(Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, 1n))))), x) == True{} : Bool}) -> {Ac.cap(x) == 65536n : Nat}:
  dlp.cap_top.at(Nat.is_le(x, 65535n), x, {==}, h)

# 10 * m <= 10 * v + d when m <= v
def dlp.raw(+m: Nat, +v: Nat, +d: DashAccess.PortDigit, +h: {Nat.is_le(m, v) == True{} : Bool}) -> {Nat.is_le(Nat.mul(10n, m), Nat.add(Nat.mul(10n, v), dlp.val(d))) == True{} : Bool}:
  LNat.wn_le_trans(Nat.mul(10n, m), Nat.mul(10n, v), Nat.add(Nat.mul(10n, v), dlp.val(d)), dlp.mul_le(m, v, h), LNat.pu.le_add_r(Nat.mul(10n, v), dlp.val(d)))

# a digit multiplies a lower bound by 10, the cap allowing
def dlp.grow(+m: Nat, +v: Nat, +d: DashAccess.PortDigit, +h: {Nat.is_le(m, v) == True{} : Bool}, +small: {Nat.is_le(Nat.mul(10n, m), 65536n) == True{} : Bool}) -> {Nat.is_le(Nat.mul(10n, m), dlp.nx(v, d)) == True{} : Bool}:
  dlp.cap_ge(Nat.mul(10n, m), Nat.add(Nat.mul(10n, v), dlp.val(d)), dlp.raw(m, v, d, h), small)

# The run's value
# ---------------

# from 65536 the run stays 65536
def dlp.big_run(+ds: List<&2, DashAccess.PortDigit>) -> {Ac.digits(DashAccess.sp_digits(ds), 65536n) == Some{65536n} : Maybe<&2, Nat>}:
  match ds:
    case Nil{}:
      {==}
    case d <> t:
      %dlp.step(d, DashAccess.sp_digits(t), 65536n) : {_ == Some{65536n} : Maybe<&2, Nat>}
      %Equal.sym(Nat, dlp.nx(65536n, d), 65536n, dlp.top(d)) : {Ac.digits(DashAccess.sp_digits(t), _) == Some{65536n} : Maybe<&2, Nat>}
      dlp.big_run(t)

# the sixth digit, from a value of at least 10000
def dlp.run5(+d5: DashAccess.PortDigit, +ds: List<&2, DashAccess.PortDigit>, +v: Nat, +h: {Nat.is_le(Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, 1n)))), v) == True{} : Bool}) -> {Ac.digits(DashAccess.sp_digits(d5 <> ds), v) == Some{65536n} : Maybe<&2, Nat>}:
  %dlp.step(d5, DashAccess.sp_digits(ds), v) : {_ == Some{65536n} : Maybe<&2, Nat>}
  %Equal.sym(Nat, dlp.nx(v, d5), 65536n, dlp.cap_top(Nat.add(Nat.mul(10n, v), dlp.val(d5)), dlp.raw(Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, 1n)))), v, d5, h))) : {Ac.digits(DashAccess.sp_digits(ds), _) == Some{65536n} : Maybe<&2, Nat>}
  dlp.big_run(ds)

def dlp.run4(+d4: DashAccess.PortDigit, +d5: DashAccess.PortDigit, +ds: List<&2, DashAccess.PortDigit>, +v: Nat, +h: {Nat.is_le(Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, 1n))), v) == True{} : Bool}) -> {Ac.digits(DashAccess.sp_digits(d4 <> d5 <> ds), v) == Some{65536n} : Maybe<&2, Nat>}:
  %dlp.step(d4, DashAccess.sp_digits(d5 <> ds), v) : {_ == Some{65536n} : Maybe<&2, Nat>}
  dlp.run5(d5, ds, dlp.nx(v, d4), dlp.grow(Nat.mul(10n, Nat.mul(10n, Nat.mul(10n, 1n))), v, d4, h, {==}))

def dlp.run3(+d3: DashAccess.PortDigit, +d4: DashAccess.PortDigit, +d5: DashAccess.PortDigit, +ds: List<&2, DashAccess.PortDigit>, +v: Nat, +h: {Nat.is_le(Nat.mul(10n, Nat.mul(10n, 1n)), v) == True{} : Bool}) -> {Ac.digits(DashAccess.sp_digits(d3 <> d4 <> d5 <> ds), v) == Some{65536n} : Maybe<&2, Nat>}:
  %dlp.step(d3, DashAccess.sp_digits(d4 <> d5 <> ds), v) : {_ == Some{65536n} : Maybe<&2, Nat>}
  dlp.run4(d4, d5, ds, dlp.nx(v, d3), dlp.grow(Nat.mul(10n, Nat.mul(10n, 1n)), v, d3, h, {==}))

def dlp.run2(+d2: DashAccess.PortDigit, +d3: DashAccess.PortDigit, +d4: DashAccess.PortDigit, +d5: DashAccess.PortDigit, +ds: List<&2, DashAccess.PortDigit>, +v: Nat, +h: {Nat.is_le(Nat.mul(10n, 1n), v) == True{} : Bool}) -> {Ac.digits(DashAccess.sp_digits(d2 <> d3 <> d4 <> d5 <> ds), v) == Some{65536n} : Maybe<&2, Nat>}:
  %dlp.step(d2, DashAccess.sp_digits(d3 <> d4 <> d5 <> ds), v) : {_ == Some{65536n} : Maybe<&2, Nat>}
  dlp.run3(d3, d4, d5, ds, dlp.nx(v, d2), dlp.grow(Nat.mul(10n, 1n), v, d2, h, {==}))

def dlp.run1(+d1: DashAccess.PortDigit, +d2: DashAccess.PortDigit, +d3: DashAccess.PortDigit, +d4: DashAccess.PortDigit, +d5: DashAccess.PortDigit, +ds: List<&2, DashAccess.PortDigit>, +v: Nat, +h: {Nat.is_le(1n, v) == True{} : Bool}) -> {Ac.digits(DashAccess.sp_digits(d1 <> d2 <> d3 <> d4 <> d5 <> ds), v) == Some{65536n} : Maybe<&2, Nat>}:
  %dlp.step(d1, DashAccess.sp_digits(d2 <> d3 <> d4 <> d5 <> ds), v) : {_ == Some{65536n} : Maybe<&2, Nat>}
  dlp.run2(d2, d3, d4, d5, ds, dlp.nx(v, d1), dlp.grow(1n, v, d1, h, {==}))

# the long port reads as no port
def dlp.port_long(+a: DashAccess.PortLead, +d1: DashAccess.PortDigit, +d2: DashAccess.PortDigit, +d3: DashAccess.PortDigit, +d4: DashAccess.PortDigit, +d5: DashAccess.PortDigit, +ds: List<&2, DashAccess.PortDigit>) -> {Ac.port(SCon{DashAccess.sp_lead(a), DashAccess.sp_digits(d1 <> d2 <> d3 <> d4 <> d5 <> ds)}) == None{} : Maybe<&2, Nat>}:
  %dlp.lead(a, DashAccess.sp_digits(d1 <> d2 <> d3 <> d4 <> d5 <> ds)) : {_ == None{} : Maybe<&2, Nat>}
  %Equal.sym(Maybe<&2, Nat>, Ac.digits(DashAccess.sp_digits(d1 <> d2 <> d3 <> d4 <> d5 <> ds), dlp.lval(a)), Some{65536n}, dlp.run1(d1, d2, d3, d4, d5, ds, dlp.lval(a), dlp.lead_one(a))) : {Ac.num.fit(_) == None{} : Maybe<&2, Nat>}
  {==}

# Ports with a ':'
# ----------------

def dlp.keep_none(+b: Bool) -> {Ac.digits.keep(b, None{}) == None{} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# digits through a ':' are none
def dlp.digits_colon(+x: String, +q: String, +v: Nat) -> {Ac.digits(String.append(x, SCon{':', q}), v) == None{} : Maybe<&2, Nat>}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %Equal.sym(Maybe<&2, Nat>, Ac.digits(String.append(t, SCon{':', q}), Ac.cap(Nat.add(Nat.mul(10n, v), Ac.digit(c)))), None{}, dlp.digits_colon(t, q, Ac.cap(Nat.add(Nat.mul(10n, v), Ac.digit(c))))) : {Ac.digits.keep(Char.is_digit(c), _) == None{} : Maybe<&2, Nat>}
      dlp.keep_none(Char.is_digit(c))

def dlp.num_colon(+x: String, +q: String) -> {Ac.num(String.append(x, SCon{':', q})) == None{} : Maybe<&2, Nat>}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %Equal.sym(Maybe<&2, Nat>, Ac.digits(String.append(SCon{c, t}, SCon{':', q}), 0n), None{}, dlp.digits_colon(SCon{c, t}, q, 0n)) : {Ac.num.fit(_) == None{} : Maybe<&2, Nat>}
      {==}

def dlp.sign_colon(+b: Bool, +c: Char, +x: String, +q: String) -> {Ac.port.sign(b, c, String.append(x, SCon{':', q})) == None{} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      dlp.num_colon(x, q)
    case False{}:
      dlp.num_colon(SCon{c, x}, q)

# a port through a ':' is none
def dlp.port_colon(+x: String, +q: String) -> {Ac.port(String.append(x, SCon{':', q})) == None{} : Maybe<&2, Nat>}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, t}:
      dlp.sign_colon(Char.is_eq(c, '+'), c, t, q)

# Authorities
# -----------

def dlp.wp_none(+h: String, +m: Maybe<&2, Nat>, +e: {m == None{} : Maybe<&2, Nat>}) -> {Ac.with_port(h, m) == Ac.NoAuthority{} : Ac.Authority}:
  %Equal.sym(Maybe<&2, Nat>, m, None{}, e) : {Ac.with_port(h, _) == Ac.NoAuthority{} : Ac.Authority}
  {==}

def dlp.after_colon(+b: Bool, +h: String, +x: String, +p: String) -> {Ac.after.colon(b, h, String.append(x, SCon{':', p})) == Ac.NoAuthority{} : Ac.Authority}:
  match b:
    case True{}:
      dlp.wp_none(h, Ac.port(String.append(x, SCon{':', p})), dlp.port_colon(x, p))
    case False{}:
      {==}

# after a bracketed host, text through a ':' before the long port: no
# authority
def dlp.after_any(+h: String, +x: String, +p: String, +np: {Ac.port(p) == None{} : Maybe<&2, Nat>}) -> {Ac.after(h, String.append(x, SCon{':', p})) == Ac.NoAuthority{} : Ac.Authority}:
  match x:
    case SNil{}:
      dlp.wp_none(h, Ac.port(p), np)
    case SCon{c, t}:
      dlp.after_colon(Char.is_eq(c, ':'), h, t, p)

def dlp.wp_cons(+m: Maybe<&2, Nat>, -h: String, +g: String, +e: {Ac.with_port(h, m) == Ac.NoAuthority{} : Ac.Authority}) -> {Ac.with_port(g, m) == Ac.NoAuthority{} : Ac.Authority}:
  match m:
    case None{}:
      {==}
    case Some{k}:
      dlp.au_absurd({Ac.with_port(g, Some{k}) == Ac.NoAuthority{} : Ac.Authority}, h, Some{k}, e)

def dlp.colon_cons(+b: Bool, -h: String, +g: String, +q: String, +e: {Ac.after.colon(b, h, q) == Ac.NoAuthority{} : Ac.Authority}) -> {Ac.after.colon(b, g, q) == Ac.NoAuthority{} : Ac.Authority}:
  match b:
    case True{}:
      dlp.wp_cons(Ac.port(q), h, g, e)
    case False{}:
      {==}

def dlp.after_cons(-h: String, +g: String, +t: String, +e: {Ac.after(h, t) == Ac.NoAuthority{} : Ac.Authority}) -> {Ac.after(g, t) == Ac.NoAuthority{} : Ac.Authority}:
  match t:
    case SNil{}:
      dlp.au_absurd({Ac.after(g, SNil{}) == Ac.NoAuthority{} : Ac.Authority}, h, None{}, e)
    case SCon{d, q}:
      dlp.colon_cons(Char.is_eq(d, ':'), h, g, q, e)

# a char before a bracketed cut keeps it no authority
def dlp.bracket_cons(+c: Char, +r: Maybe<&2, Ac.Cut>, +e: {Ac.bracket(r) == Ac.NoAuthority{} : Ac.Authority}) -> {Ac.bracket(Ac.cons(c, r)) == Ac.NoAuthority{} : Ac.Authority}:
  match r:
    case None{}:
      {==}
    case Some{u}:
      match u:
        case Ac.Cut{h, t}:
          dlp.after_cons(h, SCon{c, h}, t, e)

# the digit run holds no ']'
def dlp.close_run(+ds: List<&2, DashAccess.PortDigit>) -> {Ac.close(DashAccess.sp_digits(ds)) == None{} : Maybe<&2, Ac.Cut>}:
  match ds:
    case Nil{}:
      {==}
    case d <> t:
      %Equal.sym(Bool, Char.is_eq(DashAccess.sp_digit(d), ']'), False{}, dlp.no_close(d)) : {Ac.close.at(_, DashAccess.sp_digit(d), DashAccess.sp_digits(t), Ac.close(DashAccess.sp_digits(t))) == None{} : Maybe<&2, Ac.Cut>}
      %Equal.sym(Maybe<&2, Ac.Cut>, Ac.close(DashAccess.sp_digits(t)), None{}, dlp.close_run(t)) : {Ac.close.at(False{}, DashAccess.sp_digit(d), DashAccess.sp_digits(t), _) == None{} : Maybe<&2, Ac.Cut>}
      {==}

# the port text holds no ']'
def dlp.close_port(+a: DashAccess.PortLead, +ds: List<&2, DashAccess.PortDigit>) -> {Ac.close(SCon{DashAccess.sp_lead(a), DashAccess.sp_digits(ds)}) == None{} : Maybe<&2, Ac.Cut>}:
  %Equal.sym(Bool, Char.is_eq(DashAccess.sp_lead(a), ']'), False{}, dlp.lead_no_close(a)) : {Ac.close.at(_, DashAccess.sp_lead(a), DashAccess.sp_digits(ds), Ac.close(DashAccess.sp_digits(ds))) == None{} : Maybe<&2, Ac.Cut>}
  %Equal.sym(Maybe<&2, Ac.Cut>, Ac.close(DashAccess.sp_digits(ds)), None{}, dlp.close_run(ds)) : {Ac.close.at(False{}, DashAccess.sp_lead(a), DashAccess.sp_digits(ds), _) == None{} : Maybe<&2, Ac.Cut>}
  {==}

def dlp.bracket_at(+b: Bool, +c: Char, +t: String, +n: String, +p: String, +np: {Ac.port(p) == None{} : Maybe<&2, Nat>}, +et: {t == String.append(n, SCon{':', p}) : String}, +ih: {Ac.bracket(Ac.close(t)) == Ac.NoAuthority{} : Ac.Authority}) -> {Ac.bracket(Ac.close.at(b, c, t, Ac.close(t))) == Ac.NoAuthority{} : Ac.Authority}:
  match b:
    case True{}:
      %Equal.sym(String, t, String.append(n, SCon{':', p}), et) : {Ac.after(SCon{c, SNil{}}, _) == Ac.NoAuthority{} : Ac.Authority}
      dlp.after_any(SCon{c, SNil{}}, n, p, np)
    case False{}:
      dlp.bracket_cons(c, Ac.close(t), ih)

# whatever the host, a bracketed reading ends with no authority
def dlp.bracket_any(+n: String, +a: DashAccess.PortLead, +ds: List<&2, DashAccess.PortDigit>, +np: {Ac.port(SCon{DashAccess.sp_lead(a), DashAccess.sp_digits(ds)}) == None{} : Maybe<&2, Nat>}) -> {Ac.bracket(Ac.close(String.append(n, SCon{':', SCon{DashAccess.sp_lead(a), DashAccess.sp_digits(ds)}}))) == Ac.NoAuthority{} : Ac.Authority}:
  match n:
    case SNil{}:
      %Equal.sym(Maybe<&2, Ac.Cut>, Ac.close(SCon{DashAccess.sp_lead(a), DashAccess.sp_digits(ds)}), None{}, dlp.close_port(a, ds)) : {Ac.bracket(Ac.cons(':', _)) == Ac.NoAuthority{} : Ac.Authority}
      {==}
    case SCon{c, t}:
      dlp.bracket_at(Char.is_eq(c, ']'), c, String.append(t, SCon{':', SCon{DashAccess.sp_lead(a), DashAccess.sp_digits(ds)}}), t, SCon{DashAccess.sp_lead(a), DashAccess.sp_digits(ds)}, np, {==}, dlp.bracket_any(t, a, ds, np))

# the digit run holds no ':'
def dlp.last_run(+ds: List<&2, DashAccess.PortDigit>) -> {Ac.last(DashAccess.sp_digits(ds)) == None{} : Maybe<&2, Ac.Cut>}:
  match ds:
    case Nil{}:
      {==}
    case d <> t:
      %Equal.sym(Maybe<&2, Ac.Cut>, Ac.last(DashAccess.sp_digits(t)), None{}, dlp.last_run(t)) : {Ac.last.at(DashAccess.sp_digit(d), DashAccess.sp_digits(t), _) == None{} : Maybe<&2, Ac.Cut>}
      %Equal.sym(Bool, Char.is_eq(DashAccess.sp_digit(d), ':'), False{}, dlp.no_colon(d)) : {Ac.last.here(_, DashAccess.sp_digits(t)) == None{} : Maybe<&2, Ac.Cut>}
      {==}

# the port text holds no ':'
def dlp.last_port(+a: DashAccess.PortLead, +ds: List<&2, DashAccess.PortDigit>) -> {Ac.last(SCon{DashAccess.sp_lead(a), DashAccess.sp_digits(ds)}) == None{} : Maybe<&2, Ac.Cut>}:
  %Equal.sym(Maybe<&2, Ac.Cut>, Ac.last(DashAccess.sp_digits(ds)), None{}, dlp.last_run(ds)) : {Ac.last.at(DashAccess.sp_lead(a), DashAccess.sp_digits(ds), _) == None{} : Maybe<&2, Ac.Cut>}
  %Equal.sym(Bool, Char.is_eq(DashAccess.sp_lead(a), ':'), False{}, dlp.lead_no_colon(a)) : {Ac.last.here(_, DashAccess.sp_digits(ds)) == None{} : Maybe<&2, Ac.Cut>}
  {==}

# the last ':' is the one before the port
def dlp.last_any(+n: String, +p: String, +np: {Ac.last(p) == None{} : Maybe<&2, Ac.Cut>}) -> {Ac.last(String.append(n, SCon{':', p})) == Some{Ac.Cut{n, p}} : Maybe<&2, Ac.Cut>}:
  match n:
    case SNil{}:
      %Equal.sym(Maybe<&2, Ac.Cut>, Ac.last(p), None{}, np) : {Ac.last.at(':', p, _) == Some{Ac.Cut{SNil{}, p}} : Maybe<&2, Ac.Cut>}
      {==}
    case SCon{c, t}:
      %Equal.sym(Maybe<&2, Ac.Cut>, Ac.last(String.append(t, SCon{':', p})), Some{Ac.Cut{t, p}}, dlp.last_any(t, p, np)) : {Ac.last.at(c, String.append(t, SCon{':', p}), _) == Some{Ac.Cut{SCon{c, t}, p}} : Maybe<&2, Ac.Cut>}
      {==}

def dlp.plain_host(+b: Bool, +n: String, +p: String, +np: {Ac.port(p) == None{} : Maybe<&2, Nat>}) -> {Ac.plain.host(b, n, Some{p}) == Ac.NoAuthority{} : Ac.Authority}:
  match b:
    case True{}:
      {==}
    case False{}:
      dlp.wp_none(n, Ac.port(p), np)

# whatever the host, a plain reading ends with no authority
def dlp.plain_any(+n: String, +p: String, +nl: {Ac.last(p) == None{} : Maybe<&2, Ac.Cut>}, +np: {Ac.port(p) == None{} : Maybe<&2, Nat>}) -> {Ac.plain(String.append(n, SCon{':', p}), Ac.last(String.append(n, SCon{':', p}))) == Ac.NoAuthority{} : Ac.Authority}:
  %Equal.sym(Maybe<&2, Ac.Cut>, Ac.last(String.append(n, SCon{':', p})), Some{Ac.Cut{n, p}}, dlp.last_any(n, p, nl)) : {Ac.plain(String.append(n, SCon{':', p}), _) == Ac.NoAuthority{} : Ac.Authority}
  dlp.plain_host(Bool.or(String.is_empty(n), Ac.colons(n)), n, p, np)

# Split
# -----

def dlp.form(+b: Bool, +s: String, +hb: {Ac.bracket(Ac.close(s)) == Ac.NoAuthority{} : Ac.Authority}, +hp: {Ac.plain(s, Ac.last(s)) == Ac.NoAuthority{} : Ac.Authority}) -> {Ac.split.form(b, s) == Ac.NoAuthority{} : Ac.Authority}:
  match b:
    case True{}:
      hb
    case False{}:
      hp

def dlp.ok(+b: Bool, +c: Char, +t: String, +hb: {Ac.bracket(Ac.close(SCon{c, t})) == Ac.NoAuthority{} : Ac.Authority}, +hp: {Ac.plain(SCon{c, t}, Ac.last(SCon{c, t})) == Ac.NoAuthority{} : Ac.Authority}) -> {Ac.split.ok(b, c, t) == Ac.NoAuthority{} : Ac.Authority}:
  match b:
    case True{}:
      {==}
    case False{}:
      dlp.form(Char.is_eq(c, '['), SCon{c, t}, hb, hp)

def dlp.split(+n: String, +p: String, +hb: {Ac.bracket(Ac.close(String.append(n, SCon{':', p}))) == Ac.NoAuthority{} : Ac.Authority}, +hp: {Ac.plain(String.append(n, SCon{':', p}), Ac.last(String.append(n, SCon{':', p}))) == Ac.NoAuthority{} : Ac.Authority}) -> {Ac.split(String.append(n, SCon{':', p})) == Ac.NoAuthority{} : Ac.Authority}:
  match n:
    case SNil{}:
      dlp.ok(Ac.stops(SCon{':', p}), ':', p, hb, hp)
    case SCon{c, t}:
      dlp.ok(Ac.stops(SCon{c, String.append(t, SCon{':', p})}), c, String.append(t, SCon{':', p}), hb, hp)

def DashAccess.dash_access_host_long_port(n, a, d1, d2, d3, d4, d5, ds, al):
  +np = dlp.port_long(a, d1, d2, d3, d4, d5, ds)
  %Equal.sym(Ac.Authority, Ac.split(String.append(n, SCon{':', SCon{DashAccess.sp_lead(a), DashAccess.sp_digits(d1 <> d2 <> d3 <> d4 <> d5 <> ds)}})), Ac.NoAuthority{}, dlp.split(n, SCon{DashAccess.sp_lead(a), DashAccess.sp_digits(d1 <> d2 <> d3 <> d4 <> d5 <> ds)}, dlp.bracket_any(n, a, d1 <> d2 <> d3 <> d4 <> d5 <> ds, np), dlp.plain_any(n, SCon{DashAccess.sp_lead(a), DashAccess.sp_digits(d1 <> d2 <> d3 <> d4 <> d5 <> ds)}, dlp.last_port(a, d1 <> d2 <> d3 <> d4 <> d5 <> ds), np))) : {Ac.host_allowed.of(_, al) == False{} : Bool}
  {==}
