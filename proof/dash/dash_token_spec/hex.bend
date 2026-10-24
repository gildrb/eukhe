# eukhe: the hex lemmas of LAW dash_token_spec (and dash_stored_spec)
#
# The code's search for a digit (find) is the spec's (sp_at). The code
# looks a char up among the lowercase digits, then among "ABCDEF" from 10;
# the spec looks it up among the lowercase digits, then among the
# uppercase ones from 0: a char that is no lowercase digit is none of
# "0123456789" either, so both find the same (hx.pre: the shared prefix
# is skipped in step). The code reads exactly k pairs (bytes); the spec
# reads every pair, then asks for 32 bytes: both agree once the count is
# checked at the end (hx.len), and a byte is h*16 + l = 16*h + l.

import Base
import ../../../bend/dash.bend as Da
import ../../../laws/dash.bend as Dash
import ../../base/nat.bend as LNat

# Digits
# ------

def hx.hit(b: Bool, -n: Nat, -r: Maybe<&2, Nat>) -> {Da.find.hit(b, n, r) == Dash.sp_at.hit(b, n, r) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's search is the spec's
def hx.find(+c: Char, ds: String, +n: Nat) -> {Da.find(c, ds, n) == Dash.sp_at(c, ds, n) : Maybe<&2, Nat>}:
  match ds:
    case SNil{}:
      {==}
    case SCon{+d, +rest}:
      %hx.find(c, rest, 1n+n) : {Da.find.hit(Char.is_eq(c, d), n, Da.find(c, rest, 1n+n)) == Dash.sp_at.hit(Char.is_eq(c, d), n, _) : Maybe<&2, Nat>}
      hx.hit(Char.is_eq(c, d), n, Da.find(c, rest, 1n+n))

def hx.upper(+c: Char, m: Maybe<&2, Nat>) -> {Da.digit.upper(c, m) == Dash.sp_digit.or(m, Dash.sp_at(c, "ABCDEF", 10n)) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      hx.find(c, "ABCDEF", 10n)
    case Some{v}:
      {==}

def hx.app(p: String, q: String) -> String:
  match p:
    case SNil{}:
      q
    case SCon{x, t}:
      SCon{x, hx.app(t, q)}

# n moved past p
def hx.off(p: String, n: Nat) -> Nat:
  match p:
    case SNil{}:
      n
    case SCon{x, t}:
      hx.off(t, 1n+n)

def hx.pre.hit(b: Bool, -n: Nat, -a: Maybe<&2, Nat>, -u: Maybe<&2, Nat>, -w: Maybe<&2, Nat>, ih: {Dash.sp_digit.or(a, u) == Dash.sp_digit.or(a, w) : Maybe<&2, Nat>}) -> {Dash.sp_digit.or(Dash.sp_at.hit(b, n, a), Dash.sp_at.hit(b, n, u)) == Dash.sp_digit.or(Dash.sp_at.hit(b, n, a), w) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# two digit strings that share the prefix p: a char not found in the
# first one's prefix is not in the second one's either
def hx.pre(+c: Char, p: String, +lo: String, +up: String, +n: Nat) -> {Dash.sp_digit.or(Dash.sp_at(c, hx.app(p, lo), n), Dash.sp_at(c, hx.app(p, up), n)) == Dash.sp_digit.or(Dash.sp_at(c, hx.app(p, lo), n), Dash.sp_at(c, up, hx.off(p, n))) : Maybe<&2, Nat>}:
  match p:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      hx.pre.hit(Char.is_eq(c, x), n, Dash.sp_at(c, hx.app(t, lo), 1n+n), Dash.sp_at(c, hx.app(t, up), 1n+n), Dash.sp_at(c, up, hx.off(t, 1n+n)), hx.pre(c, t, lo, up, 1n+n))

# the code's value of a hex digit is the spec's
def hx.digit(+c: Char) -> {Da.digit(c) == Dash.sp_digit(c) : Maybe<&2, Nat>}:
  +lo = Dash.sp_at(c, "0123456789abcdef", 0n)
  Equal.trans(Maybe<&2, Nat>, Da.digit(c), Da.digit.upper(c, lo), Dash.sp_digit(c),
    Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>, m => Da.digit.upper(c, m), Da.find(c, "0123456789abcdef", 0n), lo, hx.find(c, "0123456789abcdef", 0n)),
    Equal.trans(Maybe<&2, Nat>, Da.digit.upper(c, lo), Dash.sp_digit.or(lo, Dash.sp_at(c, "ABCDEF", 10n)), Dash.sp_digit(c),
      hx.upper(c, lo),
      Equal.sym(Maybe<&2, Nat>, Dash.sp_digit(c), Dash.sp_digit.or(lo, Dash.sp_at(c, "ABCDEF", 10n)), hx.pre(c, "0123456789", "abcdef", "ABCDEF", 0n))))

# Bytes
# -----

def hx.mul16(h: Nat) -> {Nat.mul(h, 16n) == Nat.mul(16n, h) : Nat}:
  match h:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat, Nat.mul(1n+p, 16n), Nat.add(16n, Nat.mul(16n, p)), Nat.mul(16n, 1n+p),
        Equal.cong(Nat, Nat, z => Nat.add(16n, z), Nat.mul(p, 16n), Nat.mul(16n, p), hx.mul16(p)),
        Equal.sym(Nat, Nat.mul(16n, 1n+p), Nat.add(16n, Nat.mul(16n, p)), LNat.wn_mul_succ_r(16n, p)))

# the bytes m, when they are k
def hx.len(+k: Nat, m: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case None{}:
      None{}
    case Some{+bs}:
      Dash.sp_len64.is(Nat.is_eq(List.length(&2, Nat, bs), k), bs)

def hx.byte.is(b: Bool, +h: Nat, +l: Nat, -bs: List<&2, Nat>) -> {Da.byte(Some{h}, Some{l}, Dash.sp_len64.is(b, bs)) == Dash.sp_len64.is(b, Nat.add(Nat.mul(16n, h), l) <> bs) : Maybe<&2, List<&2, Nat>>}:
  match b:
    case True{}:
      %hx.mul16(h) : {Some{Nat.add(Nat.mul(h, 16n), l) <> bs} == Some{Nat.add(_, l) <> bs} : Maybe<&2, List<&2, Nat>>}
      {==}
    case False{}:
      {==}

# one pair in front of j checked bytes is j+1 checked bytes
def hx.byte(x: Maybe<&2, Nat>, y: Maybe<&2, Nat>, r: Maybe<&2, List<&2, Nat>>, +j: Nat) -> {Da.byte(x, y, hx.len(j, r)) == hx.len(1n+j, Dash.sp_cons(Dash.sp_pair(x, y), r)) : Maybe<&2, List<&2, Nat>>}:
  match x:
    case None{}:
      {==}
    case Some{+h}:
      match y:
        case None{}:
          {==}
        case Some{+l}:
          match r:
            case None{}:
              {==}
            case Some{+bs}:
              hx.byte.is(Nat.is_eq(List.length(&2, Nat, bs), j), h, l, bs)

# a pair or more is no zero bytes
def hx.len0(m: Maybe<&2, Nat>, r: Maybe<&2, List<&2, Nat>>) -> {None{} == hx.len(0n, Dash.sp_cons(m, r)) : Maybe<&2, List<&2, Nat>>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      match r:
        case None{}:
          {==}
        case Some{xs}:
          {==}

# the code's k bytes are the spec's pairs, when they are k
def hx.bytes(k: Nat, s: String) -> {Da.bytes(k, s) == hx.len(k, Dash.sp_hex(s)) : Maybe<&2, List<&2, Nat>>}:
  match k:
    case 0n:
      match s:
        case SNil{}:
          {==}
        case SCon{a, t}:
          match t:
            case SNil{}:
              {==}
            case SCon{b, u}:
              hx.len0(Dash.sp_pair(Dash.sp_digit(a), Dash.sp_digit(b)), Dash.sp_hex(u))
    case 1n++j:
      match s:
        case SNil{}:
          {==}
        case SCon{+a, t}:
          match t:
            case SNil{}:
              {==}
            case SCon{+b, +u}:
              %Equal.sym(Maybe<&2, Nat>, Da.digit(a), Dash.sp_digit(a), hx.digit(a)) : {Da.byte(_, Da.digit(b), Da.bytes(j, u)) == hx.len(1n+j, Dash.sp_cons(Dash.sp_pair(Dash.sp_digit(a), Dash.sp_digit(b)), Dash.sp_hex(u))) : Maybe<&2, List<&2, Nat>>}
              %Equal.sym(Maybe<&2, Nat>, Da.digit(b), Dash.sp_digit(b), hx.digit(b)) : {Da.byte(Dash.sp_digit(a), _, Da.bytes(j, u)) == hx.len(1n+j, Dash.sp_cons(Dash.sp_pair(Dash.sp_digit(a), Dash.sp_digit(b)), Dash.sp_hex(u))) : Maybe<&2, List<&2, Nat>>}
              %Equal.sym(Maybe<&2, List<&2, Nat>>, Da.bytes(j, u), hx.len(j, Dash.sp_hex(u)), hx.bytes(j, u)) : {Da.byte(Dash.sp_digit(a), Dash.sp_digit(b), _) == hx.len(1n+j, Dash.sp_cons(Dash.sp_pair(Dash.sp_digit(a), Dash.sp_digit(b)), Dash.sp_hex(u))) : Maybe<&2, List<&2, Nat>>}
              hx.byte(Dash.sp_digit(a), Dash.sp_digit(b), Dash.sp_hex(u), j)

def hx.len64(m: Maybe<&2, List<&2, Nat>>) -> {hx.len(32n, m) == Dash.sp_len64(m) : Maybe<&2, List<&2, Nat>>}:
  match m:
    case None{}:
      {==}
    case Some{bs}:
      {==}

# the code's token is the spec's
def hx.token(+s: String) -> {Da.parse(s) == Dash.sp_token(s) : Maybe<&2, List<&2, Nat>>}:
  Equal.trans(Maybe<&2, List<&2, Nat>>, Da.bytes(32n, s), hx.len(32n, Dash.sp_hex(s)), Dash.sp_token(s), hx.bytes(32n, s), hx.len64(Dash.sp_hex(s)))
