# proof_dashboard_auth: the D1 laws (laws/dashboard_auth.bend, the
# dashboard's pairing gate) of the model in bend/dash.bend.
#
# The gate compares a token with the current one, so an open pairs and a
# frame runs exactly when the token is the current one. A connection is
# "stale" when it is not open, or holds a token older than the current
# one. A stale connection stays stale under every event but its own open
# (a rotation only makes its token older; other connections' events do
# not touch its row), and a stale connection runs no frame. A connection
# that is not open, or was rejected, is stale. Every reachable state holds
# only tokens made so far (at most the current one), so a rotation makes
# every open connection stale; and the current token only grows, so a
# token older than it never becomes current again.
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters), with an equation that names it.

import Base
import ./dash.bend as Da

# Logic
# -----

def pa.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pa.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pa.BD(_, A, Unit)
  Unit{}

def pa.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pa.BD(_, Unit, A)
  Unit{}

def pa.or_l(a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      pa.absurdT({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pa.or_r(a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      pa.absurdT({b == False{} : Bool}, h)
    case False{}:
      h

def pa.and_l(a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pa.absurdF({False{} == True{} : Bool}, h)

def pa.and_r(a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pa.absurdF({b == True{} : Bool}, h)

# Numbers
# -------

def pa.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pa.eq_refl(p)

def pa.eq_true(a: Nat, b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pa.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      pa.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pa.eq_true(p, q, h))

def pa.eq_le(a: Nat, b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      pa.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pa.eq_le(p, q, h)

def pa.le_succ(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      pa.absurdF({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pa.le_succ(p, q, h)

def pa.le_lt_succ(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      pa.absurdF({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pa.le_lt_succ(p, q, h)

def pa.lt_succ(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      pa.absurdF({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pa.lt_succ(p, q, h)

def pa.lt_ne(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      pa.absurdF({True{} == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pa.lt_ne(p, q, h)

# The gate
# --------

def pa.ran_ok(+c: Nat, b: Bool, +h: {Da.ran(c, Da.frame.ran(c, b)) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      pa.absurdF({False{} == True{} : Bool}, h)

def pa.paired_ok(c: Nat, b: Bool, +h: {Da.is_paired(Da.open.out(c, b)) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      pa.absurdF({False{} == True{} : Bool}, h)

def pa.rejected_no(c: Nat, b: Bool, +h: {Da.is_paired(Da.open.out(c, b)) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      pa.absurdT({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# a frame that runs has the current token
def pa.frame_ran_cur(+c: Nat, m: Maybe<&2, Nat>, +cur: Nat, +h: {Da.ran(c, Da.frame.out(c, m, cur)) == True{} : Bool}) -> {m == Some{cur} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      pa.absurdF({None{} == Some{cur} : Maybe<&2, Nat>}, h)
    case Some{+t}:
      Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, t, cur, pa.eq_true(t, cur, pa.ran_ok(c, Nat.is_eq(t, cur), h)))

# an admitted token is the current one
def pa.admit_cur(+cur: Nat, shown: Maybe<&2, Nat>, +h: {Da.admit(cur, shown) == True{} : Bool}) -> {shown == Some{cur} : Maybe<&2, Nat>}:
  match shown:
    case None{}:
      pa.absurdF({None{} == Some{cur} : Maybe<&2, Nat>}, h)
    case Some{+t}:
      Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, t, cur, pa.eq_true(t, cur, h))

# The connection table
# --------------------

def pa.hds_put(+c: Nat, +i: Nat, t: Nat, r: List<&2, Da.Conn>, hit: Bool, +eh: {Nat.is_eq(i, c) == hit : Bool}, +hr: {Da.held(c, r) == None{} : Maybe<&2, Nat>}) -> {Da.held(c, Da.drop.put(Da.Conn{i, t}, r, hit)) == None{} : Maybe<&2, Nat>}:
  match hit:
    case True{}:
      hr
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(i, c), False{}, eh) : {Da.held.put(t, Da.held(c, r), _) == None{} : Maybe<&2, Nat>}
      hr

# no row of c is left once c is dropped
def pa.held_drop_same(+c: Nat, cs: List<&2, Da.Conn>) -> {Da.held(c, Da.drop(c, cs)) == None{} : Maybe<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case Da.Conn{+i, +t} <> +rest:
      pa.hds_put(c, i, t, Da.drop(c, rest), Nat.is_eq(i, c), {==}, pa.held_drop_same(c, rest))

def pa.hdo_put(+c: Nat, +x: Nat, +i: Nat, +t: Nat, +rest: List<&2, Da.Conn>, hit: Bool, +eh: {Nat.is_eq(i, x) == hit : Bool}, +ne: {Nat.is_eq(x, c) == False{} : Bool}, +ih: {Da.held(c, Da.drop(x, rest)) == Da.held(c, rest) : Maybe<&2, Nat>}) -> {Da.held(c, Da.drop.put(Da.Conn{i, t}, Da.drop(x, rest), hit)) == Da.held.put(t, Da.held(c, rest), Nat.is_eq(i, c)) : Maybe<&2, Nat>}:
  match hit:
    case True{}:
      %Equal.sym(Nat, i, x, pa.eq_true(i, x, eh)) : {Da.held(c, Da.drop(x, rest)) == Da.held.put(t, Da.held(c, rest), Nat.is_eq(_, c)) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Nat.is_eq(x, c), False{}, ne) : {Da.held(c, Da.drop(x, rest)) == Da.held.put(t, Da.held(c, rest), _) : Maybe<&2, Nat>}
      ih
    case False{}:
      %Equal.sym(Maybe<&2, Nat>, Da.held(c, Da.drop(x, rest)), Da.held(c, rest), ih) : {Da.held.put(t, _, Nat.is_eq(i, c)) == Da.held.put(t, Da.held(c, rest), Nat.is_eq(i, c)) : Maybe<&2, Nat>}
      {==}

# dropping another connection leaves the row of c as it was
def pa.held_drop_other(+c: Nat, +x: Nat, cs: List<&2, Da.Conn>, +ne: {Nat.is_eq(x, c) == False{} : Bool}) -> {Da.held(c, Da.drop(x, cs)) == Da.held(c, cs) : Maybe<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case Da.Conn{+i, +t} <> +rest:
      pa.hdo_put(c, x, i, t, rest, Nat.is_eq(i, x), {==}, ne, pa.held_drop_other(c, x, rest, ne))

def pa.held_keep_other(+c: Nat, +x: Nat, +t: Nat, b: Bool, +cs: List<&2, Da.Conn>, +ne: {Nat.is_eq(x, c) == False{} : Bool}) -> {Da.held(c, Da.open.keep(x, t, b, cs)) == Da.held(c, cs) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(x, c), False{}, ne) : {Da.held.put(t, Da.held(c, cs), _) == Da.held(c, cs) : Maybe<&2, Nat>}
      {==}
    case False{}:
      {==}

# an open of another connection leaves the row of c as it was
def pa.held_open_other(+c: Nat, +x: Nat, shown: Maybe<&2, Nat>, +cur: Nat, +cs: List<&2, Da.Conn>, +ne: {Nat.is_eq(x, c) == False{} : Bool}) -> {Da.held(c, Da.open.next(x, shown, cur, Da.drop(x, cs))) == Da.held(c, cs) : Maybe<&2, Nat>}:
  match shown:
    case None{}:
      pa.held_drop_other(c, x, cs, ne)
    case Some{+t}:
      %Equal.sym(Maybe<&2, Nat>, Da.held(c, Da.open.keep(x, t, Nat.is_eq(t, cur), Da.drop(x, cs))), Da.held(c, Da.drop(x, cs)), pa.held_keep_other(c, x, t, Nat.is_eq(t, cur), Da.drop(x, cs), ne)) : {_ == Da.held(c, cs) : Maybe<&2, Nat>}
      pa.held_drop_other(c, x, cs, ne)

# a frame of another connection leaves the row of c as it was
def pa.held_frame_other(+c: Nat, +x: Nat, b: Bool, +cs: List<&2, Da.Conn>, +ne: {Nat.is_eq(x, c) == False{} : Bool}) -> {Da.held(c, Da.frame.next(x, b, cs)) == Da.held(c, cs) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      pa.held_drop_other(c, x, cs, ne)

# Stale connections
# -----------------

# not open, or holding a token older than cur
def pa.stale(+cur: Nat, m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{t}:
      Nat.is_lt(t, cur)

# a row equal to a stale one is stale
def pa.stale_eq(+cur: Nat, m: Maybe<&2, Nat>, n: Maybe<&2, Nat>, +e: {m == n : Maybe<&2, Nat>}, +h: {pa.stale(cur, n) == True{} : Bool}) -> {pa.stale(cur, m) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, m, n, e) : {pa.stale(cur, _) == True{} : Bool}
  h

def pa.stale_succ(+cur: Nat, m: Maybe<&2, Nat>, +h: {pa.stale(cur, m) == True{} : Bool}) -> {pa.stale(1n+cur, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      pa.lt_succ(t, cur, h)

# a stale row is not admitted
def pa.stale_no(+cur: Nat, m: Maybe<&2, Nat>, +h: {pa.stale(cur, m) == True{} : Bool}) -> {Da.admit(cur, m) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      pa.lt_ne(t, cur, h)

# a stale connection's frame does not run
def pa.stale_frame(+c: Nat, m: Maybe<&2, Nat>, +cur: Nat, +h: {pa.stale(cur, m) == True{} : Bool}) -> {Da.ran(c, Da.frame.out(c, m, cur)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+t}:
      %Equal.sym(Bool, Nat.is_eq(t, cur), False{}, pa.lt_ne(t, cur, h)) : {Da.ran(c, Da.frame.ran(c, _)) == False{} : Bool}
      {==}

def pa.fr_other(+c: Nat, +x: Nat, b: Bool, +ne: {Nat.is_eq(x, c) == False{} : Bool}) -> {Da.ran(c, Da.frame.ran(x, b)) == False{} : Bool}:
  match b:
    case True{}:
      ne
    case False{}:
      {==}

# another connection's frame runs no frame of c
def pa.frame_other(+c: Nat, +x: Nat, m: Maybe<&2, Nat>, +cur: Nat, +ne: {Nat.is_eq(x, c) == False{} : Bool}) -> {Da.ran(c, Da.frame.out(x, m, cur)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      pa.fr_other(c, x, Nat.is_eq(t, cur), ne)

def pa.open_not_ran(+c: Nat, x: Nat, b: Bool) -> {Da.ran(c, Da.open.out(x, b)) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a frame of x, while c is stale, runs no frame of c
def pa.frame_quiet(+c: Nat, +x: Nat, b: Bool, +eb: {Nat.is_eq(x, c) == b : Bool}, +cur: Nat, +cs: List<&2, Da.Conn>, +st: {pa.stale(cur, Da.held(c, cs)) == True{} : Bool}) -> {Da.ran(c, Da.frame.out(x, Da.held(x, cs), cur)) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, x, c, pa.eq_true(x, c, eb)) : {Da.ran(c, Da.frame.out(_, Da.held(_, cs), cur)) == False{} : Bool}
      pa.stale_frame(c, Da.held(c, cs), cur, st)
    case False{}:
      pa.frame_other(c, x, Da.held(x, cs), cur, eb)

# a frame of x, while c is stale, leaves c stale
def pa.frame_stale(+c: Nat, +x: Nat, b: Bool, +eb: {Nat.is_eq(x, c) == b : Bool}, +cur: Nat, +cs: List<&2, Da.Conn>, +st: {pa.stale(cur, Da.held(c, cs)) == True{} : Bool}) -> {pa.stale(cur, Da.held(c, Da.frame.next(x, Da.admit(cur, Da.held(x, cs)), cs))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, x, c, pa.eq_true(x, c, eb)) : {pa.stale(cur, Da.held(c, Da.frame.next(_, Da.admit(cur, Da.held(_, cs)), cs))) == True{} : Bool}
      %Equal.sym(Bool, Da.admit(cur, Da.held(c, cs)), False{}, pa.stale_no(cur, Da.held(c, cs), st)) : {pa.stale(cur, Da.held(c, Da.frame.next(c, _, cs))) == True{} : Bool}
      %Equal.sym(Maybe<&2, Nat>, Da.held(c, Da.drop(c, cs)), None{}, pa.held_drop_same(c, cs)) : {pa.stale(cur, _) == True{} : Bool}
      {==}
    case False{}:
      pa.stale_eq(cur, Da.held(c, Da.frame.next(x, Da.admit(cur, Da.held(x, cs)), cs)), Da.held(c, cs), pa.held_frame_other(c, x, Da.admit(cur, Da.held(x, cs)), cs, eb), st)

# one event, other than an open of c, runs no frame of a stale c
def pa.step_quiet(+s: Da.St, +e: Da.Ev, +c: Nat, +st: {pa.stale(Da.St.cur(s), Da.held(c, Da.St.conns(s))) == True{} : Bool}, +no: {Da.opens(c, e) == False{} : Bool}) -> {Da.ran(c, Da.out(s, e)) == False{} : Bool}:
  match s:
    case Da.St{+cur, +cs}:
      match e:
        case Da.Rotate{}:
          {==}
        case Da.Open{+x, shown}:
          pa.open_not_ran(c, x, Da.admit(cur, shown))
        case Da.Frame{+x}:
          pa.frame_quiet(c, x, Nat.is_eq(x, c), {==}, cur, cs, st)

# one event, other than an open of c, leaves a stale c stale
def pa.step_stale(+s: Da.St, +e: Da.Ev, +c: Nat, +st: {pa.stale(Da.St.cur(s), Da.held(c, Da.St.conns(s))) == True{} : Bool}, +no: {Da.opens(c, e) == False{} : Bool}) -> {pa.stale(Da.St.cur(Da.next(s, e)), Da.held(c, Da.St.conns(Da.next(s, e)))) == True{} : Bool}:
  match s:
    case Da.St{+cur, +cs}:
      match e:
        case Da.Rotate{}:
          pa.stale_succ(cur, Da.held(c, cs), st)
        case Da.Open{+x, +shown}:
          pa.stale_eq(cur, Da.held(c, Da.open.next(x, shown, cur, Da.drop(x, cs))), Da.held(c, cs), pa.held_open_other(c, x, shown, cur, cs, no), st)
        case Da.Frame{+x}:
          pa.frame_stale(c, x, Nat.is_eq(x, c), {==}, cur, cs, st)

# a stale connection runs no frame until it opens again
def pa.quiet(evs: List<&2, Da.Ev>, +s: Da.St, +c: Nat, +st: {pa.stale(Da.St.cur(s), Da.held(c, Da.St.conns(s))) == True{} : Bool}, +again: {Da.any_opens(c, evs) == False{} : Bool}) -> {Da.any_ran(c, Da.run(evs, s)) == False{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case +e <> +rest:
      %Equal.sym(Bool, Da.ran(c, Da.out(s, e)), False{}, pa.step_quiet(s, e, c, st, pa.or_l(Da.opens(c, e), Da.any_opens(c, rest), again))) : {Bool.or(_, Da.any_ran(c, Da.run(rest, Da.next(s, e)))) == False{} : Bool}
      pa.quiet(rest, Da.next(s, e), c, pa.step_stale(s, e, c, st, pa.or_l(Da.opens(c, e), Da.any_opens(c, rest), again)), pa.or_r(Da.opens(c, e), Da.any_opens(c, rest), again))

# a rejected open leaves its connection stale
def pa.rejected_stale(+s: Da.St, +c: Nat, +shown: Maybe<&2, Nat>, +rejected: {Da.is_paired(Da.out(s, Da.Open{c, shown})) == False{} : Bool}) -> {pa.stale(Da.St.cur(Da.next(s, Da.Open{c, shown})), Da.held(c, Da.St.conns(Da.next(s, Da.Open{c, shown})))) == True{} : Bool}:
  match s:
    case Da.St{+cur, +cs}:
      match shown:
        case None{}:
          %Equal.sym(Maybe<&2, Nat>, Da.held(c, Da.drop(c, cs)), None{}, pa.held_drop_same(c, cs)) : {pa.stale(cur, _) == True{} : Bool}
          {==}
        case Some{+t}:
          %Equal.sym(Bool, Nat.is_eq(t, cur), False{}, pa.rejected_no(c, Nat.is_eq(t, cur), rejected)) : {pa.stale(cur, Da.held(c, Da.open.keep(c, t, _, Da.drop(c, cs)))) == True{} : Bool}
          %Equal.sym(Maybe<&2, Nat>, Da.held(c, Da.drop(c, cs)), None{}, pa.held_drop_same(c, cs)) : {pa.stale(cur, _) == True{} : Bool}
          {==}

# Reachable states
# ----------------

# every token the table holds is at most cur
def pa.inv(+cur: Nat, cs: List<&2, Da.Conn>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Da.Conn{i, t} <> rest:
      Bool.and(Nat.is_le(t, cur), pa.inv(cur, rest))

def pa.inv_succ(+cur: Nat, cs: List<&2, Da.Conn>, +h: {pa.inv(cur, cs) == True{} : Bool}) -> {pa.inv(1n+cur, cs) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Da.Conn{i, +t} <> +rest:
      %Equal.sym(Bool, Nat.is_le(t, 1n+cur), True{}, pa.le_succ(t, cur, pa.and_l(Nat.is_le(t, cur), pa.inv(cur, rest), h))) : {Bool.and(_, pa.inv(1n+cur, rest)) == True{} : Bool}
      pa.inv_succ(cur, rest, pa.and_r(Nat.is_le(t, cur), pa.inv(cur, rest), h))

def pa.inv_put(+cur: Nat, +i: Nat, +t: Nat, r: List<&2, Da.Conn>, hit: Bool, +ht: {Nat.is_le(t, cur) == True{} : Bool}, +hr: {pa.inv(cur, r) == True{} : Bool}) -> {pa.inv(cur, Da.drop.put(Da.Conn{i, t}, r, hit)) == True{} : Bool}:
  match hit:
    case True{}:
      hr
    case False{}:
      %Equal.sym(Bool, Nat.is_le(t, cur), True{}, ht) : {Bool.and(_, pa.inv(cur, r)) == True{} : Bool}
      hr

def pa.inv_drop(+cur: Nat, +x: Nat, cs: List<&2, Da.Conn>, +h: {pa.inv(cur, cs) == True{} : Bool}) -> {pa.inv(cur, Da.drop(x, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Da.Conn{+i, +t} <> +rest:
      pa.inv_put(cur, i, t, Da.drop(x, rest), Nat.is_eq(i, x), pa.and_l(Nat.is_le(t, cur), pa.inv(cur, rest), h), pa.inv_drop(cur, x, rest, pa.and_r(Nat.is_le(t, cur), pa.inv(cur, rest), h)))

def pa.inv_keep(+cur: Nat, x: Nat, +t: Nat, b: Bool, +eb: {Nat.is_eq(t, cur) == b : Bool}, +cs: List<&2, Da.Conn>, +h: {pa.inv(cur, cs) == True{} : Bool}) -> {pa.inv(cur, Da.open.keep(x, t, b, cs)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_le(t, cur), True{}, pa.eq_le(t, cur, eb)) : {Bool.and(_, pa.inv(cur, cs)) == True{} : Bool}
      h
    case False{}:
      h

def pa.inv_open(+cur: Nat, +x: Nat, shown: Maybe<&2, Nat>, +cs: List<&2, Da.Conn>, +h: {pa.inv(cur, cs) == True{} : Bool}) -> {pa.inv(cur, Da.open.next(x, shown, cur, Da.drop(x, cs))) == True{} : Bool}:
  match shown:
    case None{}:
      pa.inv_drop(cur, x, cs, h)
    case Some{+t}:
      pa.inv_keep(cur, x, t, Nat.is_eq(t, cur), {==}, Da.drop(x, cs), pa.inv_drop(cur, x, cs, h))

def pa.inv_frame(+cur: Nat, +x: Nat, b: Bool, +cs: List<&2, Da.Conn>, +h: {pa.inv(cur, cs) == True{} : Bool}) -> {pa.inv(cur, Da.frame.next(x, b, cs)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      pa.inv_drop(cur, x, cs, h)

def pa.inv_next(+s: Da.St, +e: Da.Ev, +h: {pa.inv(Da.St.cur(s), Da.St.conns(s)) == True{} : Bool}) -> {pa.inv(Da.St.cur(Da.next(s, e)), Da.St.conns(Da.next(s, e))) == True{} : Bool}:
  match s:
    case Da.St{+cur, +cs}:
      match e:
        case Da.Rotate{}:
          pa.inv_succ(cur, cs, h)
        case Da.Open{+x, +shown}:
          pa.inv_open(cur, x, shown, cs, h)
        case Da.Frame{+x}:
          pa.inv_frame(cur, x, Da.admit(cur, Da.held(x, cs)), cs, h)

# every reachable state holds only tokens made so far
def pa.inv_state(evs: List<&2, Da.Ev>, +s: Da.St, +h: {pa.inv(Da.St.cur(s), Da.St.conns(s)) == True{} : Bool}) -> {pa.inv(Da.St.cur(Da.state(evs, s)), Da.St.conns(Da.state(evs, s))) == True{} : Bool}:
  match evs:
    case Nil{}:
      h
    case +e <> +rest:
      pa.inv_state(rest, Da.next(s, e), pa.inv_next(s, e, h))

# a row holds a token made so far, or none
def pa.made(+cur: Nat, m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{t}:
      Nat.is_le(t, cur)

def pa.made_put(+cur: Nat, +t: Nat, r: Maybe<&2, Nat>, hit: Bool, +ht: {Nat.is_le(t, cur) == True{} : Bool}, +hr: {pa.made(cur, r) == True{} : Bool}) -> {pa.made(cur, Da.held.put(t, r, hit)) == True{} : Bool}:
  match hit:
    case True{}:
      ht
    case False{}:
      hr

def pa.held_made(+c: Nat, +cur: Nat, cs: List<&2, Da.Conn>, +h: {pa.inv(cur, cs) == True{} : Bool}) -> {pa.made(cur, Da.held(c, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Da.Conn{+i, +t} <> +rest:
      pa.made_put(cur, t, Da.held(c, rest), Nat.is_eq(i, c), pa.and_l(Nat.is_le(t, cur), pa.inv(cur, rest), h), pa.held_made(c, cur, rest, pa.and_r(Nat.is_le(t, cur), pa.inv(cur, rest), h)))

def pa.made_stale(+cur: Nat, m: Maybe<&2, Nat>, +h: {pa.made(cur, m) == True{} : Bool}) -> {pa.stale(1n+cur, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      pa.le_lt_succ(t, cur, h)

# a rotation makes every connection of a reachable state stale
def pa.rotate_stale(+s: Da.St, +c: Nat, +h: {pa.inv(Da.St.cur(s), Da.St.conns(s)) == True{} : Bool}) -> {pa.stale(Da.St.cur(Da.next(s, Da.Rotate{})), Da.held(c, Da.St.conns(Da.next(s, Da.Rotate{})))) == True{} : Bool}:
  match s:
    case Da.St{+cur, +cs}:
      pa.made_stale(cur, Da.held(c, cs), pa.held_made(c, cur, cs, h))

# The current token only grows
# ----------------------------

def pa.lt_next(+s: Da.St, +e: Da.Ev, +t: Nat, +h: {Nat.is_lt(t, Da.St.cur(s)) == True{} : Bool}) -> {Nat.is_lt(t, Da.St.cur(Da.next(s, e))) == True{} : Bool}:
  match s:
    case Da.St{+cur, +cs}:
      match e:
        case Da.Rotate{}:
          pa.lt_succ(t, cur, h)
        case Da.Open{x, shown}:
          h
        case Da.Frame{x}:
          h

def pa.lt_state(evs: List<&2, Da.Ev>, +s: Da.St, +t: Nat, +h: {Nat.is_lt(t, Da.St.cur(s)) == True{} : Bool}) -> {Nat.is_lt(t, Da.St.cur(Da.state(evs, s))) == True{} : Bool}:
  match evs:
    case Nil{}:
      h
    case +e <> +rest:
      pa.lt_state(rest, Da.next(s, e), t, pa.lt_next(s, e, t, h))

def pa.lt_rotate(+s: Da.St, +t: Nat, +h: {Nat.is_le(t, Da.St.cur(s)) == True{} : Bool}) -> {Nat.is_lt(t, Da.St.cur(Da.next(s, Da.Rotate{}))) == True{} : Bool}:
  match s:
    case Da.St{+cur, +cs}:
      pa.le_lt_succ(t, cur, h)

# The laws
# --------

def pa.frame_runs_only_current(+s: Da.St, +c: Nat, +ran: {Da.ran(c, Da.out(s, Da.Frame{c})) == True{} : Bool}) -> {Da.held(c, Da.St.conns(s)) == Some{Da.St.cur(s)} : Maybe<&2, Nat>}:
  pa.frame_ran_cur(c, Da.held(c, Da.St.conns(s)), Da.St.cur(s), ran)

def pa.current_frame_runs(+s: Da.St, +c: Nat, +cur: {Da.held(c, Da.St.conns(s)) == Some{Da.St.cur(s)} : Maybe<&2, Nat>}) -> {Da.out(s, Da.Frame{c}) == Da.Ran{c} : Da.Out}:
  %Equal.sym(Maybe<&2, Nat>, Da.held(c, Da.St.conns(s)), Some{Da.St.cur(s)}, cur) : {Da.frame.out(c, _, Da.St.cur(s)) == Da.Ran{c} : Da.Out}
  %pa.eq_refl(Da.St.cur(s)) : {Da.frame.ran(c, _) == Da.Ran{c} : Da.Out}
  {==}

def pa.open_pairs_only_current(+s: Da.St, +c: Nat, +shown: Maybe<&2, Nat>, +paired: {Da.is_paired(Da.out(s, Da.Open{c, shown})) == True{} : Bool}) -> {shown == Some{Da.St.cur(s)} : Maybe<&2, Nat>}:
  pa.admit_cur(Da.St.cur(s), shown, pa.paired_ok(c, Da.admit(Da.St.cur(s), shown), paired))

def pa.current_open_pairs(+s: Da.St, +c: Nat) -> {Da.out(s, Da.Open{c, Some{Da.St.cur(s)}}) == Da.Paired{c} : Da.Out}:
  %pa.eq_refl(Da.St.cur(s)) : {Da.open.out(c, _) == Da.Paired{c} : Da.Out}
  {==}

def pa.paired_holds_token(+s: Da.St, +c: Nat) -> {Da.held(c, Da.St.conns(Da.next(s, Da.Open{c, Some{Da.St.cur(s)}}))) == Some{Da.St.cur(s)} : Maybe<&2, Nat>}:
  match s:
    case Da.St{+cur, +cs}:
      %pa.eq_refl(cur) : {Da.held(c, Da.open.keep(c, cur, _, Da.drop(c, cs))) == Some{cur} : Maybe<&2, Nat>}
      %pa.eq_refl(c) : {Da.held.put(cur, Da.held(c, Da.drop(c, cs)), _) == Some{cur} : Maybe<&2, Nat>}
      {==}

def pa.closed_runs_nothing(+s: Da.St, +c: Nat, +evs: List<&2, Da.Ev>, +closed: {Da.held(c, Da.St.conns(s)) == None{} : Maybe<&2, Nat>}, +again: {Da.any_opens(c, evs) == False{} : Bool}) -> {Da.any_ran(c, Da.run(evs, s)) == False{} : Bool}:
  pa.quiet(evs, s, c, pa.stale_eq(Da.St.cur(s), Da.held(c, Da.St.conns(s)), None{}, closed, {==}), again)

def pa.rejected_runs_nothing(+s: Da.St, +c: Nat, +shown: Maybe<&2, Nat>, +evs: List<&2, Da.Ev>, +rejected: {Da.is_paired(Da.out(s, Da.Open{c, shown})) == False{} : Bool}, +again: {Da.any_opens(c, evs) == False{} : Bool}) -> {Da.any_ran(c, Da.run(Da.Open{c, shown} <> evs, s)) == False{} : Bool}:
  %Equal.sym(Bool, Da.ran(c, Da.out(s, Da.Open{c, shown})), False{}, pa.open_not_ran(c, c, Da.admit(Da.St.cur(s), shown))) : {Bool.or(_, Da.any_ran(c, Da.run(evs, Da.next(s, Da.Open{c, shown})))) == False{} : Bool}
  pa.quiet(evs, Da.next(s, Da.Open{c, shown}), c, pa.rejected_stale(s, c, shown, rejected), again)

def pa.rotation_ends_connections(+hist: List<&2, Da.Ev>, +c: Nat, +evs: List<&2, Da.Ev>, +again: {Da.any_opens(c, evs) == False{} : Bool}) -> {Da.any_ran(c, Da.run(Da.Rotate{} <> evs, Da.state(hist, Da.init()))) == False{} : Bool}:
  pa.quiet(evs, Da.next(Da.state(hist, Da.init()), Da.Rotate{}), c, pa.rotate_stale(Da.state(hist, Da.init()), c, pa.inv_state(hist, Da.init(), {==})), again)

def pa.rotation_rejects_old_tokens(+hist: List<&2, Da.Ev>, +more: List<&2, Da.Ev>, +c: Nat, +t: Nat, +old: {Nat.is_le(t, Da.St.cur(Da.state(hist, Da.init()))) == True{} : Bool}) -> {Da.out(Da.state(Da.Rotate{} <> more, Da.state(hist, Da.init())), Da.Open{c, Some{t}}) == Da.Rejected{c} : Da.Out}:
  %Equal.sym(Bool, Nat.is_eq(t, Da.St.cur(Da.state(more, Da.next(Da.state(hist, Da.init()), Da.Rotate{})))), False{}, pa.lt_ne(t, Da.St.cur(Da.state(more, Da.next(Da.state(hist, Da.init()), Da.Rotate{}))), pa.lt_state(more, Da.next(Da.state(hist, Da.init()), Da.Rotate{}), t, pa.lt_rotate(Da.state(hist, Da.init()), t, old)))) : {Da.open.out(c, _) == Da.Rejected{c} : Da.Out}
  {==}
