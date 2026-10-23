# eukhe: lemmas the proofs of area dash share

import Base
import ../../bend/dash.bend as Da

# ---- dashboard_auth ----

# proof_dashboard_auth: the D1 laws (LAWS.bend section dashboard_auth, the
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

# Logic
# -----

def dashboard_auth.pa.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def dashboard_auth.pa.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : dashboard_auth.pa.BD(_, A, Unit)
  Unit{}

def dashboard_auth.pa.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : dashboard_auth.pa.BD(_, Unit, A)
  Unit{}

def pa.or_l(a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      dashboard_auth.pa.absurdT({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pa.or_r(a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      dashboard_auth.pa.absurdT({b == False{} : Bool}, h)
    case False{}:
      h

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
      dashboard_auth.pa.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      dashboard_auth.pa.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pa.eq_true(p, q, h))

def pa.le_lt_succ(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      dashboard_auth.pa.absurdF({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pa.le_lt_succ(p, q, h)

def pa.lt_succ(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      dashboard_auth.pa.absurdF({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pa.lt_succ(p, q, h)

def pa.lt_ne(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      dashboard_auth.pa.absurdF({True{} == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pa.lt_ne(p, q, h)

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
