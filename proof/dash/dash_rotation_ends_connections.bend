# eukhe: the proof of LAW dash_rotation_ends_connections

import Base
import ../../bend/dash.bend as Da
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pa.and_l(a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LA.dashboard_auth.pa.absurdF({False{} == True{} : Bool}, h)

def pa.and_r(a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LA.dashboard_auth.pa.absurdF({b == True{} : Bool}, h)

def pa.eq_le(a: Nat, b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LA.dashboard_auth.pa.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pa.eq_le(p, q, h)

def pa.le_succ(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      LA.dashboard_auth.pa.absurdF({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pa.le_succ(p, q, h)

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

def pa.made_stale(+cur: Nat, m: Maybe<&2, Nat>, +h: {pa.made(cur, m) == True{} : Bool}) -> {LA.pa.stale(1n+cur, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      LA.pa.le_lt_succ(t, cur, h)

# a rotation makes every connection of a reachable state stale
def pa.rotate_stale(+s: Da.St, +c: Nat, +h: {pa.inv(Da.St.cur(s), Da.St.conns(s)) == True{} : Bool}) -> {LA.pa.stale(Da.St.cur(Da.next(s, Da.Rotate{})), Da.held(c, Da.St.conns(Da.next(s, Da.Rotate{})))) == True{} : Bool}:
  match s:
    case Da.St{+cur, +cs}:
      pa.made_stale(cur, Da.held(c, cs), pa.held_made(c, cur, cs, h))

def pa.rotation_ends_connections(+hist: List<&2, Da.Ev>, +c: Nat, +evs: List<&2, Da.Ev>, +again: {Da.any_opens(c, evs) == False{} : Bool}) -> {Da.any_ran(c, Da.run(Da.Rotate{} <> evs, Da.state(hist, Da.init()))) == False{} : Bool}:
  LA.pa.quiet(evs, Da.next(Da.state(hist, Da.init()), Da.Rotate{}), c, pa.rotate_stale(Da.state(hist, Da.init()), c, pa.inv_state(hist, Da.init(), {==})), again)

def Laws.dash_rotation_ends_connections(hist, c, evs, again):
  pa.rotation_ends_connections(hist, c, evs, again)
