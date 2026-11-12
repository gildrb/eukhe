# harness (spec): a stored tool call lifted to the current dialect of its
# family (area call_lift), as the harness design states it ("version everything the
# model sees": every call is stamped `family@rev`; old calls lift into the
# current dialect so histories stay coherent across model switches;
# replay at the same rev is byte-stable), restated without the code of
# bend/call_lift.bend. spec/harness/lift_wire.bend holds the wire of the
# entry. The laws of area call_lift (laws/call_lift.bend) state that the
# code refines it. A spec: the shipped code never calls it.
#
# L1: a call's family is the first of the table with its name; a family
#     the table lacks leaves the call unknown (untouched).
# L2: a call at its family's current rev is current (untouched).
# L3: the chain of a rev: the first step leaving it, then the first
#     leaving the rev that one arrives at, and so on, at most as many
#     steps as the family has; it arrives at the first step whose target
#     is the current rev. A rev whose chain never arrives is stranded:
#     the call is kept as stored.
# L4: the ops of the chain's steps, in order, change the stored
#     arguments (each kept at its index, in order): a rename moves the
#     first argument named `from` to `to` when `to` is free (receipt
#     renamed), else moves nothing (receipt clashed), and does nothing
#     without a `from`; a fill adds a missing name after the others
#     (receipt filled) and leaves a present one.
# L5: a lifted call takes the current rev of its family.

import Base
import ../../bend/call_lift.bend as Cl

# The family (L1)
# ---------------

def pick_rev(hit: Bool, c: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{c}
    case False{}:
      rest

# the current rev of the first family named f
def current(t: List<&2, Cl.Fam>, +f: String) -> Maybe<&2, String>:
  match t:
    case Nil{}:
      None{}
    case Con{x, rest}:
      match x:
        case Cl.Fam{+n, c, s}:
          pick_rev(String.eq(n, f), c, current(rest, f))

def pick_steps(hit: Bool, s: List<&2, Cl.Step>, rest: List<&2, Cl.Step>) -> List<&2, Cl.Step>:
  match hit:
    case True{}:
      s
    case False{}:
      rest

# the steps of the first family named f (none without one)
def steps_of(t: List<&2, Cl.Fam>, +f: String) -> List<&2, Cl.Step>:
  match t:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      match x:
        case Cl.Fam{+n, c, s}:
          pick_steps(String.eq(n, f), s, steps_of(rest, f))

# The chain (L3)
# --------------

def pick_step(hit: Bool, x: Cl.Step, rest: Maybe<&2, Cl.Step>) -> Maybe<&2, Cl.Step>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      rest

# the first step leaving rev r
def next(ss: List<&2, Cl.Step>, +r: String) -> Maybe<&2, Cl.Step>:
  match ss:
    case Nil{}:
      None{}
    case Con{x, rest}:
      match x:
        case Cl.Step{+a, b, o}:
          pick_step(String.eq(a, r), Cl.Step{a, b, o}, next(rest, r))

def chain.join(st: Cl.Step, arrived: Bool, rest: Maybe<&2, List<&2, Cl.Step>>) -> Maybe<&2, List<&2, Cl.Step>>:
  match arrived:
    case True{}:
      Some{[st]}
    case False{}:
      match rest:
        case None{}:
          None{}
        case Some{p}:
          Some{st <> p}

# the steps from the one found to the current rev cur, at most n of them;
# none when the chain never arrives
def chain(n: Nat, +ss: List<&2, Cl.Step>, +cur: String, found: Maybe<&2, Cl.Step>) -> Maybe<&2, List<&2, Cl.Step>>:
  match n:
    case 0n:
      None{}
    case 1n+m:
      match found:
        case None{}:
          None{}
        case Some{st}:
          match st:
            case Cl.Step{a, +b, o}:
              chain.join(Cl.Step{a, b, o}, String.eq(b, cur), chain(m, ss, cur, next(ss, b)))

# the ops of a chain, step by step
def ops_of(p: List<&2, Cl.Step>) -> List<&2, Cl.Op>:
  match p:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      match x:
        case Cl.Step{a, b, o}:
          List.append(&2, Cl.Op, o, ops_of(rest))

# The arguments (L4)
# ------------------

def key_of(a: Cl.Arg) -> String:
  match a:
    case Cl.Kept{i, k}:
      k
    case Cl.Added{k, j}:
      k

def named(a: Cl.Arg, k: String) -> Cl.Arg:
  match a:
    case Cl.Kept{i, o}:
      Cl.Kept{i, k}
    case Cl.Added{o, j}:
      Cl.Added{k, j}

# some argument is named k
def taken(args: List<&2, Cl.Arg>, +k: String) -> Bool:
  match args:
    case Nil{}:
      False{}
    case Con{+a, rest}:
      Bool.or(String.eq(key_of(a), k), taken(rest, k))

def move.at(hit: Bool, a: Cl.Arg, rest: List<&2, Cl.Arg>, moved: List<&2, Cl.Arg>, to: String) -> List<&2, Cl.Arg>:
  match hit:
    case True{}:
      named(a, to) <> rest
    case False{}:
      a <> moved

# the first argument named from, now named to
def move(args: List<&2, Cl.Arg>, +from: String, +to: String) -> List<&2, Cl.Arg>:
  match args:
    case Nil{}:
      Nil{}
    case Con{+a, +rest}:
      move.at(String.eq(key_of(a), from), a, rest, move(rest, from, to), to)

def op_rename(present: Bool, taken_to: Bool, +from: String, +to: String, +args: List<&2, Cl.Arg>, rs: List<&2, Cl.Receipt>) -> Cl.St:
  match present:
    case False{}:
      Cl.St{args, rs}
    case True{}:
      match taken_to:
        case True{}:
          Cl.St{args, List.append(&2, Cl.Receipt, rs, [Cl.Clashed{from, to}])}
        case False{}:
          Cl.St{move(args, from, to), List.append(&2, Cl.Receipt, rs, [Cl.Renamed{from, to}])}

def op_fill(present: Bool, +key: String, json: String, args: List<&2, Cl.Arg>, rs: List<&2, Cl.Receipt>) -> Cl.St:
  match present:
    case True{}:
      Cl.St{args, rs}
    case False{}:
      Cl.St{List.append(&2, Cl.Arg, args, [Cl.Added{key, json}]), List.append(&2, Cl.Receipt, rs, [Cl.Filled{key}])}

# one op on the arguments and receipts
def op(o: Cl.Op, st: Cl.St) -> Cl.St:
  match o:
    case Cl.Rename{+from, +to}:
      match st:
        case Cl.St{+args, rs}:
          op_rename(taken(args, from), taken(args, to), from, to, args, rs)
    case Cl.Fill{+key, json}:
      match st:
        case Cl.St{+args, rs}:
          op_fill(taken(args, key), key, json, args, rs)

# the ops, in order
def ops(os: List<&2, Cl.Op>, st: Cl.St) -> Cl.St:
  match os:
    case Nil{}:
      st
    case Con{o, rest}:
      ops(rest, op(o, st))

# the stored arguments, each kept at its index, from i
def stored(ks: List<&2, String>, +i: Nat) -> List<&2, Cl.Arg>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{k, rest}:
      Cl.Kept{i, k} <> stored(rest, 1n+i)

# The lift (L1-L5)
# ----------------

def lift_spec.done(cur: String, st: Cl.St) -> Cl.Lift:
  match st:
    case Cl.St{a, rs}:
      Cl.Lifted{cur, a, rs}

def lift_spec.chain(cur: String, ks: List<&2, String>, p: Maybe<&2, List<&2, Cl.Step>>) -> Cl.Lift:
  match p:
    case None{}:
      Cl.Stranded{}
    case Some{path}:
      lift_spec.done(cur, ops(ops_of(path), Cl.St{stored(ks, 0n), []}))

def lift_spec.at(at: Bool, cur: String, ks: List<&2, String>, p: Maybe<&2, List<&2, Cl.Step>>) -> Cl.Lift:
  match at:
    case True{}:
      Cl.Current{}
    case False{}:
      lift_spec.chain(cur, ks, p)

def lift_spec.cur(+r: String, ks: List<&2, String>, m: Maybe<&2, String>, +ss: List<&2, Cl.Step>) -> Cl.Lift:
  match m:
    case None{}:
      Cl.Unknown{}
    case Some{+cur}:
      lift_spec.at(String.eq(r, cur), cur, ks, chain(List.length(&2, Cl.Step, ss), ss, cur, next(ss, r)))

# the lift of call c by table t
def lift_spec(+t: List<&2, Cl.Fam>, c: Cl.Call) -> Cl.Lift:
  match c:
    case Cl.Call{+f, r, ks}:
      lift_spec.cur(r, ks, current(t, f), steps_of(t, f))

# Terms of the laws
# -----------------

def arrives(p: Maybe<&2, List<&2, Cl.Step>>) -> Bool:
  match p:
    case None{}:
      False{}
    case Some{x}:
      True{}

def known.at(+r: String, m: Maybe<&2, String>, +ss: List<&2, Cl.Step>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+cur}:
      Bool.or(String.eq(r, cur), arrives(chain(List.length(&2, Cl.Step, ss), ss, cur, next(ss, r))))

# rev r of family f is known to table t: the current rev, or one whose
# chain arrives at it
def known(+t: List<&2, Cl.Fam>, +f: String, +r: String) -> Bool:
  known.at(r, current(t, f), steps_of(t, f))

def same_rev(rev: String, m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      String.eq(rev, c)

# a lift leaves the call at the current rev of family f: already there, or
# lifted to it
def at_current(t: List<&2, Cl.Fam>, +f: String, l: Cl.Lift) -> Bool:
  match l:
    case Cl.Unknown{}:
      False{}
    case Cl.Current{}:
      True{}
    case Cl.Stranded{}:
      False{}
    case Cl.Lifted{rev, a, rs}:
      same_rev(rev, current(t, f))

def keys_of(a: List<&2, Cl.Arg>) -> List<&2, String>:
  match a:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      key_of(x) <> keys_of(rest)

def applied.l(f: String, r: String, ks: List<&2, String>, l: Cl.Lift) -> Cl.Call:
  match l:
    case Cl.Unknown{}:
      Cl.Call{f, r, ks}
    case Cl.Current{}:
      Cl.Call{f, r, ks}
    case Cl.Stranded{}:
      Cl.Call{f, r, ks}
    case Cl.Lifted{rev, a, rs}:
      Cl.Call{f, rev, keys_of(a)}

# the call a lift leaves: its family at the lifted rev with the lifted
# argument names, or the call as stored
def applied(c: Cl.Call, l: Cl.Lift) -> Cl.Call:
  match c:
    case Cl.Call{f, r, ks}:
      applied.l(f, r, ks, l)

# what a second lift of the applied call answers: a lifted call is current
def settled(l: Cl.Lift) -> Cl.Lift:
  match l:
    case Cl.Unknown{}:
      Cl.Unknown{}
    case Cl.Current{}:
      Cl.Current{}
    case Cl.Stranded{}:
      Cl.Stranded{}
    case Cl.Lifted{rev, a, rs}:
      Cl.Current{}

# the stored indices, in order, of the kept arguments
def kept_indices(a: List<&2, Cl.Arg>) -> List<&2, Nat>:
  match a:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      match x:
        case Cl.Kept{i, k}:
          i <> kept_indices(rest)
        case Cl.Added{k, j}:
          kept_indices(rest)

# the indices i, i+1, ... of the names ks
def upto(ks: List<&2, String>, +i: Nat) -> List<&2, Nat>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{k, rest}:
      i <> upto(rest, 1n+i)

# the stored indices a lift keeps: those of its arguments, every one of a
# call kept as stored
def kept_of(ks: List<&2, String>, l: Cl.Lift) -> List<&2, Nat>:
  match l:
    case Cl.Unknown{}:
      upto(ks, 0n)
    case Cl.Current{}:
      upto(ks, 0n)
    case Cl.Stranded{}:
      upto(ks, 0n)
    case Cl.Lifted{rev, a, rs}:
      kept_indices(a)

def added_count(a: List<&2, Cl.Arg>) -> Nat:
  match a:
    case Nil{}:
      0n
    case Con{x, rest}:
      match x:
        case Cl.Kept{i, k}:
          added_count(rest)
        case Cl.Added{k, j}:
          1n+added_count(rest)

def filled_count(rs: List<&2, Cl.Receipt>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{x, rest}:
      match x:
        case Cl.Renamed{a, b}:
          filled_count(rest)
        case Cl.Clashed{a, b}:
          filled_count(rest)
        case Cl.Filled{k}:
          1n+filled_count(rest)

# the arguments a lift added, and its filled receipts
def added_of(l: Cl.Lift) -> Nat:
  match l:
    case Cl.Unknown{}:
      0n
    case Cl.Current{}:
      0n
    case Cl.Stranded{}:
      0n
    case Cl.Lifted{rev, a, rs}:
      added_count(a)

def filled_of(l: Cl.Lift) -> Nat:
  match l:
    case Cl.Unknown{}:
      0n
    case Cl.Current{}:
      0n
    case Cl.Stranded{}:
      0n
    case Cl.Lifted{rev, a, rs}:
      filled_count(rs)
