# harness (spec): a stored tool call lifted to the current dialect of its
# family (area call_lift), as its requirement states it ("version everything the
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

def lift_spec.done(cur: String, st: Cl.St) -> Cl.Lift:
  match st:
    case Cl.St{a, rs}:
      Cl.Lifted{cur, a, rs}

def op_fill(present: Bool, +key: String, json: String, args: List<&2, Cl.Arg>, rs: List<&2, Cl.Receipt>) -> Cl.St:
  match present:
    case True{}:
      Cl.St{args, rs}
    case False{}:
      Cl.St{List.append(&2, Cl.Arg, args, [Cl.Added{key, json}]), List.append(&2, Cl.Receipt, rs, [Cl.Filled{key}])}

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

# some argument is named k
def taken(args: List<&2, Cl.Arg>, +k: String) -> Bool:
  match args:
    case Nil{}:
      False{}
    case Con{+a, rest}:
      Bool.or(String.eq(key_of(a), k), taken(rest, k))

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

# the ops of a chain, step by step
def ops_of(p: List<&2, Cl.Step>) -> List<&2, Cl.Op>:
  match p:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      match x:
        case Cl.Step{a, b, o}:
          List.append(&2, Cl.Op, o, ops_of(rest))

# the stored arguments, each kept at its index, from i
def stored(ks: List<&2, String>, +i: Nat) -> List<&2, Cl.Arg>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{k, rest}:
      Cl.Kept{i, k} <> stored(rest, 1n+i)

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

# the lift of call c by table t
def lift_spec(+t: List<&2, Cl.Fam>, c: Cl.Call) -> Cl.Lift:
  match c:
    case Cl.Call{+f, r, ks}:
      lift_spec.cur(r, ks, current(t, f), steps_of(t, f))
