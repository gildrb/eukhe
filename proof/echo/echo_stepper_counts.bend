# eukhe: the proof of LAW echo_stepper_counts
#
# PROOF: the premise makes the open a count k (state Echo{k, ""}, reply k);
# from a counting state Echo{n, last} the reply to the i-th event is n+1+i,
# a space and the event before it (last before the first): es.step, by
# induction on the events, (n+1)+(1+j) read as n+(1+(1+j)) (es.add_one).

import Base
import ../../bend/ffi_echo.bend as FEc
import ../../laws/echo.bend as Echo
import ./base.bend as LA

# (n + 1) + m is n + (1 + m)
def es.add_one(n: Nat, -m: Nat) -> {Nat.add(Nat.add(n, 1n), m) == Nat.add(n, 1n+m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, 1n), m), Nat.add(p, 1n+m), es.add_one(p, m))

# the event before the i-th of evs, last before the first
def es.before(last: String, evs: List<&2, String>, i: Nat) -> String:
  match i:
    case 0n:
      last
    case 1n+j:
      Maybe.default(&2, String, List.get(&2, String, evs, j), "")

# the event before the (1+j)-th of e <> t is the event before the j-th of t,
# e before the first
def es.before_cons(e: String, t: List<&2, String>, j: Nat) -> {es.before(e, t, j) == Maybe.default(&2, String, List.get(&2, String, e <> t, j), "") : String}:
  match j:
    case 0n:
      {==}
    case 1n+m:
      {==}

# from a counting state Echo{n, last} and the reply x, the reply to the
# i-th event is n+1+i, a space and the event before it; none past the events
def es.step(evs: List<&2, String>, +n: Nat, +last: String, +x: String, i: Nat) -> {List.get(&2, String, Echo.ec_feed(evs, (FEc.Echo{n, last}, x)), 1n+i) == Echo.ec_if_event(List.get(&2, String, evs, i), String.append(Nat.show(Nat.add(n, 1n+i)), SCon{' ', es.before(last, evs, i)})) : Maybe<&2, String>}:
  match evs:
    case Nil{}:
      {==}
    case +e <> +t:
      match i:
        case 0n:
          LA.eb.head(t, FEc.Echo{Nat.add(n, 1n), e}, String.append(Nat.show(Nat.add(n, 1n)), SCon{' ', last}))
        case 1n+(+j):
          +y = String.append(Nat.show(Nat.add(n, 1n)), SCon{' ', last})
          %es.add_one(n, 1n+j) : {List.get(&2, String, Echo.ec_feed(t, (FEc.Echo{Nat.add(n, 1n), e}, y)), 1n+j) == Echo.ec_if_event(List.get(&2, String, t, j), String.append(Nat.show(_), SCon{' ', Maybe.default(&2, String, List.get(&2, String, e <> t, j), "")})) : Maybe<&2, String>}
          %es.before_cons(e, t, j) : {List.get(&2, String, Echo.ec_feed(t, (FEc.Echo{Nat.add(n, 1n), e}, y)), 1n+j) == Echo.ec_if_event(List.get(&2, String, t, j), String.append(Nat.show(Nat.add(Nat.add(n, 1n), 1n+j)), SCon{' ', _})) : Maybe<&2, String>}
          es.step(t, Nat.add(n, 1n), e, y, j)

# the open's count n and reply x: es.step with nothing before the first event
def es.opened(evs: List<&2, String>, +n: Nat, +x: String, i: Nat) -> {List.get(&2, String, Echo.ec_feed(evs, (FEc.Echo{n, ""}, x)), 1n+i) == Echo.ec_if_event(List.get(&2, String, evs, i), String.append(Nat.show(Nat.add(n, 1n+i)), SCon{' ', Echo.ec_before(evs, i)})) : Maybe<&2, String>}:
  match i:
    case 0n:
      es.step(evs, n, "", x, 0n)
    case 1n+j:
      es.step(evs, n, "", x, 1n+j)

def Echo.echo_stepper_counts(input, k, read, evs, i):
  %Equal.sym(Maybe<&2, U32>, U32.read(input), Some{k}, read) : ({List.get(&2, String, Echo.ec_feed(evs, FEc.open.start(_)), 0n) == Some{U32.show(k)} : Maybe<&2, String>} & {List.get(&2, String, Echo.ec_feed(evs, FEc.open.start(_)), 1n+i) == Echo.ec_if_event(List.get(&2, String, evs, i), String.append(Nat.show(Nat.add(U32.to_nat(k), 1n+i)), SCon{' ', Echo.ec_before(evs, i)})) : Maybe<&2, String>})
  (LA.eb.head(evs, FEc.Echo{U32.to_nat(k), ""}, U32.show(k)), es.opened(evs, U32.to_nat(k), U32.show(k), i))
