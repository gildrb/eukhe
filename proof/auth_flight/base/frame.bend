# eukhe: lemmas of the proofs of laws/auth_flight/desk.bend: the desk's
# list moves (find, cut, set) on a caller written where it stands (the
# callers pre, none of them numbered k, then caller k, then post), and its
# joiner moves (unwait, wake, joined) as the laws' filters (af_others,
# af_waiters) and map (af_tell).

import Base
import ../../../bend/auth_flight.bend as F
import ../../../laws/auth_flight/entry.bend as S
import ../../../laws/auth_flight/safety.bend as SS
import ../../../laws/auth_flight/desk.bend as DL
import ./logic.bend as AL
import ./entry.bend as LAE

# Bool.or(a, b) is False: a is
def fr.or_f1(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LAE.ae.tf({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# Bool.or(a, b) is False: b is
def fr.or_f2(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LAE.ae.tf({b == False{} : Bool}, h)
    case False{}:
      h

# k is k, turned to rewrite with
def fr.self(+k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  Equal.sym(Bool, Nat.is_eq(k, k), True{}, AL.ad.eq_refl(k))

# j is not k, turned to rewrite with
def fr.not(+j: Nat, +k: Nat, h: {Nat.is_eq(j, k) == False{} : Bool}) -> {False{} == Nat.is_eq(j, k) : Bool}:
  Equal.sym(Bool, Nat.is_eq(j, k), False{}, h)

# x before both sides of an equation
def fr.cons(-A: Data, +x: A, -r1: List<&2, A>, -r2: List<&2, A>, e: {r1 == r2 : List<&2, A>}) -> {x <> r1 == x <> r2 : List<&2, A>}:
  Equal.cong(List<&2, A>, List<&2, A>, r => x <> r, r1, r2, e)

# the first caller numbered k is the one after pre
def fr.find(+k: Nat, pre: List<&2, F.Cl>, +p: String, +a: F.At, +post: List<&2, F.Cl>, +nl: {SS.af_live(k, pre) == False{} : Bool}) -> {F.find(k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)) == Some{F.Cl{k, p, a}} : Maybe<&2, F.Cl>}:
  match pre:
    case Nil{}:
      %fr.self(k) : {F.find.at(_, F.Cl{k, p, a}, F.find(k, post)) == Some{F.Cl{k, p, a}} : Maybe<&2, F.Cl>}
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +q, +b}:
          %fr.not(j, k, fr.or_f1(Nat.is_eq(j, k), SS.af_live(k, t), nl)) : {F.find.at(_, F.Cl{j, q, b}, F.find(k, List.append(&2, F.Cl, t, F.Cl{k, p, a} <> post))) == Some{F.Cl{k, p, a}} : Maybe<&2, F.Cl>}
          fr.find(k, t, p, a, post, fr.or_f2(Nat.is_eq(j, k), SS.af_live(k, t), nl))

# no live caller numbered k: none is found
def fr.find_none(+k: Nat, cs: List<&2, F.Cl>, +nl: {SS.af_live(k, cs) == False{} : Bool}) -> {F.find(k, cs) == None{} : Maybe<&2, F.Cl>}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +q, +b}:
          %fr.not(j, k, fr.or_f1(Nat.is_eq(j, k), SS.af_live(k, t), nl)) : {F.find.at(_, F.Cl{j, q, b}, F.find(k, t)) == None{} : Maybe<&2, F.Cl>}
          fr.find_none(k, t, fr.or_f2(Nat.is_eq(j, k), SS.af_live(k, t), nl))

# caller k leaves: pre, then post
def fr.cut(+k: Nat, pre: List<&2, F.Cl>, +p: String, +a: F.At, +post: List<&2, F.Cl>, +nl: {SS.af_live(k, pre) == False{} : Bool}) -> {F.cut(k, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)) == List.append(&2, F.Cl, pre, post) : List<&2, F.Cl>}:
  match pre:
    case Nil{}:
      %fr.self(k) : {F.cut.at(_, F.Cl{k, p, a}, post, F.cut(k, post)) == post : List<&2, F.Cl>}
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +q, +b}:
          %fr.not(j, k, fr.or_f1(Nat.is_eq(j, k), SS.af_live(k, t), nl)) : {F.cut.at(_, F.Cl{j, q, b}, List.append(&2, F.Cl, t, F.Cl{k, p, a} <> post), F.cut(k, List.append(&2, F.Cl, t, F.Cl{k, p, a} <> post))) == F.Cl{j, q, b} <> List.append(&2, F.Cl, t, post) : List<&2, F.Cl>}
          fr.cons(F.Cl, F.Cl{j, q, b}, F.cut(k, List.append(&2, F.Cl, t, F.Cl{k, p, a} <> post)), List.append(&2, F.Cl, t, post), fr.cut(k, t, p, a, post, fr.or_f2(Nat.is_eq(j, k), SS.af_live(k, t), nl)))

# caller k stands at a2, every other caller where it stood
def fr.set(+k: Nat, +a2: F.At, pre: List<&2, F.Cl>, +p: String, +a: F.At, +post: List<&2, F.Cl>, +nl: {SS.af_live(k, pre) == False{} : Bool}) -> {F.set(k, a2, List.append(&2, F.Cl, pre, F.Cl{k, p, a} <> post)) == List.append(&2, F.Cl, pre, F.Cl{k, p, a2} <> post) : List<&2, F.Cl>}:
  match pre:
    case Nil{}:
      %fr.self(k) : {F.set.at(_, F.Cl{k, p, a}, a2, post, F.set(k, a2, post)) == F.Cl{k, p, a2} <> post : List<&2, F.Cl>}
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +q, +b}:
          %fr.not(j, k, fr.or_f1(Nat.is_eq(j, k), SS.af_live(k, t), nl)) : {F.set.at(_, F.Cl{j, q, b}, a2, List.append(&2, F.Cl, t, F.Cl{k, p, a} <> post), F.set(k, a2, List.append(&2, F.Cl, t, F.Cl{k, p, a} <> post))) == F.Cl{j, q, b} <> List.append(&2, F.Cl, t, F.Cl{k, p, a2} <> post) : List<&2, F.Cl>}
          fr.cons(F.Cl, F.Cl{j, q, b}, F.set(k, a2, List.append(&2, F.Cl, t, F.Cl{k, p, a} <> post)), List.append(&2, F.Cl, t, F.Cl{k, p, a2} <> post), fr.set(k, a2, t, p, a, post, fr.or_f2(Nat.is_eq(j, k), SS.af_live(k, t), nl)))

def fr.unwait_at(b: Bool, +x: F.Cl, -r1: List<&2, F.Cl>, -r2: List<&2, F.Cl>, ih: {r1 == r2 : List<&2, F.Cl>}) -> {F.unwait.at(b, x, r1) == DL.af_keep(Bool.not(b), x, r2) : List<&2, F.Cl>}:
  match b:
    case True{}:
      ih
    case False{}:
      fr.cons(F.Cl, x, r1, r2, ih)

# the callers waiting on p's flight leave: the others stay, in order
def fr.unwait(+p: String, cs: List<&2, F.Cl>) -> {F.unwait(p, cs) == DL.af_others(p, cs) : List<&2, F.Cl>}:
  match cs:
    case Nil{}:
      {==}
    case +x <> t:
      %LAE.ae.waits(p, x) : {F.unwait.at(F.waits(p, x), x, F.unwait(p, t)) == DL.af_keep(Bool.not(_), x, DL.af_others(p, t)) : List<&2, F.Cl>}
      fr.unwait_at(F.waits(p, x), x, F.unwait(p, t), DL.af_others(p, t), fr.unwait(p, t))

def fr.wake_at(b: Bool, x: F.Cl, +a: F.Act, -r1: List<&2, F.To>, -ws: List<&2, F.Cl>, ih: {r1 == DL.af_tell(a, ws) : List<&2, F.To>}) -> {F.wake.at(b, x, a, r1) == DL.af_tell(a, DL.af_keep(b, x, ws)) : List<&2, F.To>}:
  match b:
    case True{}:
      match x:
        case F.Cl{+j, q, o}:
          Equal.cong(List<&2, F.To>, List<&2, F.To>, r => F.To{j, a} <> r, r1, DL.af_tell(a, ws), ih)
    case False{}:
      ih

# each caller waiting on p's flight, in order, is told a
def fr.wake(+p: String, +a: F.Act, cs: List<&2, F.Cl>) -> {F.wake(p, a, cs) == DL.af_tell(a, DL.af_waiters(p, cs)) : List<&2, F.To>}:
  match cs:
    case Nil{}:
      {==}
    case +x <> t:
      %LAE.ae.waits(p, x) : {F.wake.at(F.waits(p, x), x, a, F.wake(p, a, t)) == DL.af_tell(a, DL.af_keep(_, x, DL.af_waiters(p, t))) : List<&2, F.To>}
      fr.wake_at(F.waits(p, x), x, a, F.wake(p, a, t), DL.af_waiters(p, t), fr.wake(p, a, t))

def fr.joined_at(b: Bool, x: F.Cl, -r: Nat, -ws: List<&2, F.Cl>, ih: {r == List.length(&2, F.Cl, ws) : Nat}) -> {F.joined.at(b, r) == List.length(&2, F.Cl, DL.af_keep(b, x, ws)) : Nat}:
  match b:
    case True{}:
      Equal.cong(Nat, Nat, n => 1n+n, r, List.length(&2, F.Cl, ws), ih)
    case False{}:
      ih

# the joiner count is how many wait on p's flight
def fr.joined(+p: String, cs: List<&2, F.Cl>) -> {F.joined(p, cs) == List.length(&2, F.Cl, DL.af_waiters(p, cs)) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case +x <> t:
      %LAE.ae.waits(p, x) : {F.joined.at(F.waits(p, x), F.joined(p, t)) == List.length(&2, F.Cl, DL.af_keep(_, x, DL.af_waiters(p, t))) : Nat}
      fr.joined_at(F.waits(p, x), x, F.joined(p, t), DL.af_waiters(p, t), fr.joined(p, t))
