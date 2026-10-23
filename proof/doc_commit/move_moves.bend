# eukhe: the proof of LAW move_moves

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def pc.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LA.documents.pc.absurd({0n == 1n+q : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 0n:
      LA.documents.pc.absurd({1n+p == 0n : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+q:
      %pc.eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def documents.pc.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      documents.pc.eq_refl(p)

def pc.or_false_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LA.documents.pc.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def documents.pc.or_false_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LA.documents.pc.absurd({b == False{} : Bool}, h)
    case False{}:
      h

# a free name is not the name of a file that is there
def pc.ne.go(+t: Nat, +s: Nat, -es: List<&2, Cm.Entry>, b: Bool, eb: {Nat.is_eq(t, s) == b : Bool}, free: {Cm.has(t, es) == False{} : Bool}, from: {Cm.has(s, es) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      same = {Equal.cong(Nat, Bool, y => Cm.has(y, es), s, t, Equal.sym(Nat, t, s, pc.eq_true(t, s, eb))) : {Cm.has(s, es) == Cm.has(t, es) : Bool}}
      Equal.trans(Bool, True{}, Cm.has(s, es), False{}, Equal.sym(Bool, Cm.has(s, es), True{}, from), Equal.trans(Bool, Cm.has(s, es), Cm.has(t, es), False{}, same, free))
    case False{}:
      {==}

def pc.gone.put(+s: Nat, +t: Nat, +m: Nat, g: Nat, -r: List<&2, Cm.Entry>, b: Bool, eb: {Nat.is_eq(m, s) == b : Bool}, ne: {Nat.is_eq(t, s) == False{} : Bool}, ih: {Cm.has(s, r) == False{} : Bool}) -> {Cm.has(s, Cm.rename.put(t, m, g, r, b)) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(t, s), False{}, ne) : {Bool.or(_, Cm.has(s, r)) == False{} : Bool}
      ih
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(m, s), False{}, eb) : {Bool.or(_, Cm.has(s, r)) == False{} : Bool}
      ih

# after the move no file has the source name
def pc.gone(+s: Nat, +t: Nat, es: List<&2, Cm.Entry>, +ne: {Nat.is_eq(t, s) == False{} : Bool}) -> {Cm.has(s, Cm.rename(s, t, es)) == False{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cm.Entry{+m, g}:
          pc.gone.put(s, t, m, g, Cm.rename(s, t, rest), Nat.is_eq(m, s), {==}, ne, pc.gone(s, t, rest, ne))

def pc.lands.put(+s: Nat, +t: Nat, +m: Nat, +g: Nat, -r: List<&2, Cm.Entry>, -rest: List<&2, Cm.Entry>, b: Bool, hm: {Nat.is_eq(m, t) == False{} : Bool}, ih: {Cm.get(t, r) == Cm.get(s, rest) : Maybe<&2, Nat>}) -> {Cm.get(t, Cm.rename.put(t, m, g, r, b)) == Cm.get.put(b, g, Cm.get(s, rest)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(t, t), True{}, documents.pc.eq_refl(t)) : {Cm.get.put(_, g, Cm.get(t, r)) == Some{g} : Maybe<&2, Nat>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(m, t), False{}, hm) : {Cm.get.put(_, g, Cm.get(t, r)) == Cm.get(s, rest) : Maybe<&2, Nat>}
      ih

# after the move the destination holds what the source held
def pc.lands(+s: Nat, +t: Nat, es: List<&2, Cm.Entry>, +free: {Cm.has(t, es) == False{} : Bool}) -> {Cm.get(t, Cm.rename(s, t, es)) == Cm.get(s, es) : Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cm.Entry{+m, +g}:
          pc.lands.put(s, t, m, g, Cm.rename(s, t, rest), rest, Nat.is_eq(m, s), pc.or_false_l(Nat.is_eq(m, t), Cm.has(t, rest), free), pc.lands(s, t, rest, documents.pc.or_false_r(Nat.is_eq(m, t), Cm.has(t, rest), free)))

# the law move_moves
def pc.move_moves(+s: Nat, +t: Nat, +es: List<&2, Cm.Entry>, +free: {Cm.has(t, es) == False{} : Bool}, +from: {Cm.has(s, es) == True{} : Bool}) -> {Cm.Mv.ok(Cm.move(s, t, es)) == True{} : Bool} & {Cm.has(s, Cm.Mv.es(Cm.move(s, t, es))) == False{} : Bool} & {Cm.get(t, Cm.Mv.es(Cm.move(s, t, es))) == Cm.get(s, es) : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Cm.has(t, es), False{}, free) : {Cm.Mv.ok(Cm.move.go(s, t, _, es)) == True{} : Bool} & {Cm.has(s, Cm.Mv.es(Cm.move.go(s, t, _, es))) == False{} : Bool} & {Cm.get(t, Cm.Mv.es(Cm.move.go(s, t, _, es))) == Cm.get(s, es) : Maybe<&2, Nat>}
  ({==}, (pc.gone(s, t, es, pc.ne.go(t, s, es, Nat.is_eq(t, s), {==}, free, from)), pc.lands(s, t, es, free)))

def DocCommit.move_moves(s, t, es, free, from):
  pc.move_moves(s, t, es, free, from)
