# eukhe: lemmas the proofs of area once share
#
# Logic: a refuted premise proves anything; modus ponens and the parts of
# a conjunction over Bool. The life: an end absorbs every record
# (ob.go_ran, ob.go_lost, ob.go_void); from a pending or a running effect
# the fold tells the spec's life (ob.go_pending, ob.go_run); the fold
# runs through an append (ob.go_append). The restart: a keyed effect is
# sent again exactly while fewer than cap (ob.keyed), and its verdict is
# a launch or an interrupt (ob.keyed_cases).

import Base
import ../../bend/once.bend as O
import ../../spec/once/life.bend as S

# Logic
# -----

def ob.TF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

def ob.FT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# a premise True == False proves anything
def ob.true_false(-G: Type, h: {True{} == False{} : Bool}) -> G:
  %h : ob.TF(_, G)
  Unit{}

# a premise False == True proves anything
def ob.false_true(-G: Type, h: {False{} == True{} : Bool}) -> G:
  %h : ob.FT(_, G)
  Unit{}

# from a, and a implies b, b
def ob.mp(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hab: {Bool.or(Bool.not(a), b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      hab
    case False{}:
      ob.false_true({b == True{} : Bool}, ha)

# the first part of a conjunction
def ob.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# the second part of a conjunction
def ob.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      ob.false_true({b == True{} : Bool}, h)

# a implies a
def ob.self(a: Bool) -> {Bool.or(Bool.not(a), a) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ob.MD(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some
def ob.none_some(-A: Data, -G: Type, -r: A, h: {None{} == Some{r} : Maybe<&2, A>}) -> G:
  %h : ob.MD(A, _, G)
  Unit{}

def ob.get(-A: Data, m: Maybe<&2, A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is injective
def ob.some_inj(-A: Data, +a: A, +b: A, h: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => ob.get(A, m, a), Some{a}, Some{b}, h)

# x or true
def ob.or_true(x: Bool) -> {Bool.or(x, True{}) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# Numbers
# -------

# a number that is_eq says is 0 is 0
def ob.eq_zero(a: Nat, h: {Nat.is_eq(a, 0n) == True{} : Bool}) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      ob.false_true({1n+p == 0n : Nat}, h)

# 1 is at most 1 + c
def ob.le_one(c: Nat) -> {Nat.is_le(1n, 1n+c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+q:
      {==}

def ob.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ob.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def ob.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ob.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# The life
# --------

# an end absorbs every record
def ob.go_ran(j: List<&2, O.Rec>) -> {O.life.go(j, O.Ran{}) == O.Ran{} : O.Life}:
  match j:
    case Nil{}:
      {==}
    case r <> t:
      ob.go_ran(t)

def ob.go_lost(j: List<&2, O.Rec>) -> {O.life.go(j, O.Unsure{}) == O.Unsure{} : O.Life}:
  match j:
    case Nil{}:
      {==}
    case r <> t:
      ob.go_lost(t)

def ob.go_void(j: List<&2, O.Rec>) -> {O.life.go(j, O.Void{}) == O.Void{} : O.Life}:
  match j:
    case Nil{}:
      {==}
    case r <> t:
      ob.go_void(t)

# from an effect launched 1 + n times, the fold tells the spec's life:
# the first end, else running with the later launches added
def ob.go_run(j: List<&2, O.Rec>, +n: Nat, -b: Bool) -> {O.life.go(j, O.Running{n}) == S.life_spec.of(S.first_end(j), 1n+Nat.add(S.starts(j), n), b) : O.Life}:
  match j:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case O.Intended{}:
          ob.go_run(t, n, b)
        case O.Started{}:
          %ob.add_succ(S.starts(t), n) : {O.life.go(t, O.Running{1n+n}) == S.life_spec.of(S.first_end(t), 1n+_, b) : O.Life}
          ob.go_run(t, 1n+n, b)
        case O.Finished{}:
          ob.go_ran(t)
        case O.Unknown{}:
          ob.go_lost(t)
        case O.Unstarted{}:
          ob.go_void(t)

# from a first launch, the fold tells the spec's life
def ob.go_first(+t: List<&2, O.Rec>, -b: Bool) -> {O.life.go(t, O.Running{0n}) == S.life_spec.of(S.first_end(t), 1n+S.starts(t), b) : O.Life}:
  %ob.add_zero(S.starts(t)) : {O.life.go(t, O.Running{0n}) == S.life_spec.of(S.first_end(t), 1n+_, b) : O.Life}
  ob.go_run(t, 0n, b)

# from a pending effect, the fold tells the spec's life
def ob.go_pending(j: List<&2, O.Rec>) -> {O.life.go(j, O.Pending{}) == S.life_spec.of(S.first_end(j), S.starts(j), True{}) : O.Life}:
  match j:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case O.Intended{}:
          ob.go_pending(t)
        case O.Started{}:
          ob.go_first(t, True{})
        case O.Finished{}:
          ob.go_ran(t)
        case O.Unknown{}:
          ob.go_lost(t)
        case O.Unstarted{}:
          ob.go_void(t)

# the fold runs through an append
def ob.go_append(j: List<&2, O.Rec>, -rest: List<&2, O.Rec>, l: O.Life) -> {O.life.go(List.append(&2, O.Rec, j, rest), l) == O.life.go(rest, O.life.go(j, l)) : O.Life}:
  match j:
    case Nil{}:
      {==}
    case r <> t:
      ob.go_append(t, rest, O.life.step(l, r))

# one more record after j steps the life j tells
def ob.go_snoc(j: List<&2, O.Rec>, -r: O.Rec) -> {O.life(List.append(&2, O.Rec, j, [r])) == O.life.step(O.life(j), r) : O.Life}:
  ob.go_append(j, [r], O.Absent{})

# an ended life absorbs every record
def ob.stays(x: O.Life, rest: List<&2, O.Rec>, e: {S.settled(x) == True{} : Bool}) -> {O.life.go(rest, x) == x : O.Life}:
  match x:
    case O.Absent{}:
      ob.false_true({O.life.go(rest, O.Absent{}) == O.Absent{} : O.Life}, e)
    case O.Pending{}:
      ob.false_true({O.life.go(rest, O.Pending{}) == O.Pending{} : O.Life}, e)
    case O.Running{again}:
      ob.false_true({O.life.go(rest, O.Running{again}) == O.Running{again} : O.Life}, e)
    case O.Ran{}:
      ob.go_ran(rest)
    case O.Unsure{}:
      ob.go_lost(rest)
    case O.Void{}:
      ob.go_void(rest)

# The restart
# -----------

# a keyed effect is sent again exactly while fewer than cap
def ob.keyed(cap: Nat, again: Nat) -> {O.keyed(cap, again) == S.more_spec(Nat.is_lt(again, cap)) : O.Verdict}:
  match cap:
    case 0n:
      match again:
        case 0n:
          {==}
        case 1n+a:
          {==}
    case 1n+c:
      match again:
        case 0n:
          {==}
        case 1n+a:
          ob.keyed(c, a)

# what holds of a launch and of an interrupt holds of a keyed effect's
# verdict
def ob.keyed_cases(cap: Nat, again: Nat, -P: O.Verdict -> Type, launch: P(O.Launch{}), interrupt: P(O.Interrupt{})) -> P(O.keyed(cap, again)):
  match cap:
    case 0n:
      interrupt
    case 1n+c:
      match again:
        case 0n:
          launch
        case 1n+a:
          ob.keyed_cases(c, a, P, launch, interrupt)

# what holds of a launch made within the cap and of an interrupt holds
# of a keyed effect's verdict
def ob.keyed_within(cap: Nat, again: Nat, -P: O.Verdict -> Type, launch: {Nat.is_le(1n+again, cap) == True{} : Bool} -> P(O.Launch{}), interrupt: P(O.Interrupt{})) -> P(O.keyed(cap, again)):
  match cap:
    case 0n:
      interrupt
    case 1n+c:
      match again:
        case 0n:
          launch(ob.le_one(c))
        case 1n+a:
          ob.keyed_within(c, a, P, launch, interrupt)
