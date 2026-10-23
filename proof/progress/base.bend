# eukhe: lemmas the proofs of area progress share

import Base
import ../../bend/progress.bend as Pr
import ../base/nat.bend as LNat

# ---- progress ----

# proof_progress: the progress laws (LAWS.bend section progress) of the model in
# bend/progress.bend.
#
# The ledger only adds an act it does not hold. So reading an act it holds
# changes nothing, every act read is held, and the ledger never shrinks.
# Reading acts the session did before keeps the work (`pp.repeat`);
# reading an act the session never did grows it (`pp.grows`). The goal's
# check sees no growth in a run of repeats, so the count of continuations
# with no new work grows by one at each, and the goal stops at the cap
# (`pp.stops`). The watch reads the same token at each poll of a looping
# child, so each poll is a quiet poll of bend/child.bend, and quiet polls
# end the watch in time (`pc.stalls_in_time`).
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters); a split on a computed test goes to a helper
# that takes the test as a parameter, with the recursive result passed in.

# Logic
# -----

def progress.pp.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pp.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : progress.pp.BD(_, Unit, A)
  Unit{}

def pp.or_true_r(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pp.or_ff_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      pp.absurdT({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pp.or_ff_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      pp.absurdT({b == False{} : Bool}, h)
    case False{}:
      h

# The ledger
# ----------

def pp.app_ledger(a: List<&2, Nat>, +b: List<&2, Nat>, +s: List<&2, Nat>) -> {Pr.ledger(List.append(&2, Nat, a, b), s) == Pr.ledger(b, Pr.ledger(a, s)) : List<&2, Nat>}:
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      pp.app_ledger(t, b, Pr.add(s, h))

# adding an act the ledger holds changes nothing
def pp.add_hit(+s: List<&2, Nat>, +x: Nat, m: {Pr.mem(x, s) == True{} : Bool}) -> {Pr.add(s, x) == s : List<&2, Nat>}:
  %Equal.sym(Bool, Pr.mem(x, s), True{}, m) : {Pr.add.put(_, x, s) == s : List<&2, Nat>}
  {==}

# every act of xs is held by s
def pp.Held(xs: List<&2, Nat>, +s: List<&2, Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case +h <> +t:
      {Pr.mem(h, s) == True{} : Bool} & pp.Held(t, s)

# reading acts the ledger holds changes nothing
def pp.ledger_held(xs: List<&2, Nat>, +s: List<&2, Nat>, held: pp.Held(xs, s)) -> {Pr.ledger(xs, s) == s : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      (m, rest) = held
      %Equal.sym(List<&2, Nat>, Pr.add(s, h), s, pp.add_hit(s, h, m)) : {Pr.ledger(t, _) == s : List<&2, Nat>}
      pp.ledger_held(t, s, rest)

def pp.mem_put(b: Bool, +s: List<&2, Nat>, +x: Nat, +y: Nat, m: {Pr.mem(y, s) == True{} : Bool}) -> {Pr.mem(y, Pr.add.put(b, x, s)) == True{} : Bool}:
  match b:
    case True{}:
      m
    case False{}:
      %Equal.sym(Bool, Pr.mem(y, s), True{}, m) : {Bool.or(Nat.is_eq(x, y), _) == True{} : Bool}
      pp.or_true_r(Nat.is_eq(x, y))

# an act the ledger holds stays held after reading xs
def pp.mem_ledger(xs: List<&2, Nat>, +s: List<&2, Nat>, +y: Nat, m: {Pr.mem(y, s) == True{} : Bool}) -> {Pr.mem(y, Pr.ledger(xs, s)) == True{} : Bool}:
  match xs:
    case Nil{}:
      m
    case +h <> +t:
      pp.mem_ledger(t, Pr.add(s, h), y, pp.mem_put(Pr.mem(h, s), s, h, y, m))

def pp.mem_self.at(b: Bool, +s: List<&2, Nat>, +x: Nat, e: {Pr.mem(x, s) == b : Bool}) -> {Pr.mem(x, Pr.add.put(b, x, s)) == True{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, LNat.child.pc.eq_refl(x)) : {Bool.or(_, Pr.mem(x, s)) == True{} : Bool}
      {==}

# an act read is held
def pp.in_ledger(xs: List<&2, Nat>, +s: List<&2, Nat>, +x: Nat, i: Pr.In(x, xs)) -> {Pr.mem(x, Pr.ledger(xs, s)) == True{} : Bool}:
  match xs:
    case Nil{}:
      match i:
    case +h <> +t:
      match i:
        case Inl{eq}:
          %Equal.sym(Nat, x, h, eq) : {Pr.mem(_, Pr.ledger(t, Pr.add(s, h))) == True{} : Bool}
          pp.mem_ledger(t, Pr.add(s, h), h, pp.mem_self.at(Pr.mem(h, s), s, h, {==}))
        case Inr{it}:
          pp.in_ledger(t, Pr.add(s, h), x, it)

# the acts of a list within seen are held by the ledger of seen
def pp.held_of(xs: List<&2, Nat>, +seen: List<&2, Nat>, w: Pr.Within(xs, seen)) -> pp.Held(xs, Pr.ledger(seen, Nil{})):
  match xs:
    case Nil{}:
      Unit{}
    case +h <> +t:
      (i, rest) = w
      (pp.in_ledger(seen, Nil{}, h, i), pp.held_of(t, seen, rest))

# reading again acts the session did before keeps its work
def pp.repeat(+seen: List<&2, Nat>, +loop: List<&2, Nat>, w: Pr.Within(loop, seen)) -> {Pr.work(List.append(&2, Nat, seen, loop)) == Pr.work(seen) : Nat}:
  +l = Pr.ledger(seen, Nil{})
  %Equal.sym(List<&2, Nat>, Pr.ledger(List.append(&2, Nat, seen, loop), Nil{}), Pr.ledger(loop, l), pp.app_ledger(seen, loop, Nil{})) : {List.length(&2, Nat, _) == List.length(&2, Nat, l) : Nat}
  %Equal.sym(List<&2, Nat>, Pr.ledger(loop, l), l, pp.ledger_held(loop, l, pp.held_of(loop, seen, w))) : {List.length(&2, Nat, _) == List.length(&2, Nat, l) : Nat}
  {==}

# Growth
# ------

def pp.len_put(b: Bool, +s: List<&2, Nat>, +x: Nat) -> {Nat.is_le(List.length(&2, Nat, s), List.length(&2, Nat, Pr.add.put(b, x, s))) == True{} : Bool}:
  match b:
    case True{}:
      LNat.child.pc.le_refl(List.length(&2, Nat, s))
    case False{}:
      LNat.pc.le_succ(List.length(&2, Nat, s), List.length(&2, Nat, s), LNat.child.pc.le_refl(List.length(&2, Nat, s)))

# the ledger never shrinks
def pp.len_ledger(xs: List<&2, Nat>, +s: List<&2, Nat>) -> {Nat.is_le(List.length(&2, Nat, s), List.length(&2, Nat, Pr.ledger(xs, s))) == True{} : Bool}:
  match xs:
    case Nil{}:
      LNat.child.pc.le_refl(List.length(&2, Nat, s))
    case +h <> +t:
      +a = Pr.add(s, h)
      LNat.child.pc.le_trans(List.length(&2, Nat, s), List.length(&2, Nat, a), List.length(&2, Nat, Pr.ledger(t, a)), pp.len_put(Pr.mem(h, s), s, h), pp.len_ledger(t, a))

# x is held by s, or reading xs grows the ledger past s
def pp.Grown(+x: Nat, +s: List<&2, Nat>, +r: List<&2, Nat>) -> Type:
  Or({Pr.mem(x, s) == True{} : Bool}, {Nat.is_le(1n+List.length(&2, Nat, s), List.length(&2, Nat, r)) == True{} : Bool})

# x is the act h read now: held before, or new and so the ledger grows
def pp.grown_now.at(b: Bool, +x: Nat, +s: List<&2, Nat>, +r: List<&2, Nat>, e: {Pr.mem(x, s) == b : Bool}, le: {Nat.is_le(List.length(&2, Nat, Pr.add.put(b, x, s)), List.length(&2, Nat, r)) == True{} : Bool}) -> pp.Grown(x, s, r):
  match b:
    case True{}:
      Inl{e}
    case False{}:
      Inr{le}

# x was held by the ledger after h; then it was held before, or it is h
def pp.grown_was.eq(c: Bool, +x: Nat, +h: Nat, +s: List<&2, Nat>, +r: List<&2, Nat>, e: {Nat.is_eq(h, x) == c : Bool}, m: {Bool.or(c, Pr.mem(x, s)) == True{} : Bool}, le: {Nat.is_le(List.length(&2, Nat, h <> s), List.length(&2, Nat, r)) == True{} : Bool}) -> pp.Grown(x, s, r):
  match c:
    case True{}:
      Inr{le}
    case False{}:
      Inl{m}

def pp.grown_was.at(b: Bool, +x: Nat, +h: Nat, +s: List<&2, Nat>, +r: List<&2, Nat>, m: {Pr.mem(x, Pr.add.put(b, h, s)) == True{} : Bool}, le: {Nat.is_le(List.length(&2, Nat, Pr.add.put(b, h, s)), List.length(&2, Nat, r)) == True{} : Bool}) -> pp.Grown(x, s, r):
  match b:
    case True{}:
      Inl{m}
    case False{}:
      pp.grown_was.eq(Nat.is_eq(h, x), x, h, s, r, {==}, m, le)

# the ledger after h grew past r, so past s
def pp.grown_past(+x: Nat, +s: List<&2, Nat>, +a: List<&2, Nat>, +r: List<&2, Nat>, sa: {Nat.is_le(List.length(&2, Nat, s), List.length(&2, Nat, a)) == True{} : Bool}, g: pp.Grown(x, a, r), back: {Pr.mem(x, a) == True{} : Bool} -> pp.Grown(x, s, r)) -> pp.Grown(x, s, r):
  match g:
    case Inl{m}:
      back(m)
    case Inr{le}:
      Inr{LNat.child.pc.le_trans(1n+List.length(&2, Nat, s), 1n+List.length(&2, Nat, a), List.length(&2, Nat, r), sa, le)}

# an act x of xs is held by s, or reading xs grows the ledger past s
def pp.grows(xs: List<&2, Nat>, +s: List<&2, Nat>, +x: Nat, i: Pr.In(x, xs)) -> pp.Grown(x, s, Pr.ledger(xs, s)):
  match xs:
    case Nil{}:
      match i:
    case +h <> +t:
      match i:
        case Inl{eq}:
          %Equal.sym(Nat, x, h, eq) : pp.Grown(_, s, Pr.ledger(t, Pr.add(s, h)))
          pp.grown_now.at(Pr.mem(h, s), h, s, Pr.ledger(t, Pr.add(s, h)), {==}, pp.len_ledger(t, Pr.add(s, h)))
        case Inr{it}:
          pp.grown_past(x, s, Pr.add(s, h), Pr.ledger(t, Pr.add(s, h)), pp.len_put(Pr.mem(h, s), s, h), pp.grows(t, Pr.add(s, h), x, it), m => pp.grown_was.at(Pr.mem(h, s), x, h, s, Pr.ledger(t, Pr.add(s, h)), m, pp.len_ledger(t, Pr.add(s, h))))

# a grown ledger past a ledger that does not hold x
def pp.grown_fresh(+x: Nat, +s: List<&2, Nat>, +r: List<&2, Nat>, fresh: {Pr.mem(x, s) == False{} : Bool}, g: pp.Grown(x, s, r)) -> {Nat.is_le(1n+List.length(&2, Nat, s), List.length(&2, Nat, r)) == True{} : Bool}:
  match g:
    case Inl{m}:
      pp.absurdT({Nat.is_le(1n+List.length(&2, Nat, s), List.length(&2, Nat, r)) == True{} : Bool}, Equal.trans(Bool, True{}, Pr.mem(x, s), False{}, Equal.sym(Bool, Pr.mem(x, s), True{}, m), fresh))
    case Inr{le}:
      le

# an act of seg that seen does not hold grows the work
def pp.more(+seen: List<&2, Nat>, +seg: List<&2, Nat>, +x: Nat, fresh: {Pr.mem(x, Pr.ledger(seen, Nil{})) == False{} : Bool}, i: Pr.In(x, seg)) -> {Nat.is_le(1n+Pr.work(seen), Pr.work(List.append(&2, Nat, seen, seg))) == True{} : Bool}:
  +l = Pr.ledger(seen, Nil{})
  %Equal.sym(List<&2, Nat>, Pr.ledger(List.append(&2, Nat, seen, seg), Nil{}), Pr.ledger(seg, l), pp.app_ledger(seen, seg, Nil{})) : {Nat.is_le(1n+List.length(&2, Nat, l), List.length(&2, Nat, _)) == True{} : Bool}
  pp.grown_fresh(x, l, Pr.ledger(seg, l), fresh, pp.grows(seg, l, x, i))

# a fresh act is not held by the ledger
def pp.nmem_put(b: Bool, +s: List<&2, Nat>, +h: Nat, +x: Nat, ne: {Nat.is_eq(h, x) == False{} : Bool}, m: {Pr.mem(x, s) == False{} : Bool}) -> {Pr.mem(x, Pr.add.put(b, h, s)) == False{} : Bool}:
  match b:
    case True{}:
      m
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(h, x), False{}, ne) : {Bool.or(_, Pr.mem(x, s)) == False{} : Bool}
      m

def pp.nmem_ledger(xs: List<&2, Nat>, +s: List<&2, Nat>, +x: Nat, +n: {Pr.mem(x, xs) == False{} : Bool}, m: {Pr.mem(x, s) == False{} : Bool}) -> {Pr.mem(x, Pr.ledger(xs, s)) == False{} : Bool}:
  match xs:
    case Nil{}:
      m
    case +h <> +t:
      pp.nmem_ledger(t, Pr.add(s, h), x, pp.or_ff_r(Nat.is_eq(h, x), Pr.mem(x, t), n), pp.nmem_put(Pr.mem(h, s), s, h, x, pp.or_ff_l(Nat.is_eq(h, x), Pr.mem(x, t), n), m))

# an act of seg the session never did grows the work
def pp.new_work(+seen: List<&2, Nat>, +seg: List<&2, Nat>, +x: Nat, fresh: {Pr.mem(x, seen) == False{} : Bool}, i: Pr.In(x, seg)) -> {Nat.is_le(1n+Pr.work(seen), Pr.work(List.append(&2, Nat, seen, seg))) == True{} : Bool}:
  pp.more(seen, seg, x, pp.nmem_ledger(seen, Nil{}, x, fresh, {==}), i)

# Appending
# ---------

def pp.in_app(+x: Nat, xs: List<&2, Nat>, +more: List<&2, Nat>, i: Pr.In(x, xs)) -> Pr.In(x, List.append(&2, Nat, xs, more)):
  match xs:
    case Nil{}:
      match i:
    case +h <> +t:
      match i:
        case Inl{eq}:
          Inl{eq}
        case Inr{it}:
          Inr{pp.in_app(x, t, more, it)}

def pp.within_app(xs: List<&2, Nat>, +hist: List<&2, Nat>, +more: List<&2, Nat>, w: Pr.Within(xs, hist)) -> Pr.Within(xs, List.append(&2, Nat, hist, more)):
  match xs:
    case Nil{}:
      Unit{}
    case +h <> +t:
      (i, rest) = w
      (pp.in_app(h, hist, more, i), pp.within_app(t, hist, more, rest))

# The check the Rust goal loop runs (`judge`): below t it is the check on
# the counts, the counts grow exactly when `grew`, and the count is held.

def pp.le0_eq(t: Nat) -> {True{} == Nat.is_le(0n, t) : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

# a < b is 1 + a <= b
def pp.lt_is_le(a: Nat, b: Nat) -> {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      %pp.le0_eq(bp) : {True{} == _ : Bool}
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      pp.lt_is_le(ap, bp)
