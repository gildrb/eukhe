# proof_progress: the progress laws (laws/progress.bend) of the model in
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

import Base
import ./child.bend as C
import ./progress.bend as Pr
import ./proof_child.bend as Children

# Logic
# -----

def pp.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pp.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pp.BD(_, Unit, A)
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

# Numbers
# -------

def pp.lt_self(+n: Nat) -> {Nat.is_le(1n+n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pp.lt_self(p)

def pp.add_zero(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 0n), p, pp.add_zero(p)) : {1n+_ == 1n+p : Nat}
      {==}

def pp.add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), pp.add_succ(p, b)) : {1n+_ == 2n+Nat.add(p, b) : Nat}
      {==}

# b is not a: a test that sees b at least 1 above a sees them differ
def pp.ne.at(c: Bool, +a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == c : Bool}, lt: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Bool.not(c) == True{} : Bool}:
  match c:
    case True{}:
      Children.pc.lt_ne({Bool.not(True{}) == True{} : Bool}, a, b, lt, e)
    case False{}:
      {==}

def pp.ne(+a: Nat, +b: Nat, lt: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Bool.not(Nat.is_eq(a, b)) == True{} : Bool}:
  pp.ne.at(Nat.is_eq(a, b), a, b, {==}, lt)

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

# adding an act the ledger does not hold puts it in front
def pp.add_new(+s: List<&2, Nat>, +x: Nat, m: {Pr.mem(x, s) == False{} : Bool}) -> {Pr.add(s, x) == x <> s : List<&2, Nat>}:
  %Equal.sym(Bool, Pr.mem(x, s), False{}, m) : {Pr.add.put(_, x, s) == x <> s : List<&2, Nat>}
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
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, Children.pc.eq_refl(x)) : {Bool.or(_, Pr.mem(x, s)) == True{} : Bool}
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
      Children.pc.le_refl(List.length(&2, Nat, s))
    case False{}:
      Children.pc.le_succ(List.length(&2, Nat, s), List.length(&2, Nat, s), Children.pc.le_refl(List.length(&2, Nat, s)))

# the ledger never shrinks
def pp.len_ledger(xs: List<&2, Nat>, +s: List<&2, Nat>) -> {Nat.is_le(List.length(&2, Nat, s), List.length(&2, Nat, Pr.ledger(xs, s))) == True{} : Bool}:
  match xs:
    case Nil{}:
      Children.pc.le_refl(List.length(&2, Nat, s))
    case +h <> +t:
      +a = Pr.add(s, h)
      Children.pc.le_trans(List.length(&2, Nat, s), List.length(&2, Nat, a), List.length(&2, Nat, Pr.ledger(t, a)), pp.len_put(Pr.mem(h, s), s, h), pp.len_ledger(t, a))

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
      Inr{Children.pc.le_trans(1n+List.length(&2, Nat, s), 1n+List.length(&2, Nat, a), List.length(&2, Nat, r), sa, le)}

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

def pp.repeats_app(segs: List<&2, List<&2, Nat>>, +hist: List<&2, Nat>, +more: List<&2, Nat>, r: Pr.Repeats(segs, hist)) -> Pr.Repeats(segs, List.append(&2, Nat, hist, more)):
  match segs:
    case Nil{}:
      Unit{}
    case +seg <> +rest:
      (w, rr) = r
      (pp.within_app(seg, hist, more, w), pp.repeats_app(rest, hist, more, rr))

def pp.loops_app(ps: List<&2, Pr.Peek>, +hist: List<&2, Nat>, +more: List<&2, Nat>, l: Pr.Loops(ps, hist)) -> Pr.Loops(ps, List.append(&2, Nat, hist, more)):
  match ps:
    case Nil{}:
      Unit{}
    case p <> +rest:
      match p:
        case Pr.Peek{+seg, +dt}:
          (w, lr) = l
          (pp.within_app(seg, hist, more, w), pp.loops_app(rest, hist, more, lr))

# The goal's progress check
# -------------------------

# a run of repeats does not grow the work
def pp.grew_no(+hist: List<&2, Nat>, +seg: List<&2, Nat>, w: Pr.Within(seg, hist)) -> {Pr.grew(hist, seg) == False{} : Bool}:
  %Equal.sym(Nat, Pr.work(List.append(&2, Nat, hist, seg)), Pr.work(hist), pp.repeat(hist, seg, w)) : {Nat.is_le(1n+Pr.work(hist), _) == False{} : Bool}
  pp.lt_self(Pr.work(hist))

# new work clears the count
def pp.grew_yes(+cap: Nat, +s: Nat, +hist: List<&2, Nat>, +seg: List<&2, Nat>, +x: Nat, fresh: {Pr.mem(x, hist) == False{} : Bool}, i: Pr.In(x, seg)) -> {Pr.check(cap, s, Pr.grew(hist, seg)) == Pr.Go{0n} : Pr.Goal}:
  %Equal.sym(Bool, Pr.grew(hist, seg), True{}, pp.new_work(hist, seg, x, fresh, i)) : {Pr.check(cap, s, _) == Pr.Go{0n} : Pr.Goal}
  {==}

# the last check: the stalls reach the cap, so the goal stops
def pp.last.at(b: Bool, +cap: Nat, +s: Nat, +h: List<&2, Nat>, e: {Nat.is_le(cap, 1n+s) == b : Bool}, long: {Nat.is_le(cap, 1n+s) == True{} : Bool}) -> {Pr.Goal.stopped(Pr.goal(Nil{}, cap, h, Pr.strike.put(b, 1n+s))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      pp.absurdT({Pr.Goal.stopped(Pr.goal(Nil{}, cap, h, Pr.Go{1n+s})) == True{} : Bool}, Equal.trans(Bool, True{}, Nat.is_le(cap, 1n+s), False{}, Equal.sym(Bool, Nat.is_le(cap, 1n+s), True{}, long), e))

# a check before the last: the goal stops now, or the next checks stop it
def pp.next.at(b: Bool, +cap: Nat, +s: Nat, +h: List<&2, Nat>, +seg: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, ih: {Pr.Goal.stopped(Pr.goal(seg <> rest, cap, h, Pr.Go{1n+s})) == True{} : Bool}) -> {Pr.Goal.stopped(Pr.goal(seg <> rest, cap, h, Pr.strike.put(b, 1n+s))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the bound at the last check
def pp.long_last(+cap: Nat, +s: Nat, long: {Nat.is_le(cap, Nat.add(1n+s, 0n)) == True{} : Bool}) -> {Nat.is_le(cap, 1n+s) == True{} : Bool}:
  %pp.add_zero(1n+s) : {Nat.is_le(cap, _) == True{} : Bool}
  long

# the bound after one more check
def pp.long_next(+cap: Nat, +s: Nat, +l: Nat, long: {Nat.is_le(cap, Nat.add(1n+s, 1n+l)) == True{} : Bool}) -> {Nat.is_le(cap, Nat.add(2n+s, l)) == True{} : Bool}:
  %pp.add_succ(s, l) : {Nat.is_le(cap, 1n+_) == True{} : Bool}
  long

# from Go{s}, checks of repeats stop the goal once s + their number
# reaches the cap
def pp.stops(rest: List<&2, List<&2, Nat>>, +seg: List<&2, Nat>, +cap: Nat, +s: Nat, +hist: List<&2, Nat>, r: Pr.Repeats(seg <> rest, hist), long: {Nat.is_le(cap, Nat.add(1n+s, List.length(&2, List<&2, Nat>, rest))) == True{} : Bool}) -> {Pr.Goal.stopped(Pr.goal(seg <> rest, cap, hist, Pr.Go{s})) == True{} : Bool}:
  match rest:
    case Nil{}:
      (w, rr) = r
      %Equal.sym(Bool, Pr.grew(hist, seg), False{}, pp.grew_no(hist, seg, w)) : {Pr.Goal.stopped(Pr.goal(Nil{}, cap, List.append(&2, Nat, hist, seg), Pr.check(cap, s, _))) == True{} : Bool}
      pp.last.at(Nat.is_le(cap, 1n+s), cap, s, List.append(&2, Nat, hist, seg), {==}, pp.long_last(cap, s, long))
    case +seg2 <> +rest2:
      (w, rr) = r
      +h = List.append(&2, Nat, hist, seg)
      %Equal.sym(Bool, Pr.grew(hist, seg), False{}, pp.grew_no(hist, seg, w)) : {Pr.Goal.stopped(Pr.goal(seg2 <> rest2, cap, h, Pr.check(cap, s, _))) == True{} : Bool}
      pp.next.at(Nat.is_le(cap, 1n+s), cap, s, h, seg2, rest2, pp.stops(rest2, seg2, cap, 1n+s, h, pp.repeats_app(seg2 <> rest2, hist, seg, rr), pp.long_next(cap, s, List.length(&2, List<&2, Nat>, rest2), long)))

def pp.goal_stops(+cap: Nat, +s: Nat, +hist: List<&2, Nat>, +seg: List<&2, Nat>, +segs: List<&2, List<&2, Nat>>, r: Pr.Repeats(seg <> segs, hist), long: {Nat.is_le(cap, List.length(&2, List<&2, Nat>, seg <> segs)) == True{} : Bool}) -> {Pr.Goal.stopped(Pr.goal(seg <> segs, cap, hist, Pr.Go{s})) == True{} : Bool}:
  +l = List.length(&2, List<&2, Nat>, segs)
  pp.stops(segs, seg, cap, s, hist, r, Children.pc.le_trans(cap, 1n+l, Nat.add(1n+s, l), long, Children.pc.le_add(s, l)))

# The subagent watch
# ------------------

# the quiet polls a list of polls is, for bend/child.bend
def pp.sames(ps: List<&2, Pr.Peek>) -> List<&2, C.Hush>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> +rest:
      match p:
        case Pr.Peek{seg, dt}:
          C.Same{dt} <> pp.sames(rest)

def pp.len_sames(ps: List<&2, Pr.Peek>) -> {List.length(&2, C.Hush, pp.sames(ps)) == List.length(&2, Pr.Peek, ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case p <> +rest:
      match p:
        case Pr.Peek{seg, dt}:
          %Equal.sym(Nat, List.length(&2, C.Hush, pp.sames(rest)), List.length(&2, Pr.Peek, rest), pp.len_sames(rest)) : {1n+_ == 1n+List.length(&2, Pr.Peek, rest) : Nat}
          {==}

# a watching verdict holds token t
def pp.Keep(x: C.Next, +t: Maybe<&2, Nat>) -> Data:
  match x:
    case C.Watch{w}:
      {C.W.tok(w) == t : Maybe<&2, Nat>}
    case C.Owe{k}:
      Unit
    case C.Quiet{}:
      Unit

def pp.spend_keeps(r: Nat, +tok: Maybe<&2, Nat>, +n: Nat) -> pp.Keep(C.spend(r, tok, n), tok):
  match r:
    case 0n:
      Unit{}
    case 1n+p:
      {==}

# a poll that reads the token the watch holds keeps it
def pp.same_keeps(+cfg: C.Cfg, w: C.W, +e: Nat) -> pp.Keep(C.look(cfg, w, e, C.Busy{C.W.tok(w)}), C.W.tok(w)):
  match w:
    case C.W{+tok, +l, +n}:
      %Children.pc.moved_self(tok) : pp.Keep(C.busy(_, cfg, C.W{tok, l, n}, tok, e), tok)
      pp.spend_keeps(Nat.sub(l, e), tok, C.Cfg.fails(cfg))

def pp.keep_eq(x: C.Next, +a: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, e: {a == b : Maybe<&2, Nat>}, k: pp.Keep(x, a)) -> pp.Keep(x, b):
  %e : pp.Keep(x, _)
  k

# the watch over the polls of a looping child is the watch over quiet polls
def pp.watch_hush(ps: List<&2, Pr.Peek>, +cfg: C.Cfg, +hist: List<&2, Nat>, x: C.Next, l: Pr.Loops(ps, hist), +inv: pp.Keep(x, Some{Pr.work(hist)})) -> {Pr.watch(ps, cfg, hist, x) == C.hush(pp.sames(ps), cfg, x) : C.Next}:
  match ps:
    case Nil{}:
      {==}
    case p <> +rest:
      match p:
        case Pr.Peek{+seg, +dt}:
          match x:
            case C.Watch{+v}:
              (w, lr) = l
              +h = List.append(&2, Nat, hist, seg)
              +same = pp.repeat(hist, seg, w)
              %Equal.sym(Nat, Pr.work(h), Pr.work(hist), same) : {Pr.watch(rest, cfg, h, C.look(cfg, v, 1n+dt, C.Busy{Some{_}})) == C.hush(pp.sames(rest), cfg, C.look(cfg, v, 1n+dt, C.Busy{C.W.tok(v)})) : C.Next}
              %inv : {Pr.watch(rest, cfg, h, C.look(cfg, v, 1n+dt, C.Busy{_})) == C.hush(pp.sames(rest), cfg, C.look(cfg, v, 1n+dt, C.Busy{C.W.tok(v)})) : C.Next}
              +next = C.look(cfg, v, 1n+dt, C.Busy{C.W.tok(v)})
              +moved = Equal.trans(Maybe<&2, Nat>, C.W.tok(v), Some{Pr.work(hist)}, Some{Pr.work(h)}, inv, Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n}, Pr.work(hist), Pr.work(h), Equal.sym(Nat, Pr.work(h), Pr.work(hist), same)))
              pp.watch_hush(rest, cfg, h, next, pp.loops_app(rest, hist, seg, lr), pp.keep_eq(next, C.W.tok(v), Some{Pr.work(h)}, moved, pp.same_keeps(cfg, v, 1n+dt)))
            case C.Owe{+k}:
              (w, lr) = l
              pp.watch_hush(rest, cfg, List.append(&2, Nat, hist, seg), C.Owe{k}, pp.loops_app(rest, hist, seg, lr), Unit{})
            case C.Quiet{}:
              (w, lr) = l
              pp.watch_hush(rest, cfg, List.append(&2, Nat, hist, seg), C.Quiet{}, pp.loops_app(rest, hist, seg, lr), Unit{})

# the bound over the quiet polls the polls are
def pp.long_sames(+w: C.W, +ps: List<&2, Pr.Peek>, long: {Nat.is_le(C.W.left(w), 1n+List.length(&2, Pr.Peek, ps)) == True{} : Bool}) -> {Nat.is_le(C.W.left(w), 1n+List.length(&2, C.Hush, pp.sames(ps))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, C.Hush, pp.sames(ps)), List.length(&2, Pr.Peek, ps), pp.len_sames(ps)) : {Nat.is_le(C.W.left(w), 1n+_) == True{} : Bool}
  long

def pp.loop_stalls(+cfg: C.Cfg, +w: C.W, +hist: List<&2, Nat>, p: Pr.Peek, +ps: List<&2, Pr.Peek>, l: Pr.Loops(p <> ps, hist), tok: {C.W.tok(w) == Some{Pr.work(hist)} : Maybe<&2, Nat>}, long: {Nat.is_le(C.W.left(w), List.length(&2, Pr.Peek, p <> ps)) == True{} : Bool}) -> {C.Next.watching(Pr.watch(p <> ps, cfg, hist, C.Watch{w})) == False{} : Bool}:
  match p:
    case Pr.Peek{+seg, +dt}:
      +q = {Pr.Peek{seg, dt} : Pr.Peek}
      %Equal.sym(C.Next, Pr.watch(q <> ps, cfg, hist, C.Watch{w}), C.hush(pp.sames(q <> ps), cfg, C.Watch{w}), pp.watch_hush(q <> ps, cfg, hist, C.Watch{w}, l, tok)) : {C.Next.watching(_) == False{} : Bool}
      Children.pc.stalls_in_time(cfg, w, C.Same{dt}, pp.sames(ps), pp.long_sames(w, ps, long))

# a poll that reads more work than the watch holds is progress
def pp.news(+w: C.W, +a: Nat, +b: Nat, tok: {C.W.tok(w) == Some{a} : Maybe<&2, Nat>}, lt: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {C.moved(C.W.tok(w), Some{b}) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, C.W.tok(w), Some{a}, tok) : {C.moved(_, Some{b}) == True{} : Bool}
  pp.ne(a, b, lt)

def pp.new_work_moves(+cfg: C.Cfg, +w: C.W, +e: Nat, +seen: List<&2, Nat>, +seg: List<&2, Nat>, +x: Nat, fresh: {Pr.mem(x, seen) == False{} : Bool}, i: Pr.In(x, seg), tok: {C.W.tok(w) == Some{Pr.work(seen)} : Maybe<&2, Nat>}) -> {C.look(cfg, w, e, C.Busy{Some{Pr.work(List.append(&2, Nat, seen, seg))}}) == C.Watch{C.W.fresh(cfg, Some{Pr.work(List.append(&2, Nat, seen, seg))})} : C.Next}:
  +b = Pr.work(List.append(&2, Nat, seen, seg))
  Children.pc.progress_is_not_a_stall(cfg, w, e, b, pp.news(w, Pr.work(seen), b, tok, pp.new_work(seen, seg, x, fresh, i)))
