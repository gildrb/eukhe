# eukhe: the proof of LAW guard_cuts_repeats

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

# More numbers
# ------------

def pi.eq_true(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.pi.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LLogicLogic.pi.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pi.eq_true(p, q, h))

def pi.le_refl(+a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pi.le_refl(p)

def pi.le_succ_r(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      LLogicLogic.pi.absurdF({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pi.le_succ_r(p, q, h)

def pi.le_add_r(+r: Nat, +s: Nat) -> {Nat.is_le(s, Nat.add(r, s)) == True{} : Bool}:
  match r:
    case 0n:
      pi.le_refl(s)
    case 1n+p:
      pi.le_succ_r(s, Nat.add(p, s), pi.le_add_r(p, s))

# The repetition guard
# --------------------

def pi.or_tl(a: Bool, +b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.pi.absurdF({Bool.or(False{}, b) == True{} : Bool}, h)

def pi.or_tr(a: Bool, +b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# period 1 is always checked
def pi.periodic_ge1(+s: List<&2, Nat>, +k: Nat, +r: Nat, +e: {If.each(s, 0n, Nat.sub(k, 1n)) == True{} : Bool}) -> {If.periodic.go(s, k, 1n+r) == True{} : Bool}:
  match r:
    case 0n:
      pi.or_tl(If.each(s, 0n, Nat.sub(k, 1n)), If.periodic.go(s, k, 0n), e)
    case 1n+t:
      pi.or_tr(If.each(s, 1n+t, Nat.sub(k, 2n+t)), If.periodic.go(s, k, 1n+t), pi.periodic_ge1(s, k, t, e))

def pi.periodic_one(+s: List<&2, Nat>, +k: Nat, q: Nat, +e: {If.each(s, 0n, Nat.sub(k, 1n)) == True{} : Bool}) -> {If.periodic.go(s, k, If.periods.of(q)) == True{} : Bool}:
  match q:
    case 0n:
      pi.periodic_ge1(s, k, 0n, e)
    case 1n+r:
      pi.periodic_ge1(s, k, r, e)

def pi.sub1_le(+k: Nat, +s: Nat, +h: {Nat.is_le(k, 1n+s) == True{} : Bool}) -> {Nat.is_le(Nat.sub(k, 1n), s) == True{} : Bool}:
  match k:
    case 0n:
      LNat.pi.le0(s)
    case 1n+j:
      match j:
        case 0n:
          LNat.pi.le0(s)
        case 1n+i:
          h

def pi.le_add0(+k: Nat, +run: Nat, +h: {Nat.is_le(k, Nat.add(run, 0n)) == True{} : Bool}) -> {Nat.is_le(k, run) == True{} : Bool}:
  %Equal.sym(Nat, run, Nat.add(run, 0n), LA.pi.add_zero(run)) : {Nat.is_le(k, _) == True{} : Bool}
  h

# a run that reaches k - 1 with what continues it: one chunk more
def pi.run_h(e: Bool, +y: Nat, +r2: List<&2, Nat>, +x: Nat, +s: List<&2, Nat>, +K: Nat, +ee: {Nat.is_eq(y, x) == e : Bool}, +h: {Nat.is_le(K, Nat.add(If.cycle(x <> s, 0n), If.same_run.go(y <> r2, x, e))) == True{} : Bool}, +lt: {Nat.is_le(K, If.cycle(x <> s, 0n)) == False{} : Bool}) -> {Nat.is_le(K, Nat.add(If.cycle.go(y <> x <> s, 0n, e), If.same_run(r2, y))) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(Nat, y, x, pi.eq_true(y, x, ee)) : {Nat.is_le(K, 1n+Nat.add(If.cycle(x <> s, 0n), If.same_run(r2, _))) == True{} : Bool}
      %LA.pi.add_succ(If.cycle(x <> s, 0n), If.same_run(r2, x)) : {Nat.is_le(K, _) == True{} : Bool}
      h
    case False{}:
      LA.pi.void({Nat.is_le(K, Nat.add(If.cycle.go(y <> x <> s, 0n, False{}), If.same_run(r2, y))) == True{} : Bool}, LA.pi.flip(Nat.is_le(K, If.cycle(x <> s, 0n)), pi.le_add0(K, If.cycle(x <> s, 0n), h), lt))

# a run of x whose counter of period 1, with the chunks that continue it,
# reaches k - 1 ends in a periodic window
def pi.run_loops(+rest: List<&2, Nat>, +k: Nat, +x: Nat, +s: List<&2, Nat>, c: Bool, +ec: {Nat.is_le(Nat.sub(k, 1n), If.cycle(x <> s, 0n)) == c : Bool}, +h: {Nat.is_le(Nat.sub(k, 1n), Nat.add(If.cycle(x <> s, 0n), If.same_run(rest, x))) == True{} : Bool}) -> {Bool.or(If.periodic(x <> s, k), If.loops.go(rest, k, x <> s)) == True{} : Bool}:
  match rest:
    case Nil{}:
      match c:
        case True{}:
          +e = Equal.trans(Bool, If.each(x <> s, 0n, Nat.sub(k, 1n)), Nat.is_le(Nat.sub(k, 1n), If.cycle(x <> s, 0n)), True{}, LA.pi.each_cycle(x <> s, 0n, Nat.sub(k, 1n)), ec)
          pi.or_tl(If.periodic(x <> s, k), If.loops.go(Nil{}, k, x <> s), pi.periodic_one(x <> s, k, If.quarter(k), e))
        case False{}:
          LA.pi.void({Bool.or(If.periodic(x <> s, k), If.loops.go(Nil{}, k, x <> s)) == True{} : Bool}, LA.pi.flip(Nat.is_le(Nat.sub(k, 1n), If.cycle(x <> s, 0n)), pi.le_add0(Nat.sub(k, 1n), If.cycle(x <> s, 0n), h), ec))
    case y <> r2:
      match c:
        case True{}:
          +e = Equal.trans(Bool, If.each(x <> s, 0n, Nat.sub(k, 1n)), Nat.is_le(Nat.sub(k, 1n), If.cycle(x <> s, 0n)), True{}, LA.pi.each_cycle(x <> s, 0n, Nat.sub(k, 1n)), ec)
          pi.or_tl(If.periodic(x <> s, k), If.loops.go(y <> r2, k, x <> s), pi.periodic_one(x <> s, k, If.quarter(k), e))
        case False{}:
          +h2 = pi.run_h(Nat.is_eq(y, x), y, r2, x, s, Nat.sub(k, 1n), {==}, h, ec)
          +r = pi.run_loops(r2, k, y, x <> s, Nat.is_le(Nat.sub(k, 1n), If.cycle(y <> x <> s, 0n)), {==}, h2)
          pi.or_tr(If.periodic(x <> s, k), If.loops.go(y <> r2, k, x <> s), r)

# a run that reaches k after its first chunk
def pi.rhead(xs: List<&2, Nat>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> +rest:
      Nat.is_le(k, 1n+If.same_run(rest, x))

# a stream that repeats a chunk k times in a row has a periodic window
# (period 1)
def pi.rep_go(+xs: List<&2, Nat>, +k: Nat, +seen: List<&2, Nat>, c: Bool, +ec: {pi.rhead(xs, k) == c : Bool}, +rep: {If.repeats(xs, k) == True{} : Bool}) -> {If.loops.go(xs, k, seen) == True{} : Bool}:
  match xs:
    case Nil{}:
      LLogicLogic.pi.absurdF({If.loops.go(Nil{}, k, seen) == True{} : Bool}, rep)
    case x <> rest:
      match c:
        case True{}:
          +S = If.same_run(rest, x)
          +C = If.cycle(x <> seen, 0n)
          +h = LA.pi.le_trans(Nat.sub(k, 1n), S, Nat.add(C, S), pi.sub1_le(k, S, ec), pi.le_add_r(C, S))
          pi.run_loops(rest, k, x, seen, Nat.is_le(Nat.sub(k, 1n), C), {==}, h)
        case False{}:
          +rr = LA.pi.or_r_true(Nat.is_le(k, 1n+If.same_run(rest, x)), If.repeats(rest, k), rep, ec)
          pi.or_tr(If.periodic(x <> seen, k), If.loops.go(rest, k, x <> seen), pi.rep_go(rest, k, x <> seen, pi.rhead(rest, k), {==}, rr))

def pi.guard_cuts_repeats(+xs: List<&2, Nat>, +k: Nat, rep: {If.repeats(xs, k) == True{} : Bool}) -> {If.Cut.cut(If.guard(xs, k)) == True{} : Bool}:
  LA.pi.cut_go(xs, k, Nil{}, 0n, If.fire.at(xs, k, Nil{}), {==}, pi.rep_go(xs, k, Nil{}, pi.rhead(xs, k), {==}, rep))

def Infer.guard_cuts_repeats(xs, k, rep):
  pi.guard_cuts_repeats(xs, k, rep)
