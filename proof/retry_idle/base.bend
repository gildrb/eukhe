# eukhe: lemmas the proofs of area retry_idle share

import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../base/logic/logic.bend as LLogicLogic

# Nat facts
# ---------

def ri.gt_zero(d: Nat) -> {Nat.is_gt(0n, d) == False{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+q:
      {==}

def ri.gt_refl(d: Nat) -> {Nat.is_gt(d, d) == False{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+q:
      ri.gt_refl(q)

def ri.sub_zero(d: Nat) -> {Nat.sub(d, 0n) == d : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+q:
      {==}

# a <= b <= c: a <= c
def ri.ngt_trans(g: Nat, k: Nat, d: Nat, e1: {Nat.is_gt(g, k) == False{} : Bool}, e2: {Nat.is_gt(k, d) == False{} : Bool}) -> {Nat.is_gt(g, d) == False{} : Bool}:
  match g:
    case 0n:
      ri.gt_zero(d)
    case 1n+p:
      match k:
        case 0n:
          LLogicLogic.pf.absurd_tf({Nat.is_gt(1n+p, d) == False{} : Bool}, e1)
        case 1n+q:
          match d:
            case 0n:
              LLogicLogic.pf.absurd_tf({Nat.is_gt(1n+p, 0n) == False{} : Bool}, e2)
            case 1n+r:
              ri.ngt_trans(p, q, r, e1, e2)

# neither above the other: equal
def ri.eq_of_ngt(k: Nat, d: Nat, e1: {Nat.is_gt(k, d) == False{} : Bool}, e2: {Nat.is_gt(d, k) == False{} : Bool}) -> {k == d : Nat}:
  match k:
    case 0n:
      match d:
        case 0n:
          {==}
        case 1n+q:
          LLogicLogic.pf.absurd_tf({0n == 1n+q : Nat}, e2)
    case 1n++p:
      match d:
        case 0n:
          LLogicLogic.pf.absurd_tf({1n+p == 0n : Nat}, e1)
        case 1n++q:
          Equal.cong(Nat, Nat, x => 1n+x, p, q, ri.eq_of_ngt(p, q, e1, e2))

# k below d: k and what is left of d make d
def ri.add_sub(k: Nat, d: Nat, e: {Nat.is_gt(d, k) == True{} : Bool}) -> {Nat.add(k, Nat.sub(d, k)) == d : Nat}:
  match k:
    case 0n:
      match d:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n++p:
      match d:
        case 0n:
          LLogicLogic.wr_absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, e)
        case 1n++q:
          Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, Nat.sub(q, p)), q, ri.add_sub(p, q, e))

def ri.ngt_succ(x: Nat, p: Nat, e: {Nat.is_gt(x, p) == False{} : Bool}) -> {Nat.is_gt(x, 1n+p) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+a:
      match p:
        case 0n:
          LLogicLogic.pf.absurd_tf({Nat.is_gt(1n+a, 1n) == False{} : Bool}, e)
        case 1n+b:
          ri.ngt_succ(a, b, e)

# k - g is at most k
def ri.sub_ngt(k: Nat, g: Nat) -> {Nat.is_gt(Nat.sub(k, g), k) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      match g:
        case 0n:
          ri.gt_refl(1n+p)
        case 1n++q:
          ri.ngt_succ(Nat.sub(p, q), p, ri.sub_ngt(p, q))

# An event, under a timer within the deadline
# --------------------------------------------

# the timer after an event that came: k - g when it came before the
# timer, d - g when it came after a re-arm
def ri.came(late: Bool, +g: Nat, +d: Nat, +k: Nat) -> Nat:
  match late:
    case False{}:
      Nat.sub(k, g)
    case True{}:
      Nat.sub(d, g)

def ri.asel(over: Bool, +last: Nat, +d: Nat, c: Nat) -> RetryIdle.Arrive:
  match over:
    case True{}:
      RetryIdle.ArrStall{Nat.add(last, d)}
    case False{}:
      RetryIdle.ArrCame{c}

# what an event g after last meets, the timer k <= d after last: the
# stall at last + d past the deadline, else the event and the timer after it
def ri.arr(+g: Nat, +d: Nat, +last: Nat, +k: Nat) -> RetryIdle.Arrive:
  ri.asel(Nat.is_gt(g, d), last, d, ri.came(Nat.is_gt(g, k), g, d, k))

def ri.a3(b3: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat, e3: {Nat.is_gt(g, d) == b3 : Bool}, e1: {Nat.is_gt(g, k) == True{} : Bool}) -> {RetryIdle.arrive.after(b3, g, d, last, d) == ri.arr(g, d, last, k) : RetryIdle.Arrive}:
  match b3:
    case False{}:
      %Equal.sym(Bool, Nat.is_gt(g, d), False{}, e3) : {RetryIdle.ArrCame{Nat.sub(d, g)} == ri.asel(_, last, d, ri.came(Nat.is_gt(g, k), g, d, k)) : RetryIdle.Arrive}
      %Equal.sym(Bool, Nat.is_gt(g, k), True{}, e1) : {RetryIdle.ArrCame{Nat.sub(d, g)} == ri.asel(False{}, last, d, ri.came(_, g, d, k)) : RetryIdle.Arrive}
      {==}
    case True{}:
      %Equal.sym(Bool, Nat.is_gt(d, d), False{}, ri.gt_refl(d)) : {RetryIdle.arrive.fire2(last, d, R.idle.wake.sel(_, Nat.sub(d, d))) == ri.arr(g, d, last, k) : RetryIdle.Arrive}
      %Equal.sym(Bool, Nat.is_gt(g, d), True{}, e3) : {RetryIdle.ArrStall{Nat.add(last, d)} == ri.asel(_, last, d, ri.came(Nat.is_gt(g, k), g, d, k)) : RetryIdle.Arrive}
      {==}

def ri.a2(b2: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat, e2: {Nat.is_gt(d, k) == b2 : Bool}, +e1: {Nat.is_gt(g, k) == True{} : Bool}, hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {RetryIdle.arrive.fire1(g, d, last, k, R.idle.wake.sel(b2, Nat.sub(d, k))) == ri.arr(g, d, last, k) : RetryIdle.Arrive}:
  match b2:
    case False{}:
      +ekd = ri.eq_of_ngt(k, d, hk, e2)
      +egd = Equal.trans(Bool, Nat.is_gt(g, d), Nat.is_gt(g, k), True{}, Equal.cong(Nat, Bool, x => Nat.is_gt(g, x), d, k, Equal.sym(Nat, k, d, ekd)), e1)
      %Equal.sym(Bool, Nat.is_gt(g, d), True{}, egd) : {RetryIdle.ArrStall{Nat.add(last, k)} == ri.asel(_, last, d, ri.came(Nat.is_gt(g, k), g, d, k)) : RetryIdle.Arrive}
      Equal.cong(Nat, RetryIdle.Arrive, x => RetryIdle.ArrStall{Nat.add(last, x)}, k, d, ekd)
    case True{}:
      %Equal.sym(Nat, Nat.add(k, Nat.sub(d, k)), d, ri.add_sub(k, d, e2)) : {RetryIdle.arrive.after(Nat.is_gt(g, _), g, d, last, _) == ri.arr(g, d, last, k) : RetryIdle.Arrive}
      ri.a3(Nat.is_gt(g, d), g, d, last, k, {==}, e1)

def ri.a1(b1: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat, +e1: {Nat.is_gt(g, k) == b1 : Bool}, +hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {RetryIdle.arrive.first(b1, g, d, last, k) == ri.arr(g, d, last, k) : RetryIdle.Arrive}:
  match b1:
    case False{}:
      %Equal.sym(Bool, Nat.is_gt(g, d), False{}, ri.ngt_trans(g, k, d, e1, hk)) : {RetryIdle.ArrCame{Nat.sub(k, g)} == ri.asel(_, last, d, ri.came(Nat.is_gt(g, k), g, d, k)) : RetryIdle.Arrive}
      %Equal.sym(Bool, Nat.is_gt(g, k), False{}, e1) : {RetryIdle.ArrCame{Nat.sub(k, g)} == ri.asel(False{}, last, d, ri.came(_, g, d, k)) : RetryIdle.Arrive}
      {==}
    case True{}:
      ri.a2(Nat.is_gt(d, k), g, d, last, k, {==}, e1, hk)

# the loop meets an event as ri.arr says
def ri.arrive(+g: Nat, +d: Nat, +last: Nat, +k: Nat, hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {RetryIdle.arrive(g, d, last, k) == ri.arr(g, d, last, k) : RetryIdle.Arrive}:
  ri.a1(Nat.is_gt(g, k), g, d, last, k, {==}, hk)

def ri.l2(b: Bool, +g: Nat, +d: Nat, +k: Nat, hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {Nat.is_gt(ri.came(b, g, d, k), d) == False{} : Bool}:
  match b:
    case False{}:
      ri.ngt_trans(Nat.sub(k, g), k, d, ri.sub_ngt(k, g), hk)
    case True{}:
      ri.sub_ngt(d, g)

def ri.l1(b: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat, hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {Nat.is_gt(RetryIdle.arrive.left(ri.asel(b, last, d, ri.came(Nat.is_gt(g, k), g, d, k))), d) == False{} : Bool}:
  match b:
    case True{}:
      ri.gt_zero(d)
    case False{}:
      ri.l2(Nat.is_gt(g, k), g, d, k, hk)

# the timer after an event stays within the deadline
def ri.left_ngt(+g: Nat, +d: Nat, +last: Nat, +k: Nat, hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {Nat.is_gt(RetryIdle.arrive.left(ri.arr(g, d, last, k)), d) == False{} : Bool}:
  ri.l1(Nat.is_gt(g, d), g, d, last, k, hk)

# The loop over the events
# ------------------------

def ri.m_nil(b: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat) -> {RetryIdle.drive.sel(ri.asel(b, last, d, ri.came(Nat.is_gt(g, k), g, d, k)), Nil{}, Nat.add(last, g), RetryIdle.drive(Nil{}, d, Nat.add(last, g), RetryIdle.arrive.left(ri.asel(b, last, d, ri.came(Nat.is_gt(g, k), g, d, k))))) == Some{R.idle.sel(b, R.IdleStall{Nat.add(last, d)}, R.idle.go(Nil{}, d, Nat.add(last, g)))} : Maybe<&2, R.Idle>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ri.m_cons(b: Bool, +g: Nat, +h: Nat, +t: List<&2, Nat>, +d: Nat, +last: Nat, +k: Nat, ih: {RetryIdle.drive(h <> t, d, Nat.add(last, g), RetryIdle.arrive.left(ri.asel(b, last, d, ri.came(Nat.is_gt(g, k), g, d, k)))) == Some{R.idle.go(h <> t, d, Nat.add(last, g))} : Maybe<&2, R.Idle>}) -> {RetryIdle.drive.sel(ri.asel(b, last, d, ri.came(Nat.is_gt(g, k), g, d, k)), h <> t, Nat.add(last, g), RetryIdle.drive(h <> t, d, Nat.add(last, g), RetryIdle.arrive.left(ri.asel(b, last, d, ri.came(Nat.is_gt(g, k), g, d, k))))) == Some{R.idle.sel(b, R.IdleStall{Nat.add(last, d)}, R.idle.go(h <> t, d, Nat.add(last, g)))} : Maybe<&2, R.Idle>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the loop ends the events g, rest after last as the idle model does,
# from any timer within the deadline
def ri.drive(rest: List<&2, Nat>, +g: Nat, +d: Nat, +last: Nat, +k: Nat, +hk: {Nat.is_gt(k, d) == False{} : Bool}) -> {RetryIdle.drive(g <> rest, d, last, k) == Some{R.idle.go(g <> rest, d, last)} : Maybe<&2, R.Idle>}:
  match rest:
    case Nil{}:
      %Equal.sym(RetryIdle.Arrive, RetryIdle.arrive(g, d, last, k), ri.arr(g, d, last, k), ri.arrive(g, d, last, k, hk)) : {RetryIdle.drive.sel(_, Nil{}, Nat.add(last, g), RetryIdle.drive(Nil{}, d, Nat.add(last, g), RetryIdle.arrive.left(_))) == Some{R.idle.go(g <> Nil{}, d, last)} : Maybe<&2, R.Idle>}
      ri.m_nil(Nat.is_gt(g, d), g, d, last, k)
    case +h <> +t:
      +ih = ri.drive(t, h, d, Nat.add(last, g), RetryIdle.arrive.left(ri.arr(g, d, last, k)), ri.left_ngt(g, d, last, k, hk))
      %Equal.sym(RetryIdle.Arrive, RetryIdle.arrive(g, d, last, k), ri.arr(g, d, last, k), ri.arrive(g, d, last, k, hk)) : {RetryIdle.drive.sel(_, h <> t, Nat.add(last, g), RetryIdle.drive(h <> t, d, Nat.add(last, g), RetryIdle.arrive.left(_))) == Some{R.idle.go(g <> (h <> t), d, last)} : Maybe<&2, R.Idle>}
      ri.m_cons(Nat.is_gt(g, d), g, h, t, d, last, k, ih)

# The entry
# ---------

def ri.bool_rt(b: Bool, rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ri.put_wake(w: R.Wake) -> {Fi.put_wake(w) == RetryIdle.spell_wake(w) : String}:
  match w:
    case R.WakeStall{}:
      {==}
    case R.WakeSleep{us}:
      {==}

# the laws' reader, its requests turned into the entry's
def ri.req(a: RetryIdle.idle.Ask) -> Fi.Req:
  match a:
    case RetryIdle.idle.AskArm{nan, neg, whole, frac}:
      Fi.QArm{nan, neg, whole, frac}
    case RetryIdle.idle.AskWake{held, since, d}:
      Fi.QWake{held, since, d}

def ri.conv(r: Wr.Dec<RetryIdle.idle.Ask>) -> Wr.Dec<Fi.Req>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{ri.req(a), s}
    case Wr.Bad{}:
      Wr.Bad{}

def ri.rq_arm_frac(nan: Bool, neg: Bool, whole: Nat, r: Wr.Dec<Bool>) -> {ri.conv(RetryIdle.read_arm.frac(nan, neg, whole, r)) == Fi.get_arm.frac(nan, neg, whole, r) : Wr.Dec<Fi.Req>}:
  match r:
    case Wr.Got{frac, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ri.rq_arm_whole(nan: Bool, neg: Bool, r: Wr.Dec<Nat>) -> {ri.conv(RetryIdle.read_arm.whole(nan, neg, r)) == Fi.get_arm.whole(nan, neg, r) : Wr.Dec<Fi.Req>}:
  match r:
    case Wr.Got{whole, s}:
      ri.rq_arm_frac(nan, neg, whole, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ri.rq_arm_neg(nan: Bool, r: Wr.Dec<Bool>) -> {ri.conv(RetryIdle.read_arm.neg(nan, r)) == Fi.get_arm.neg(nan, r) : Wr.Dec<Fi.Req>}:
  match r:
    case Wr.Got{neg, s}:
      ri.rq_arm_whole(nan, neg, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ri.rq_arm(r: Wr.Dec<Bool>) -> {ri.conv(RetryIdle.read_arm(r)) == Fi.get_arm(r) : Wr.Dec<Fi.Req>}:
  match r:
    case Wr.Got{nan, s}:
      ri.rq_arm_neg(nan, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ri.rq_wake_d(held: Bool, since: Nat, r: Wr.Dec<Nat>) -> {ri.conv(RetryIdle.read_wake.d(held, since, r)) == Fi.get_wake.d(held, since, r) : Wr.Dec<Fi.Req>}:
  match r:
    case Wr.Got{d, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ri.rq_wake_since(held: Bool, r: Wr.Dec<Nat>) -> {ri.conv(RetryIdle.read_wake.since(held, r)) == Fi.get_wake.since(held, r) : Wr.Dec<Fi.Req>}:
  match r:
    case Wr.Got{since, s}:
      ri.rq_wake_d(held, since, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ri.rq_wake(r: Wr.Dec<Bool>) -> {ri.conv(RetryIdle.read_wake(r)) == Fi.get_wake(r) : Wr.Dec<Fi.Req>}:
  match r:
    case Wr.Got{held, s}:
      ri.rq_wake_since(held, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ri.rq_tag(t: Nat, s: String) -> {ri.conv(RetryIdle.read_ask.tag(t, s)) == Fi.get_req.tag(t, s) : Wr.Dec<Fi.Req>}:
  match t:
    case 0n:
      ri.rq_arm(Wr.get_bool(s))
    case 1n:
      ri.rq_wake(Wr.get_bool(s))
    case 2n+p:
      {==}

# the entry reads every input as the laws' reader does
def ri.rq(r: Wr.Dec<Nat>) -> {ri.conv(RetryIdle.read_ask.go(r)) == Fi.get_req.go(r) : Wr.Dec<Fi.Req>}:
  match r:
    case Wr.Got{t, s}:
      ri.rq_tag(t, s)
    case Wr.Bad{}:
      {==}
