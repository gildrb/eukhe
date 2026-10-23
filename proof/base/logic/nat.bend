# eukhe: lemmas the proofs of two or more areas share: logic/nat

import Base
import ../../../bend/fsmode.bend as Fs
import ../../../bend/replace.bend as Rp
import ../../../bend/run/state.bend as RnState
import ../../../bend/run/step.bend as RnStep
import ../../../bend/semver.bend as Sv
import ../../../laws/command.bend as Command
import ./bool.bend as LLogicBool
import ./logic.bend as LLogicLogic

# Equality of chars, names, paths
# -------------------------------

def cb_nat_eq(+x: Nat, +y: Nat, e: {Nat.is_eq(x, y) == True{} : Bool}) -> {x == y : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.cb_absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      LLogicLogic.cb_absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %cb_nat_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def child.pc.eq_of(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.child.pc.absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      LLogicLogic.child.pc.absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %child.pc.eq_of(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def pq.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.pq.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LLogicLogic.pq.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pq.eq_true(p, q, h))

def semver.ps.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.semver.ps.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LLogicLogic.semver.ps.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, semver.ps.eq_true(p, q, h))

def ppr.nat_eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.ppr.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LLogicLogic.ppr.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, ppr.nat_eq_true(p, q, h))

def supervisor.ps.eq_of_is_eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.supervisor.ps.absurdF({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      LLogicLogic.supervisor.ps.absurdF({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, supervisor.ps.eq_of_is_eq(p, q, e))

def rp.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.rp.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LLogicLogic.rp.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, rp.eq_true(p, q, h))

# cmd_eq true: the names are equal
def cb_eq(+a: List<&2, Nat>, +b: List<&2, Nat>, +e: {Command.cmd_eq(a, b) == True{} : Bool}) -> {a == b : List<&2, Nat>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      LLogicLogic.cb_absurd({Nil{} == y <> ys : List<&2, Nat>}, e)
    case Con{x, xs} Nil{}:
      LLogicLogic.cb_absurd({x <> xs == Nil{} : List<&2, Nat>}, e)
    case Con{+x, +xs} Con{+y, +ys}:
      %cb_nat_eq(x, y, LLogicBool.cb_and_l(Nat.is_eq(x, y), Command.cmd_eq(xs, ys), e)) : {x <> xs == _ <> ys : List<&2, Nat>}
      %cb_eq(xs, ys, LLogicBool.cb_and_r(Nat.is_eq(x, y), Command.cmd_eq(xs, ys), e)) : {x <> xs == x <> _ : List<&2, Nat>}
      {==}

# cmd_path_eq true: the paths are equal
def cb_path_eq(+a: List<&2, List<&2, Nat>>, +b: List<&2, List<&2, Nat>>, +e: {Command.cmd_path_eq(a, b) == True{} : Bool}) -> {a == b : List<&2, List<&2, Nat>>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      LLogicLogic.cb_absurd({Nil{} == y <> ys : List<&2, List<&2, Nat>>}, e)
    case Con{x, xs} Nil{}:
      LLogicLogic.cb_absurd({x <> xs == Nil{} : List<&2, List<&2, Nat>>}, e)
    case Con{+x, +xs} Con{+y, +ys}:
      %cb_eq(x, y, LLogicBool.cb_and_l(Command.cmd_eq(x, y), Command.cmd_path_eq(xs, ys), e)) : {x <> xs == _ <> ys : List<&2, List<&2, Nat>>}
      %cb_path_eq(xs, ys, LLogicBool.cb_and_r(Command.cmd_eq(x, y), Command.cmd_path_eq(xs, ys), e)) : {x <> xs == x <> _ : List<&2, List<&2, Nat>>}
      {==}

# The value of digits read last first: d0 + 10 * value(rest).
def wo_value(ds: List<&2, Nat>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, t}:
      Nat.add(d, Nat.mul(10n, wo_value(t)))

def wn_pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# a - b, cut at 0
def wn_sub(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n 0n:
      0n
    case 0n 1n+q:
      0n
    case 1n+p 0n:
      1n+p
    case 1n+p 1n+q:
      wn_sub(p, q)

# ---- agree ----

# proof_agree: push_agrees_always, for every number of pushes. Under push
# alone, Taelin's list is a bijective binary counter: T messages are
# T = sum (1 + d_j)·2^j with digits d_j in {0, 1} (the keep bits, newest
# entry first), and entry j is one line of level j + d_j. pa.GE writes
# push's list and pa.GV the view (that list read oldest first) as
# functions of the digits.
#
# One step appends message T's line, and push adds 1 to the digits. If
# every digit is 1, the list grows and the fit merges nothing. Otherwise
# let j be the lowest 0 digit: push's carry merges the two level-j lines
# j and j-1 (line 0 and the new line when j = 0), and with push's length
# as the budget the fit makes exactly one merge. The due order picks that
# pair:
# - j > 0 (the lowest digit is 1): the view is the view of the higher
#   digits one level up (every line lifted, T + 2 doubled) plus the new
#   line, and the due order between lifted lines is the same (pa.md_lift),
#   so the fit is the lifted fit of the higher digits (pa.fit_lift);
# - j = 0: the pair (line 0, the new line) is due (T + 1 - T)/1 = 1; every
#   older line ends recently enough, in its own line size, to be due less
#   than 1 (pa.Good, pa.old_one), and no later pair can merge (their
#   levels differ).
#
# The arithmetic runs on Nat through Bits.val: the comparisons of the
# model's bit lists are those of their values (pa.cmp_val, pa.val_add).

# Nat
# ---

def pa.succ(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, pred, 1n+a, 1n+b, e)

# The measure
# -----------
# M(s): the inputs a run may still take from s, at most; 0 once it ended.
# A request takes Q = 2 + polls inputs (its preparation, its reply, its
# polls); a retry (noted or not) one more request; a compaction one input
# and one more request; a generation G inputs, its round's end included.
# u is the retries and notes left, U the retries and notes a generation
# starts with.

def Q(+P: Nat) -> Nat:
  2n+P

# what the compactions c and the retries and notes u left in a generation
# may take
def B(+P: Nat, c: Nat, u: Nat) -> Nat:
  Nat.add(Nat.mul(c, 1n+Q(P)), Nat.mul(u, Q(P)))

# what the generation may still take before its round ends
def gen(+P: Nat, ph: RnState.Ph, c: Nat, u: Nat, p: Nat) -> Nat:
  match ph:
    case RnState.Prepare{}:
      Nat.add(Q(P), B(P, c, u))
    case RnState.Call{}:
      1n+Nat.add(p, B(P, c, u))
    case RnState.Compact{over}:
      1n+Nat.add(Q(P), B(P, c, u))
    case RnState.Tools{}:
      0n
    case RnState.Answered{}:
      0n
    case RnState.Aborted{}:
      0n
    case RnState.Failed{why}:
      0n

def G(+P: Nat, +U: Nat) -> Nat:
  1n+gen(P, RnState.Prepare{}, 1n, U, 0n)

def M.ph(+P: Nat, +U: Nat, ph: RnState.Ph, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> Nat:
  match ph:
    case RnState.Prepare{}:
      Nat.add(gen(P, RnState.Prepare{}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case RnState.Call{}:
      Nat.add(gen(P, RnState.Call{}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case RnState.Compact{over}:
      Nat.add(gen(P, RnState.Compact{over}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case RnState.Tools{}:
      Nat.add(gen(P, RnState.Tools{}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case RnState.Answered{}:
      0n
    case RnState.Aborted{}:
      0n
    case RnState.Failed{why}:
      0n

def M(+cfg: RnState.Cfg, s: RnState.St) -> Nat:
  match cfg s:
    case RnState.Cfg{cap, pp, aa, nn} RnState.St{ph, r, c, a, n, p}:
      M.ph(pp, Nat.add(aa, nn), ph, r, c, Nat.add(a, n), p)

def X(+P: Nat, +U: Nat, r: Nat) -> Nat:
  Nat.mul(r, G(P, U))

def K.prepare_cut(+P: Nat, cut: Bool, c: Nat) -> Nat:
  match cut c:
    case True{} 1n+d:
      1n+P
    case True{} 0n:
      0n
    case False{} c:
      0n

def K.prepare(+P: Nat, reply: RnState.Reply, c: Nat) -> Nat:
  match reply:
    case RnState.Overflow{cut}:
      K.prepare_cut(P, cut, c)
    case RnState.Plain{}:
      0n
    case RnState.Calls{}:
      0n
    case RnState.Deferred{}:
      0n
    case RnState.Error{retryable, noted}:
      0n

# the k of a call that ends the run
def K.call_end(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> Nat:
  Nat.add(gen(P, RnState.Call{}, c, u, p), X(P, U, r))

def K.retry(+P: Nat, +U: Nat, retryable: Bool, +r: Nat, +c: Nat, a: Nat, +n: Nat, +p: Nat) -> Nat:
  match retryable a:
    case True{} 1n+b:
      p
    case True{} 0n:
      K.call_end(P, U, r, c, Nat.add(0n, n), p)
    case False{} +a:
      K.call_end(P, U, r, c, Nat.add(a, n), p)

def K.note(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +a: Nat, n: Nat, +p: Nat) -> Nat:
  match n:
    case 1n+m:
      p
    case 0n:
      K.call_end(P, U, r, c, Nat.add(a, 0n), p)

def K.error(+P: Nat, +U: Nat, retryable: Bool, noted: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Nat:
  match noted:
    case True{}:
      K.note(P, U, r, c, a, n, p)
    case False{}:
      K.retry(P, U, retryable, r, c, a, n, p)

def K.overflow(+P: Nat, +U: Nat, cut: Bool, +r: Nat, c: Nat, +u: Nat, +p: Nat) -> Nat:
  match cut c:
    case True{} 1n+d:
      p
    case True{} 0n:
      K.call_end(P, U, r, 0n, u, p)
    case False{} +c:
      K.call_end(P, U, r, c, u, p)

def K.deferred(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +u: Nat, p: Nat) -> Nat:
  match p:
    case 0n:
      K.call_end(P, U, r, c, u, 0n)
    case 1n+q:
      0n

def K.call(+P: Nat, +U: Nat, reply: RnState.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Nat:
  match reply:
    case RnState.Plain{}:
      K.call_end(P, U, r, c, Nat.add(a, n), p)
    case RnState.Calls{}:
      Nat.add(p, B(P, c, Nat.add(a, n)))
    case RnState.Deferred{}:
      K.deferred(P, U, r, c, Nat.add(a, n), p)
    case RnState.Error{retryable, noted}:
      K.error(P, U, retryable, noted, r, c, a, n, p)
    case RnState.Overflow{cut}:
      K.overflow(P, U, cut, r, c, Nat.add(a, n), p)

def K.compact(+P: Nat, +U: Nat, over: Bool, got: RnState.Got, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> Nat:
  match over got:
    case over RnState.Built{}:
      0n
    case True{} RnState.Kept{}:
      Nat.add(gen(P, RnState.Compact{True{}}, c, u, p), X(P, U, r))
    case False{} RnState.Kept{}:
      0n
    case over RnState.Broke{}:
      Nat.add(gen(P, RnState.Compact{over}, c, u, p), X(P, U, r))

def K.round(+P: Nat, +U: Nat, reset: Bool, r: Nat) -> Nat:
  match reset r:
    case reset 0n:
      Nat.add(0n, X(P, U, 0n))
    case True{} 1n+s:
      Nat.add(0n, X(P, U, 1n+s))
    case False{} 1n+s:
      0n

def K.tools(+P: Nat, +U: Nat, fin: RnState.Fin, +r: Nat) -> Nat:
  match fin:
    case RnState.Stops{}:
      Nat.add(0n, X(P, U, r))
    case RnState.Goes{}:
      K.round(P, U, False{}, r)
    case RnState.Resets{}:
      K.round(P, U, True{}, r)

# k for any input
def K(+cfg: RnState.Cfg, s: RnState.St, e: RnState.Ev) -> Nat:
  match cfg s:
    case RnState.Cfg{cap, pp, aa, nn} RnState.St{ph, r, c, a, n, p}:
      match ph e:
        case RnState.Answered{} e:
          0n
        case RnState.Aborted{} e:
          0n
        case RnState.Failed{why} e:
          0n
        case RnState.Prepare{} RnState.Abort{}:
          Nat.add(gen(pp, RnState.Prepare{}, c, Nat.add(a, n), p), X(pp, Nat.add(aa, nn), r))
        case RnState.Call{} RnState.Abort{}:
          K.call_end(pp, Nat.add(aa, nn), r, c, Nat.add(a, n), p)
        case RnState.Compact{over} RnState.Abort{}:
          Nat.add(gen(pp, RnState.Compact{over}, c, Nat.add(a, n), p), X(pp, Nat.add(aa, nn), r))
        case RnState.Tools{} RnState.Abort{}:
          Nat.add(0n, X(pp, Nat.add(aa, nn), r))
        case RnState.Prepare{} RnState.Go{reply, fin, got}:
          K.prepare(pp, reply, c)
        case RnState.Call{} RnState.Go{reply, fin, got}:
          K.call(pp, Nat.add(aa, nn), reply, r, c, a, n, p)
        case RnState.Compact{over} RnState.Go{reply, fin, got}:
          K.compact(pp, Nat.add(aa, nn), over, got, r, c, Nat.add(a, n), p)
        case RnState.Tools{} RnState.Go{reply, fin, got}:
          K.tools(pp, Nat.add(aa, nn), fin, r)

# The working dir of a session
# ----------------------------

def pf.opened_p(o: Fs.Open) -> Nat:
  match o:
    case Fs.Opened{p}:
      p
    case Fs.NeedsCwd{}:
      0n
    case Fs.Gone{p}:
      0n
    case Fs.NotDir{p}:
      0n

# a + b == 0: both are 0
def auth_flight.pf.add_zero(a: Nat, -b: Nat, e: {Nat.add(a, b) == 0n : Nat}) -> ({a == 0n : Nat} & {b == 0n : Nat}):
  match a:
    case 0n:
      ({==}, e)
    case 1n+p:
      LLogicLogic.pf.succ_ne_zero(({1n+p == 0n : Nat} & {b == 0n : Nat}), Nat.add(p, b), e)

def rk.ten_zero(v: Nat, e: {Sv.Num.ten(v) == 0n : Nat}) -> {v == 0n : Nat}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      LLogicLogic.pf.succ_ne_zero({1n+p == 0n : Nat}, Nat.add(9n, Sv.Num.ten(p)), e)

# digits whose most significant digit is not 0 have a value above 0
def rk.pos(rr: List<&2, Sv.Dig>, +r: Sv.Dig, h: {Bool.not(Rp.zero(Rp.top(rr, r))) == True{} : Bool}, e: {Sv.Num.val(r <> rr) == 0n : Nat}) -> Empty:
  match rr:
    case Nil{}:
      match r:
        case Sv.D0{}:
          LLogicLogic.semver.ps.absurdF(Empty, h)
        case Sv.D1{}:
          LLogicLogic.pf.succ_ne_zero(Empty, 0n, e)
        case Sv.D2{}:
          LLogicLogic.pf.succ_ne_zero(Empty, 1n, e)
        case Sv.D3{}:
          LLogicLogic.pf.succ_ne_zero(Empty, 2n, e)
        case Sv.D4{}:
          LLogicLogic.pf.succ_ne_zero(Empty, 3n, e)
        case Sv.D5{}:
          LLogicLogic.pf.succ_ne_zero(Empty, 4n, e)
        case Sv.D6{}:
          LLogicLogic.pf.succ_ne_zero(Empty, 5n, e)
        case Sv.D7{}:
          LLogicLogic.pf.succ_ne_zero(Empty, 6n, e)
        case Sv.D8{}:
          LLogicLogic.pf.succ_ne_zero(Empty, 7n, e)
        case Sv.D9{}:
          LLogicLogic.pf.succ_ne_zero(Empty, 8n, e)
    case +r2 <> +rr2:
      rk.pos(rr2, r2, h, rk.ten_zero(Sv.Num.val(r2 <> rr2), LLogicLogic.pf.snd({Sv.Dig.val(r) == 0n : Nat}, {Sv.Num.ten(Sv.Num.val(r2 <> rr2)) == 0n : Nat}, auth_flight.pf.add_zero(Sv.Dig.val(r), Sv.Num.ten(Sv.Num.val(r2 <> rr2)), e))))

# Each phase
# ----------
# For a live run s and any input e, M falls: M(s) = k + 1 + M(step(s, e)),
# with k = K(cfg, s, e). Once a run ends, M is 0.

# M falls from s to t, by k + 1
def Fall(+cfg: RnState.Cfg, s: RnState.St, k: Nat, t: RnState.St) -> Type:
  {M(cfg, s) == Nat.add(k, 1n+M(cfg, t)) : Nat}

# the goal of dec at a phase
def FallAt(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +ph: RnState.Ph, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +e: RnState.Ev) -> Type:
  Fall(RnState.Cfg{cap, P, A, N}, RnState.St{ph, r, c, a, n, p}, K(RnState.Cfg{cap, P, A, N}, RnState.St{ph, r, c, a, n, p}, e), RnStep.step(RnState.Cfg{cap, P, A, N}, RnState.St{ph, r, c, a, n, p}, e))
