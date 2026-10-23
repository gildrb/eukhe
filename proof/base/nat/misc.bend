# eukhe: lemmas the proofs of two or more areas share: nat/misc

import Base
import ../../../bend/fsmode.bend as Fs
import ../../../bend/run.bend as Rn
import ../bool/misc.bend as LBoolMisc

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

def ND(n: Nat, t: Type, f: Type) -> Type:
  match n:
    case 0n:
      t
    case 1n+p:
      f

# 0 is no successor
def zero_succ(-A: Type, -n: Nat, e: {0n == 1n+n : Nat}) -> A:
  %e : ND(_, Unit, A)
  Unit{}

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
def gen(+P: Nat, ph: Rn.Ph, c: Nat, u: Nat, p: Nat) -> Nat:
  match ph:
    case Rn.Prepare{}:
      Nat.add(Q(P), B(P, c, u))
    case Rn.Call{}:
      1n+Nat.add(p, B(P, c, u))
    case Rn.Compact{over}:
      1n+Nat.add(Q(P), B(P, c, u))
    case Rn.Tools{}:
      0n
    case Rn.Answered{}:
      0n
    case Rn.Aborted{}:
      0n
    case Rn.Failed{why}:
      0n

def G(+P: Nat, +U: Nat) -> Nat:
  1n+gen(P, Rn.Prepare{}, 1n, U, 0n)

def M.ph(+P: Nat, +U: Nat, ph: Rn.Ph, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> Nat:
  match ph:
    case Rn.Prepare{}:
      Nat.add(gen(P, Rn.Prepare{}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case Rn.Call{}:
      Nat.add(gen(P, Rn.Call{}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case Rn.Compact{over}:
      Nat.add(gen(P, Rn.Compact{over}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case Rn.Tools{}:
      Nat.add(gen(P, Rn.Tools{}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case Rn.Answered{}:
      0n
    case Rn.Aborted{}:
      0n
    case Rn.Failed{why}:
      0n

def M(+cfg: Rn.Cfg, s: Rn.St) -> Nat:
  match cfg s:
    case Rn.Cfg{cap, pp, aa, nn} Rn.St{ph, r, c, a, n, p}:
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

def K.prepare(+P: Nat, reply: Rn.Reply, c: Nat) -> Nat:
  match reply:
    case Rn.Overflow{cut}:
      K.prepare_cut(P, cut, c)
    case Rn.Plain{}:
      0n
    case Rn.Calls{}:
      0n
    case Rn.Deferred{}:
      0n
    case Rn.Error{retryable, noted}:
      0n

# the k of a call that ends the run
def K.call_end(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> Nat:
  Nat.add(gen(P, Rn.Call{}, c, u, p), X(P, U, r))

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

def K.call(+P: Nat, +U: Nat, reply: Rn.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Nat:
  match reply:
    case Rn.Plain{}:
      K.call_end(P, U, r, c, Nat.add(a, n), p)
    case Rn.Calls{}:
      Nat.add(p, B(P, c, Nat.add(a, n)))
    case Rn.Deferred{}:
      K.deferred(P, U, r, c, Nat.add(a, n), p)
    case Rn.Error{retryable, noted}:
      K.error(P, U, retryable, noted, r, c, a, n, p)
    case Rn.Overflow{cut}:
      K.overflow(P, U, cut, r, c, Nat.add(a, n), p)

def K.compact(+P: Nat, +U: Nat, over: Bool, got: Rn.Got, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> Nat:
  match over got:
    case over Rn.Built{}:
      0n
    case True{} Rn.Kept{}:
      Nat.add(gen(P, Rn.Compact{True{}}, c, u, p), X(P, U, r))
    case False{} Rn.Kept{}:
      0n
    case over Rn.Broke{}:
      Nat.add(gen(P, Rn.Compact{over}, c, u, p), X(P, U, r))

def K.round(+P: Nat, +U: Nat, reset: Bool, r: Nat) -> Nat:
  match reset r:
    case reset 0n:
      Nat.add(0n, X(P, U, 0n))
    case True{} 1n+s:
      Nat.add(0n, X(P, U, 1n+s))
    case False{} 1n+s:
      0n

def K.tools(+P: Nat, +U: Nat, fin: Rn.Fin, +r: Nat) -> Nat:
  match fin:
    case Rn.Stops{}:
      Nat.add(0n, X(P, U, r))
    case Rn.Goes{}:
      K.round(P, U, False{}, r)
    case Rn.Resets{}:
      K.round(P, U, True{}, r)

# k for any input
def K(+cfg: Rn.Cfg, s: Rn.St, e: Rn.Ev) -> Nat:
  match cfg s:
    case Rn.Cfg{cap, pp, aa, nn} Rn.St{ph, r, c, a, n, p}:
      match ph e:
        case Rn.Answered{} e:
          0n
        case Rn.Aborted{} e:
          0n
        case Rn.Failed{why} e:
          0n
        case Rn.Prepare{} Rn.Abort{}:
          Nat.add(gen(pp, Rn.Prepare{}, c, Nat.add(a, n), p), X(pp, Nat.add(aa, nn), r))
        case Rn.Call{} Rn.Abort{}:
          K.call_end(pp, Nat.add(aa, nn), r, c, Nat.add(a, n), p)
        case Rn.Compact{over} Rn.Abort{}:
          Nat.add(gen(pp, Rn.Compact{over}, c, Nat.add(a, n), p), X(pp, Nat.add(aa, nn), r))
        case Rn.Tools{} Rn.Abort{}:
          Nat.add(0n, X(pp, Nat.add(aa, nn), r))
        case Rn.Prepare{} Rn.Go{reply, fin, got}:
          K.prepare(pp, reply, c)
        case Rn.Call{} Rn.Go{reply, fin, got}:
          K.call(pp, Nat.add(aa, nn), reply, r, c, a, n, p)
        case Rn.Compact{over} Rn.Go{reply, fin, got}:
          K.compact(pp, Nat.add(aa, nn), over, got, r, c, Nat.add(a, n), p)
        case Rn.Tools{} Rn.Go{reply, fin, got}:
          K.tools(pp, Nat.add(aa, nn), fin, r)

def tc.cmp_lt(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.cmp(a, b) == LT{} : Cmp}:
  match a b:
    case _ 0n:
      LBoolMisc.tree.pt.absurdF({Nat.cmp(a, 0n) == LT{} : Cmp}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      tc.cmp_lt(p, q, h)

def tc.cmp_gt(a: Nat, b: Nat, +h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.cmp(a, b) == GT{} : Cmp}:
  match a b:
    case 0n 0n:
      LBoolMisc.tree.pt.absurdF({Nat.cmp(0n, 0n) == GT{} : Cmp}, h)
    case 0n 1n+q:
      LBoolMisc.tree.pt.absurdF({Nat.cmp(0n, 1n+q) == GT{} : Cmp}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      tc.cmp_gt(p, q, h)

def tc.cmp_eq(a: Nat, b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {Nat.cmp(a, b) == EQ{} : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LBoolMisc.tree.pt.absurdF({Nat.cmp(0n, 1n+q) == EQ{} : Cmp}, h)
    case 1n+p 0n:
      LBoolMisc.tree.pt.absurdF({Nat.cmp(1n+p, 0n) == EQ{} : Cmp}, h)
    case 1n+p 1n+q:
      tc.cmp_eq(p, q, h)

def pj.sub_zero(c: Nat) -> {c == Nat.sub(c, 0n) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pj.min_of_le(n: Nat, m: Nat, h: {Nat.is_le(n, m) == True{} : Bool}) -> {n == Nat.min(n, m) : Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      LBoolMisc.pj.absurdF({1n+np == Nat.min(1n+np, 0n) : Nat}, h)
    case 1n+np 1n+mp:
      %pj.min_of_le(np, mp, h) : {1n+np == 1n+_ : Nat}
      {==}

def pf.ND(n: Nat, z: Type, s: Type) -> Type:
  match n:
    case 0n:
      z
    case 1n+p:
      s

def pf.succ_ne_zero(-A: Type, -n: Nat, e: {1n+n == 0n : Nat}) -> A:
  %e : pf.ND(_, A, Unit)
  Unit{}

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

def rp.ge_move(-a: Nat, -b: Nat, +c: Nat, e: {a == b : Nat}, h: {Nat.is_ge(a, c) == True{} : Bool}) -> {Nat.is_ge(b, c) == True{} : Bool}:
  %e : {Nat.is_ge(_, c) == True{} : Bool}
  h
