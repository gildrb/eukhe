# proof_run: the H4 laws of LAWS.bend about bend/run.bend.
#
# - run_ends: an explicit measure M (the inputs a run may still take) falls
#   by at least one at every input to a live run: lexicographically, the
#   rounds left, then the compactions, and the retries and notes left in
#   the generation (one budget u = a + n: each retry, noted or not, spends
#   one of them), the polls left, then the phase (prepare > call >
#   compact; tools ends the generation). M is that order written as one
#   number, in mixed radix, and M at the start is bound(cfg).
# - end_stays, abort_ends_now: by computation on each phase.
# - rounds_capped, rounds_fail_at_cap: invariants of every run and its
#   counted rounds, by induction on its inputs.
# - polls_need_defers: an invariant of the run and its deferred replies in
#   a row, by induction on its inputs.
# - no_answer, calls_never_answer, note_spends_no_retry,
#   retry_spends_no_note: by computation: Ended.reply makes a message with
#   a tool call Calls, whatever its text, and one with no text and no call
#   a noted Error; a noted Error spends a note, any other a retry.

import Base
import ./run.bend as R

# Logic
# -----

def BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : BD(_, A, Unit)
  Unit{}

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

# Numbers
# -------

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# a + (b + c) = b + (a + c)
def add_lcomm(+a: Nat, +b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  %add_assoc(a, b, c) : {_ == Nat.add(b, Nat.add(a, c)) : Nat}
  %Equal.sym(Nat, Nat.add(a, b), Nat.add(b, a), add_comm(a, b)) : {Nat.add(_, c) == Nat.add(b, Nat.add(a, c)) : Nat}
  add_assoc(b, a, c)

def add_succ_r(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  Equal.sym(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), add_succ(a, b))

def add_assoc_r(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), add_assoc(a, b, c))

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
def gen(+P: Nat, ph: R.Ph, c: Nat, u: Nat, p: Nat) -> Nat:
  match ph:
    case R.Prepare{}:
      Nat.add(Q(P), B(P, c, u))
    case R.Call{}:
      1n+Nat.add(p, B(P, c, u))
    case R.Compact{over}:
      1n+Nat.add(Q(P), B(P, c, u))
    case R.Tools{}:
      0n
    case R.Answered{}:
      0n
    case R.Aborted{}:
      0n
    case R.Failed{why}:
      0n

def G(+P: Nat, +U: Nat) -> Nat:
  1n+gen(P, R.Prepare{}, 1n, U, 0n)

def M.ph(+P: Nat, +U: Nat, ph: R.Ph, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> Nat:
  match ph:
    case R.Prepare{}:
      Nat.add(gen(P, R.Prepare{}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case R.Call{}:
      Nat.add(gen(P, R.Call{}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case R.Compact{over}:
      Nat.add(gen(P, R.Compact{over}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case R.Tools{}:
      Nat.add(gen(P, R.Tools{}, c, u, p), 1n+Nat.mul(r, G(P, U)))
    case R.Answered{}:
      0n
    case R.Aborted{}:
      0n
    case R.Failed{why}:
      0n

def M(+cfg: R.Cfg, s: R.St) -> Nat:
  match cfg s:
    case R.Cfg{cap, P, A, N} R.St{ph, r, c, a, n, p}:
      M.ph(P, Nat.add(A, N), ph, r, c, Nat.add(a, n), p)

# a fall within the generation is a fall of M
def lift(k: Nat, -gs: Nat, -gt: Nat, -X: Nat, e: {gs == Nat.add(k, 1n+gt) : Nat}) -> {Nat.add(gs, 1n+X) == Nat.add(k, 1n+Nat.add(gt, 1n+X)) : Nat}:
  %Equal.sym(Nat, gs, Nat.add(k, 1n+gt), e) : {Nat.add(_, 1n+X) == Nat.add(k, 1n+Nat.add(gt, 1n+X)) : Nat}
  add_assoc(k, 1n+gt, 1n+X)

# a run that ends takes no more inputs
def to_end(+gs: Nat, +X: Nat) -> {Nat.add(gs, 1n+X) == Nat.add(Nat.add(gs, X), 1n+0n) : Nat}:
  %add_succ_r(Nat.add(gs, X), 0n) : {Nat.add(gs, 1n+X) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(gs, X), 0n), Nat.add(gs, X), add_zero(Nat.add(gs, X))) : {Nat.add(gs, 1n+X) == 1n+_ : Nat}
  add_succ(gs, X)

# Each input
# ----------

# prepare -> compact: the generation's compaction
def prep_compact(+P: Nat, +d: Nat, +u: Nat) -> {gen(P, R.Prepare{}, 1n+d, u, 0n) == Nat.add(1n+P, 1n+gen(P, R.Compact{False{}}, d, u, 0n)) : Nat}:
  +mD = Nat.mul(d, 1n+Q(P))
  +mU = Nat.mul(u, Q(P))
  %add_assoc_r(1n+Q(P), mD, mU) : {Nat.add(Q(P), _) == Nat.add(1n+P, 1n+gen(P, R.Compact{False{}}, d, u, 0n)) : Nat}
  %add_succ_r(P, gen(P, R.Compact{False{}}, d, u, 0n)) : {Nat.add(Q(P), Nat.add(1n+Q(P), Nat.add(mD, mU))) == 1n+_ : Nat}
  {==}

# call -> tools: the generation's round starts
def call_tools(+X: Nat) -> {1n+X == Nat.add(X, 1n+0n) : Nat}:
  %add_succ_r(X, 0n) : {1n+X == _ : Nat}
  %add_zero(X) : {1n+_ == 1n+Nat.add(X, 0n) : Nat}
  {==}

# call -> prepare: a retry, noted or not
def call_retry(+P: Nat, +c: Nat, +b: Nat, +p: Nat) -> {gen(P, R.Call{}, c, 1n+b, p) == Nat.add(p, 1n+gen(P, R.Prepare{}, c, b, 0n)) : Nat}:
  +mC = Nat.mul(c, 1n+Q(P))
  +mb = Nat.mul(b, Q(P))
  %add_succ_r(p, gen(P, R.Prepare{}, c, b, 0n)) : {gen(P, R.Call{}, c, 1n+b, p) == _ : Nat}
  %add_lcomm(mC, Q(P), mb) : {gen(P, R.Call{}, c, 1n+b, p) == 1n+Nat.add(p, _) : Nat}
  {==}

# call -> prepare: a noted retry spends a note, a + (1 + m) = 1 + (a + m)
def call_note(+P: Nat, +c: Nat, +a: Nat, +m: Nat, +p: Nat) -> {gen(P, R.Call{}, c, Nat.add(a, 1n+m), p) == Nat.add(p, 1n+gen(P, R.Prepare{}, c, Nat.add(a, m), 0n)) : Nat}:
  %add_succ_r(a, m) : {gen(P, R.Call{}, c, _, p) == Nat.add(p, 1n+gen(P, R.Prepare{}, c, Nat.add(a, m), 0n)) : Nat}
  call_retry(P, c, Nat.add(a, m), p)

# call -> compact: an overflow's compaction
def call_compact(+P: Nat, +d: Nat, +u: Nat, +p: Nat) -> {gen(P, R.Call{}, 1n+d, u, p) == Nat.add(p, 1n+gen(P, R.Compact{True{}}, d, u, 0n)) : Nat}:
  +mD = Nat.mul(d, 1n+Q(P))
  +mU = Nat.mul(u, Q(P))
  %add_succ_r(p, gen(P, R.Compact{True{}}, d, u, 0n)) : {gen(P, R.Call{}, 1n+d, u, p) == _ : Nat}
  %add_assoc(1n+Q(P), mD, mU) : {gen(P, R.Call{}, 1n+d, u, p) == 1n+Nat.add(p, _) : Nat}
  {==}

# tools -> prepare: the next generation
def next_gen(+gp: Nat, +X: Nat) -> {Nat.add(0n, 1n+Nat.add(1n+gp, X)) == Nat.add(0n, 1n+Nat.add(gp, 1n+X)) : Nat}:
  %add_succ(gp, X) : {1n+_ == 1n+Nat.add(gp, 1n+X) : Nat}
  {==}

# Each phase
# ----------
# For a live run s and any input e, M falls: M(s) = k + 1 + M(step(s, e)),
# with k = K(cfg, s, e). Once a run ends, M is 0.

# M falls from s to t, by k + 1
def Fall(+cfg: R.Cfg, s: R.St, k: Nat, t: R.St) -> Type:
  {M(cfg, s) == Nat.add(k, 1n+M(cfg, t)) : Nat}

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

def dec_prepare_cut(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(R.Cfg{cap, P, A, N}, R.St{R.Prepare{}, r, c, a, n, p}, K.prepare_cut(P, cut, c), R.prepare.cut(R.Cfg{cap, P, A, N}, cut, r, c, a, n)):
  match cut c:
    case True{} 1n+d:
      lift(1n+P, gen(P, R.Prepare{}, 1n+d, Nat.add(a, n), p), gen(P, R.Compact{False{}}, d, Nat.add(a, n), P), X(P, Nat.add(A, N), r), prep_compact(P, d, Nat.add(a, n)))
    case True{} 0n:
      lift(0n, gen(P, R.Prepare{}, 0n, Nat.add(a, n), p), gen(P, R.Call{}, 0n, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})
    case False{} +c:
      lift(0n, gen(P, R.Prepare{}, c, Nat.add(a, n), p), gen(P, R.Call{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})

def K.prepare(+P: Nat, reply: R.Reply, c: Nat) -> Nat:
  match reply:
    case R.Overflow{cut}:
      K.prepare_cut(P, cut, c)
    case R.Text{}:
      0n
    case R.Calls{}:
      0n
    case R.Deferred{}:
      0n
    case R.Error{retryable, noted}:
      0n

def dec_prepare(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: R.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(R.Cfg{cap, P, A, N}, R.St{R.Prepare{}, r, c, a, n, p}, K.prepare(P, reply, c), R.prepare(R.Cfg{cap, P, A, N}, reply, r, c, a, n)):
  match reply:
    case R.Overflow{cut}:
      dec_prepare_cut(cap, P, A, N, cut, r, c, a, n, p)
    case R.Text{}:
      lift(0n, gen(P, R.Prepare{}, c, Nat.add(a, n), p), gen(P, R.Call{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})
    case R.Calls{}:
      lift(0n, gen(P, R.Prepare{}, c, Nat.add(a, n), p), gen(P, R.Call{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})
    case R.Deferred{}:
      lift(0n, gen(P, R.Prepare{}, c, Nat.add(a, n), p), gen(P, R.Call{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})
    case R.Error{retryable, noted}:
      lift(0n, gen(P, R.Prepare{}, c, Nat.add(a, n), p), gen(P, R.Call{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})

# the k of a call that ends the run
def K.call_end(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> Nat:
  Nat.add(gen(P, R.Call{}, c, u, p), X(P, U, r))

def call_end(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> {Nat.add(gen(P, R.Call{}, c, u, p), 1n+X(P, U, r)) == Nat.add(K.call_end(P, U, r, c, u, p), 1n+0n) : Nat}:
  to_end(gen(P, R.Call{}, c, u, p), X(P, U, r))

def K.retry(+P: Nat, +U: Nat, retryable: Bool, +r: Nat, +c: Nat, a: Nat, +n: Nat, +p: Nat) -> Nat:
  match retryable a:
    case True{} 1n+b:
      p
    case True{} 0n:
      K.call_end(P, U, r, c, Nat.add(0n, n), p)
    case False{} +a:
      K.call_end(P, U, r, c, Nat.add(a, n), p)

def dec_retry(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, +r: Nat, +c: Nat, a: Nat, +n: Nat, +p: Nat) -> Fall(R.Cfg{cap, P, A, N}, R.St{R.Call{}, r, c, a, n, p}, K.retry(P, Nat.add(A, N), retryable, r, c, a, n, p), R.retry(R.Cfg{cap, P, A, N}, retryable, r, c, a, n, p)):
  match retryable a:
    case True{} 1n+b:
      lift(p, gen(P, R.Call{}, c, Nat.add(1n+b, n), p), gen(P, R.Prepare{}, c, Nat.add(b, n), P), X(P, Nat.add(A, N), r), call_retry(P, c, Nat.add(b, n), p))
    case True{} 0n:
      call_end(P, Nat.add(A, N), r, c, Nat.add(0n, n), p)
    case False{} +a:
      call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), p)

def K.note(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +a: Nat, n: Nat, +p: Nat) -> Nat:
  match n:
    case 1n+m:
      p
    case 0n:
      K.call_end(P, U, r, c, Nat.add(a, 0n), p)

def dec_note(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +r: Nat, +c: Nat, +a: Nat, n: Nat, +p: Nat) -> Fall(R.Cfg{cap, P, A, N}, R.St{R.Call{}, r, c, a, n, p}, K.note(P, Nat.add(A, N), r, c, a, n, p), R.note(R.Cfg{cap, P, A, N}, r, c, a, n, p)):
  match n:
    case 1n+m:
      lift(p, gen(P, R.Call{}, c, Nat.add(a, 1n+m), p), gen(P, R.Prepare{}, c, Nat.add(a, m), P), X(P, Nat.add(A, N), r), call_note(P, c, a, m, p))
    case 0n:
      call_end(P, Nat.add(A, N), r, c, Nat.add(a, 0n), p)

def K.error(+P: Nat, +U: Nat, retryable: Bool, noted: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Nat:
  match noted:
    case True{}:
      K.note(P, U, r, c, a, n, p)
    case False{}:
      K.retry(P, U, retryable, r, c, a, n, p)

def dec_error(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, noted: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(R.Cfg{cap, P, A, N}, R.St{R.Call{}, r, c, a, n, p}, K.error(P, Nat.add(A, N), retryable, noted, r, c, a, n, p), R.error(R.Cfg{cap, P, A, N}, retryable, noted, r, c, a, n, p)):
  match noted:
    case True{}:
      dec_note(cap, P, A, N, r, c, a, n, p)
    case False{}:
      dec_retry(cap, P, A, N, retryable, r, c, a, n, p)

def K.overflow(+P: Nat, +U: Nat, cut: Bool, +r: Nat, c: Nat, +u: Nat, +p: Nat) -> Nat:
  match cut c:
    case True{} 1n+d:
      p
    case True{} 0n:
      K.call_end(P, U, r, 0n, u, p)
    case False{} +c:
      K.call_end(P, U, r, c, u, p)

def dec_overflow(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(R.Cfg{cap, P, A, N}, R.St{R.Call{}, r, c, a, n, p}, K.overflow(P, Nat.add(A, N), cut, r, c, Nat.add(a, n), p), R.overflow(cut, r, c, a, n, p)):
  match cut c:
    case True{} 1n+d:
      lift(p, gen(P, R.Call{}, 1n+d, Nat.add(a, n), p), gen(P, R.Compact{True{}}, d, Nat.add(a, n), p), X(P, Nat.add(A, N), r), call_compact(P, d, Nat.add(a, n), p))
    case True{} 0n:
      call_end(P, Nat.add(A, N), r, 0n, Nat.add(a, n), p)
    case False{} +c:
      call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), p)

def K.deferred(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +u: Nat, p: Nat) -> Nat:
  match p:
    case 0n:
      K.call_end(P, U, r, c, u, 0n)
    case 1n+q:
      0n

def dec_deferred(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +r: Nat, +c: Nat, +a: Nat, +n: Nat, p: Nat) -> Fall(R.Cfg{cap, P, A, N}, R.St{R.Call{}, r, c, a, n, p}, K.deferred(P, Nat.add(A, N), r, c, Nat.add(a, n), p), R.call(R.Cfg{cap, P, A, N}, R.Deferred{}, r, c, a, n, p)):
  match p:
    case 0n:
      call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), 0n)
    case 1n+q:
      lift(0n, gen(P, R.Call{}, c, Nat.add(a, n), 1n+q), gen(P, R.Call{}, c, Nat.add(a, n), q), X(P, Nat.add(A, N), r), {==})

def K.call(+P: Nat, +U: Nat, reply: R.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Nat:
  match reply:
    case R.Text{}:
      K.call_end(P, U, r, c, Nat.add(a, n), p)
    case R.Calls{}:
      Nat.add(p, B(P, c, Nat.add(a, n)))
    case R.Deferred{}:
      K.deferred(P, U, r, c, Nat.add(a, n), p)
    case R.Error{retryable, noted}:
      K.error(P, U, retryable, noted, r, c, a, n, p)
    case R.Overflow{cut}:
      K.overflow(P, U, cut, r, c, Nat.add(a, n), p)

def dec_call(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: R.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(R.Cfg{cap, P, A, N}, R.St{R.Call{}, r, c, a, n, p}, K.call(P, Nat.add(A, N), reply, r, c, a, n, p), R.call(R.Cfg{cap, P, A, N}, reply, r, c, a, n, p)):
  match reply:
    case R.Text{}:
      call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), p)
    case R.Calls{}:
      lift(Nat.add(p, B(P, c, Nat.add(a, n))), gen(P, R.Call{}, c, Nat.add(a, n), p), 0n, X(P, Nat.add(A, N), r), call_tools(Nat.add(p, B(P, c, Nat.add(a, n)))))
    case R.Deferred{}:
      dec_deferred(cap, P, A, N, r, c, a, n, p)
    case R.Error{retryable, noted}:
      dec_error(cap, P, A, N, retryable, noted, r, c, a, n, p)
    case R.Overflow{cut}:
      dec_overflow(cap, P, A, N, cut, r, c, a, n, p)

def K.compact(+P: Nat, +U: Nat, over: Bool, got: R.Got, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> Nat:
  match over got:
    case over R.Built{}:
      0n
    case True{} R.Kept{}:
      Nat.add(gen(P, R.Compact{True{}}, c, u, p), X(P, U, r))
    case False{} R.Kept{}:
      0n
    case over R.Broke{}:
      Nat.add(gen(P, R.Compact{over}, c, u, p), X(P, U, r))

def dec_compact(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +over: Bool, got: R.Got, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(R.Cfg{cap, P, A, N}, R.St{R.Compact{over}, r, c, a, n, p}, K.compact(P, Nat.add(A, N), over, got, r, c, Nat.add(a, n), p), R.compact(R.Cfg{cap, P, A, N}, over, got, r, c, a, n, p)):
  match over got:
    case over R.Built{}:
      lift(0n, gen(P, R.Compact{over}, c, Nat.add(a, n), p), gen(P, R.Prepare{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})
    case True{} R.Kept{}:
      to_end(gen(P, R.Compact{True{}}, c, Nat.add(a, n), p), X(P, Nat.add(A, N), r))
    case False{} R.Kept{}:
      lift(0n, gen(P, R.Compact{False{}}, c, Nat.add(a, n), p), gen(P, R.Prepare{}, c, Nat.add(a, n), P), X(P, Nat.add(A, N), r), {==})
    case over R.Broke{}:
      to_end(gen(P, R.Compact{over}, c, Nat.add(a, n), p), X(P, Nat.add(A, N), r))

def K.round(+P: Nat, +U: Nat, reset: Bool, r: Nat) -> Nat:
  match reset r:
    case reset 0n:
      Nat.add(0n, X(P, U, 0n))
    case True{} 1n+s:
      Nat.add(0n, X(P, U, 1n+s))
    case False{} 1n+s:
      0n

def dec_round(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reset: Bool, r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(R.Cfg{cap, P, A, N}, R.St{R.Tools{}, r, c, a, n, p}, K.round(P, Nat.add(A, N), reset, r), R.round(R.Cfg{cap, P, A, N}, reset, r, c, a, n, p)):
  match reset r:
    case reset 0n:
      to_end(0n, X(P, Nat.add(A, N), 0n))
    case True{} 1n+s:
      to_end(0n, X(P, Nat.add(A, N), 1n+s))
    case False{} 1n+s:
      next_gen(gen(P, R.Prepare{}, 1n, Nat.add(A, N), 0n), X(P, Nat.add(A, N), s))

def K.tools(+P: Nat, +U: Nat, fin: R.Fin, +r: Nat) -> Nat:
  match fin:
    case R.Stops{}:
      Nat.add(0n, X(P, U, r))
    case R.Goes{}:
      K.round(P, U, False{}, r)
    case R.Resets{}:
      K.round(P, U, True{}, r)

def dec_tools(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, fin: R.Fin, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> Fall(R.Cfg{cap, P, A, N}, R.St{R.Tools{}, r, c, a, n, p}, K.tools(P, Nat.add(A, N), fin, r), R.tools(R.Cfg{cap, P, A, N}, fin, r, c, a, n, p)):
  match fin:
    case R.Stops{}:
      to_end(0n, X(P, Nat.add(A, N), r))
    case R.Goes{}:
      dec_round(cap, P, A, N, False{}, r, c, a, n, p)
    case R.Resets{}:
      dec_round(cap, P, A, N, True{}, r, c, a, n, p)

# k for any input
def K(+cfg: R.Cfg, s: R.St, e: R.Ev) -> Nat:
  match cfg s:
    case R.Cfg{cap, P, A, N} R.St{ph, r, c, a, n, p}:
      match ph e:
        case R.Answered{} e:
          0n
        case R.Aborted{} e:
          0n
        case R.Failed{why} e:
          0n
        case R.Prepare{} R.Abort{}:
          Nat.add(gen(P, R.Prepare{}, c, Nat.add(a, n), p), X(P, Nat.add(A, N), r))
        case R.Call{} R.Abort{}:
          K.call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), p)
        case R.Compact{over} R.Abort{}:
          Nat.add(gen(P, R.Compact{over}, c, Nat.add(a, n), p), X(P, Nat.add(A, N), r))
        case R.Tools{} R.Abort{}:
          Nat.add(0n, X(P, Nat.add(A, N), r))
        case R.Prepare{} R.Go{reply, fin, got}:
          K.prepare(P, reply, c)
        case R.Call{} R.Go{reply, fin, got}:
          K.call(P, Nat.add(A, N), reply, r, c, a, n, p)
        case R.Compact{over} R.Go{reply, fin, got}:
          K.compact(P, Nat.add(A, N), over, got, r, c, Nat.add(a, n), p)
        case R.Tools{} R.Go{reply, fin, got}:
          K.tools(P, Nat.add(A, N), fin, r)

# the goal of dec at a phase
def FallAt(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +ph: R.Ph, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +e: R.Ev) -> Type:
  Fall(R.Cfg{cap, P, A, N}, R.St{ph, r, c, a, n, p}, K(R.Cfg{cap, P, A, N}, R.St{ph, r, c, a, n, p}, e), R.step(R.Cfg{cap, P, A, N}, R.St{ph, r, c, a, n, p}, e))

# every input to a live run lowers M
def dec(+cfg: R.Cfg, +s: R.St, +e: R.Ev, nd: {R.done(s) == False{} : Bool}) -> Fall(cfg, s, K(cfg, s, e), R.step(cfg, s, e)):
  match cfg:
    case R.Cfg{cap, P, A, N}:
      match s:
        case R.St{ph, r, c, a, n, p}:
          match ph e:
            case R.Answered{} e:
              absurd(FallAt(cap, P, A, N, R.Answered{}, r, c, a, n, p, e), Equal.sym(Bool, True{}, False{}, nd))
            case R.Aborted{} e:
              absurd(FallAt(cap, P, A, N, R.Aborted{}, r, c, a, n, p, e), Equal.sym(Bool, True{}, False{}, nd))
            case R.Failed{why} e:
              absurd(FallAt(cap, P, A, N, R.Failed{why}, r, c, a, n, p, e), Equal.sym(Bool, True{}, False{}, nd))
            case R.Prepare{} R.Abort{}:
              to_end(gen(P, R.Prepare{}, c, Nat.add(a, n), p), X(P, Nat.add(A, N), r))
            case R.Call{} R.Abort{}:
              call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), p)
            case R.Compact{over} R.Abort{}:
              to_end(gen(P, R.Compact{over}, c, Nat.add(a, n), p), X(P, Nat.add(A, N), r))
            case R.Tools{} R.Abort{}:
              to_end(0n, X(P, Nat.add(A, N), r))
            case R.Prepare{} R.Go{reply, fin, got}:
              dec_prepare(cap, P, A, N, reply, r, c, a, n, p)
            case R.Call{} R.Go{reply, fin, got}:
              dec_call(cap, P, A, N, reply, r, c, a, n, p)
            case R.Compact{over} R.Go{reply, fin, got}:
              dec_compact(cap, P, A, N, over, got, r, c, a, n, p)
            case R.Tools{} R.Go{reply, fin, got}:
              dec_tools(cap, P, A, N, fin, r, c, a, n, p)

# The run ends
# ------------

# an ended run stays as it is
def end_stays(+cfg: R.Cfg, s: R.St, e: R.Ev, d: {R.done(s) == True{} : Bool}) -> {R.step(cfg, s, e) == s : R.St}:
  match s:
    case R.St{ph, r, c, a, n, p}:
      match ph:
        case R.Answered{}:
          {==}
        case R.Aborted{}:
          {==}
        case R.Failed{why}:
          {==}
        case R.Prepare{}:
          absurd({R.step(cfg, R.St{R.Prepare{}, r, c, a, n, p}, e) == R.St{R.Prepare{}, r, c, a, n, p} : R.St}, d)
        case R.Call{}:
          absurd({R.step(cfg, R.St{R.Call{}, r, c, a, n, p}, e) == R.St{R.Call{}, r, c, a, n, p} : R.St}, d)
        case R.Compact{over}:
          absurd({R.step(cfg, R.St{R.Compact{over}, r, c, a, n, p}, e) == R.St{R.Compact{over}, r, c, a, n, p} : R.St}, d)
        case R.Tools{}:
          absurd({R.step(cfg, R.St{R.Tools{}, r, c, a, n, p}, e) == R.St{R.Tools{}, r, c, a, n, p} : R.St}, d)

def stays_done(evs: List<&2, R.Ev>, +cfg: R.Cfg, +s: R.St, +d: {R.done(s) == True{} : Bool}) -> {R.done(R.run.go(evs, cfg, s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      d
    case e <> rest:
      %Equal.sym(R.St, R.step(cfg, s, e), s, end_stays(cfg, s, e, d)) : {R.done(R.run.go(rest, cfg, _)) == True{} : Bool}
      stays_done(rest, cfg, s, d)

def succ_m(+j: Nat, +g: Nat, +X: Nat) -> {Nat.add(j, Nat.add(g, 1n+X)) == 1n+Nat.add(j, Nat.add(g, X)) : Nat}:
  %add_succ_r(g, X) : {Nat.add(j, _) == 1n+Nat.add(j, Nat.add(g, X)) : Nat}
  add_succ(j, Nat.add(g, X))

# a live run may still take an input
def pos(-T: Type, +j: Nat, +g: Nat, +X: Nat, h: {0n == Nat.add(j, Nat.add(g, 1n+X)) : Nat}) -> T:
  zero_succ(T, Nat.add(j, Nat.add(g, X)), Equal.trans(Nat, 0n, Nat.add(j, Nat.add(g, 1n+X)), 1n+Nat.add(j, Nat.add(g, X)), h, succ_m(j, g, X)))

# with no input left, the run has ended
def nil_done(+cfg: R.Cfg, +s: R.St, +j: Nat, h: {0n == Nat.add(j, M(cfg, s)) : Nat}) -> {R.done(s) == True{} : Bool}:
  match cfg:
    case R.Cfg{cap, P, A, N}:
      match s:
        case R.St{ph, r, c, a, n, p}:
          match ph:
            case R.Prepare{}:
              pos({R.done(R.St{R.Prepare{}, r, c, a, n, p}) == True{} : Bool}, j, gen(P, R.Prepare{}, c, Nat.add(a, n), p), Nat.mul(r, G(P, Nat.add(A, N))), h)
            case R.Call{}:
              pos({R.done(R.St{R.Call{}, r, c, a, n, p}) == True{} : Bool}, j, gen(P, R.Call{}, c, Nat.add(a, n), p), Nat.mul(r, G(P, Nat.add(A, N))), h)
            case R.Compact{over}:
              pos({R.done(R.St{R.Compact{over}, r, c, a, n, p}) == True{} : Bool}, j, gen(P, R.Compact{over}, c, Nat.add(a, n), p), Nat.mul(r, G(P, Nat.add(A, N))), h)
            case R.Tools{}:
              pos({R.done(R.St{R.Tools{}, r, c, a, n, p}) == True{} : Bool}, j, 0n, Nat.mul(r, G(P, Nat.add(A, N))), h)
            case R.Answered{}:
              {==}
            case R.Aborted{}:
              {==}
            case R.Failed{why}:
              {==}

def next_len1(-n: Nat, +j: Nat, +k: Nat, -ms: Nat, -mt: Nat, h: {1n+n == Nat.add(j, ms) : Nat}, eq: {ms == Nat.add(k, 1n+mt) : Nat}) -> {1n+n == 1n+Nat.add(Nat.add(j, k), mt) : Nat}:
  %add_succ(Nat.add(j, k), mt) : {1n+n == _ : Nat}
  %add_assoc_r(j, k, 1n+mt) : {1n+n == _ : Nat}
  %eq : {1n+n == Nat.add(j, _) : Nat}
  h

# one input later, the inputs left still cover M
def next_len(+cfg: R.Cfg, +s: R.St, +e: R.Ev, +j: Nat, -rest: List<&2, R.Ev>, h: {1n+List.length(&2, R.Ev, rest) == Nat.add(j, M(cfg, s)) : Nat}, nd: {R.done(s) == False{} : Bool}) -> {List.length(&2, R.Ev, rest) == Nat.add(Nat.add(j, K(cfg, s, e)), M(cfg, R.step(cfg, s, e))) : Nat}:
  succ_inj(List.length(&2, R.Ev, rest), Nat.add(Nat.add(j, K(cfg, s, e)), M(cfg, R.step(cfg, s, e))), next_len1(List.length(&2, R.Ev, rest), j, K(cfg, s, e), M(cfg, s), M(cfg, R.step(cfg, s, e)), h, dec(cfg, s, e, nd)))

# a run whose inputs cover M has ended after them
def ends(evs: List<&2, R.Ev>, +cfg: R.Cfg, +s: R.St, +j: Nat, h: {List.length(&2, R.Ev, evs) == Nat.add(j, M(cfg, s)) : Nat}) -> {R.done(R.run.go(evs, cfg, s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      nil_done(cfg, s, j, h)
    case +e <> rest:
      match s:
        case R.St{ph, r, c, a, n, p}:
          match ph:
            case R.Prepare{}:
              +t = {R.St{R.Prepare{}, r, c, a, n, p} : R.St}
              ends(rest, cfg, R.step(cfg, t, e), Nat.add(j, K(cfg, t, e)), next_len(cfg, t, e, j, rest, h, {==}))
            case R.Call{}:
              +t = {R.St{R.Call{}, r, c, a, n, p} : R.St}
              ends(rest, cfg, R.step(cfg, t, e), Nat.add(j, K(cfg, t, e)), next_len(cfg, t, e, j, rest, h, {==}))
            case R.Compact{over}:
              +t = {R.St{R.Compact{over}, r, c, a, n, p} : R.St}
              ends(rest, cfg, R.step(cfg, t, e), Nat.add(j, K(cfg, t, e)), next_len(cfg, t, e, j, rest, h, {==}))
            case R.Tools{}:
              +t = {R.St{R.Tools{}, r, c, a, n, p} : R.St}
              ends(rest, cfg, R.step(cfg, t, e), Nat.add(j, K(cfg, t, e)), next_len(cfg, t, e, j, rest, h, {==}))
            case R.Answered{}:
              stays_done(rest, cfg, R.St{R.Answered{}, r, c, a, n, p}, {==})
            case R.Aborted{}:
              stays_done(rest, cfg, R.St{R.Aborted{}, r, c, a, n, p}, {==})
            case R.Failed{why}:
              stays_done(rest, cfg, R.St{R.Failed{why}, r, c, a, n, p}, {==})

# The bound
# ---------

# a generation: 2 + (U + 2)·(polls + 2), U = retries + notes
def G_eq(+P: Nat, +U: Nat) -> {G(P, U) == 2n+Nat.mul(2n+U, 2n+P) : Nat}:
  +Y = Nat.add(P, Nat.mul(U, Q(P)))
  %Equal.sym(Nat, Nat.add(P, 0n), P, add_zero(P)) : {1n+Nat.add(Q(P), Nat.add(3n+_, Nat.mul(U, Q(P)))) == 2n+Nat.mul(2n+U, 2n+P) : Nat}
  %Equal.sym(Nat, Nat.add(P, Nat.add(3n, Y)), Nat.add(3n, Nat.add(P, Y)), add_lcomm(P, 3n, Y)) : {3n+_ == 2n+Nat.mul(2n+U, 2n+P) : Nat}
  %Equal.sym(Nat, Nat.add(P, Nat.add(2n, Y)), Nat.add(2n, Nat.add(P, Y)), add_lcomm(P, 2n, Y)) : {6n+Nat.add(P, Y) == 4n+_ : Nat}
  {==}

# max(cap, 1) = 1 + (cap - 1)
def max1(cap: Nat) -> {Nat.max(cap, 1n) == 1n+Nat.sub(cap, 1n) : Nat}:
  match cap:
    case 0n:
      {==}
    case 1n+k:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}

# bound(cfg) is M at the start
def bound_m(+cfg: R.Cfg) -> {R.bound(cfg) == M(cfg, R.init(cfg)) : Nat}:
  match cfg:
    case R.Cfg{cap, P, A, N}:
      +U = Nat.add(A, N)
      +gp = gen(P, R.Prepare{}, 1n, U, 0n)
      +r0 = Nat.sub(cap, 1n)
      %G_eq(P, U) : {Nat.mul(Nat.max(cap, 1n), _) == M(R.Cfg{cap, P, A, N}, R.init(R.Cfg{cap, P, A, N})) : Nat}
      %Equal.sym(Nat, Nat.max(cap, 1n), 1n+r0, max1(cap)) : {Nat.mul(_, G(P, U)) == M(R.Cfg{cap, P, A, N}, R.init(R.Cfg{cap, P, A, N})) : Nat}
      %add_succ(gp, Nat.mul(r0, G(P, U))) : {_ == Nat.add(gp, 1n+Nat.mul(r0, G(P, U))) : Nat}
      {==}

def run_append(xs: List<&2, R.Ev>, -ys: List<&2, R.Ev>, +cfg: R.Cfg, +s: R.St) -> {R.run.go(List.append(&2, R.Ev, xs, ys), cfg, s) == R.run.go(ys, cfg, R.run.go(xs, cfg, s)) : R.St}:
  match xs:
    case Nil{}:
      {==}
    case e <> rest:
      run_append(rest, ys, cfg, R.step(cfg, s, e))

# The invariant
# -------------
# After any inputs, with k the counted rounds: the cap ended the run only
# after max(cap, 1) rounds; and a run that did not fail has made
# cap - 1 - r rounds.

def Inv(+cap: Nat, +ph: R.Ph, +r: Nat, +k: Nat) -> Type:
  Or({R.Ph.capped(ph) == False{} : Bool}, {k == Nat.max(cap, 1n) : Nat}) & Or({R.Ph.failed(ph) == True{} : Bool}, {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat})

def InvS(+cfg: R.Cfg, +s: R.St, +k: Nat) -> Type:
  Inv(R.Cfg.cap(cfg), R.St.ph(s), R.St.r(s), k)

# a live run has not failed
def cap_of(-T: Type, o: Or({False{} == True{} : Bool}, T)) -> T:
  match o:
    case Inl{x}:
      absurd(T, x)
    case Inr{y}:
      y

def eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

def cap_next(n: Nat, -s: Nat, -cap: Nat, capv: {Nat.add(n, 2n+s) == cap : Nat}) -> {1n+Nat.add(n, 1n+s) == cap : Nat}:
  %capv : {1n+Nat.add(n, 1n+s) == _ : Nat}
  add_succ_r(n, 1n+s)

# the round that meets the cap is the max(cap, 1)th
def one_more(+n: Nat, -m: Nat, capv: {Nat.add(n, 1n+0n) == m : Nat}) -> {1n+n == m : Nat}:
  %capv : {1n+n == _ : Nat}
  %add_succ_r(n, 0n) : {1n+n == _ : Nat}
  %Equal.sym(Nat, Nat.add(n, 0n), n, add_zero(n)) : {1n+n == 1n+_ : Nat}
  {==}

def inv_round(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reset: Bool, r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(R.Cfg{cap, P, A, N}, R.round(R.Cfg{cap, P, A, N}, reset, r, c, a, n, p), 1n+k):
  match reset r:
    case reset 0n:
      (Inr{one_more(k, Nat.max(cap, 1n), capv)}, Inl{{==}})
    case True{} 1n+s:
      (Inl{{==}}, Inr{cap_next(k, s, Nat.max(cap, 1n), capv)})
    case False{} 1n+s:
      (Inl{{==}}, Inr{cap_next(k, s, Nat.max(cap, 1n), capv)})

def inv_tools(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, fin: R.Fin, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(R.Cfg{cap, P, A, N}, R.tools(R.Cfg{cap, P, A, N}, fin, r, c, a, n, p), R.counted.go(fin, k)):
  match fin:
    case R.Stops{}:
      (Inl{{==}}, Inr{capv})
    case R.Goes{}:
      inv_round(cap, P, A, N, False{}, r, c, a, n, p, k, capv)
    case R.Resets{}:
      inv_round(cap, P, A, N, True{}, r, c, a, n, p, k, capv)

def inv_prepare_cut(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(R.Cfg{cap, P, A, N}, R.prepare.cut(R.Cfg{cap, P, A, N}, cut, r, c, a, n), k):
  match cut c:
    case True{} 1n+d:
      (Inl{{==}}, Inr{capv})
    case True{} 0n:
      (Inl{{==}}, Inr{capv})
    case False{} c:
      (Inl{{==}}, Inr{capv})

def inv_prepare(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: R.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(R.Cfg{cap, P, A, N}, R.prepare(R.Cfg{cap, P, A, N}, reply, r, c, a, n), k):
  match reply:
    case R.Overflow{cut}:
      inv_prepare_cut(cap, P, A, N, cut, r, c, a, n, k, capv)
    case R.Text{}:
      (Inl{{==}}, Inr{capv})
    case R.Calls{}:
      (Inl{{==}}, Inr{capv})
    case R.Deferred{}:
      (Inl{{==}}, Inr{capv})
    case R.Error{retryable, noted}:
      (Inl{{==}}, Inr{capv})

def inv_retry(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, +r: Nat, +c: Nat, a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(R.Cfg{cap, P, A, N}, R.retry(R.Cfg{cap, P, A, N}, retryable, r, c, a, n, p), k):
  match retryable a:
    case True{} 1n+b:
      (Inl{{==}}, Inr{capv})
    case True{} 0n:
      (Inl{{==}}, Inl{{==}})
    case False{} a:
      (Inl{{==}}, Inl{{==}})

def inv_note(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +r: Nat, +c: Nat, +a: Nat, n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(R.Cfg{cap, P, A, N}, R.note(R.Cfg{cap, P, A, N}, r, c, a, n, p), k):
  match n:
    case 1n+m:
      (Inl{{==}}, Inr{capv})
    case 0n:
      (Inl{{==}}, Inl{{==}})

def inv_error(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, noted: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(R.Cfg{cap, P, A, N}, R.error(R.Cfg{cap, P, A, N}, retryable, noted, r, c, a, n, p), k):
  match noted:
    case True{}:
      inv_note(cap, P, A, N, r, c, a, n, p, k, capv)
    case False{}:
      inv_retry(cap, P, A, N, retryable, r, c, a, n, p, k, capv)

def inv_overflow(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(R.Cfg{cap, P, A, N}, R.overflow(cut, r, c, a, n, p), k):
  match cut c:
    case True{} 1n+d:
      (Inl{{==}}, Inr{capv})
    case True{} 0n:
      (Inl{{==}}, Inl{{==}})
    case False{} c:
      (Inl{{==}}, Inl{{==}})

def inv_call(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: R.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(R.Cfg{cap, P, A, N}, R.call(R.Cfg{cap, P, A, N}, reply, r, c, a, n, p), k):
  match reply:
    case R.Text{}:
      (Inl{{==}}, Inr{capv})
    case R.Calls{}:
      (Inl{{==}}, Inr{capv})
    case R.Deferred{}:
      match p:
        case 0n:
          (Inl{{==}}, Inl{{==}})
        case 1n+q:
          (Inl{{==}}, Inr{capv})
    case R.Error{retryable, noted}:
      inv_error(cap, P, A, N, retryable, noted, r, c, a, n, p, k, capv)
    case R.Overflow{cut}:
      inv_overflow(cap, P, A, N, cut, r, c, a, n, p, k, capv)

def inv_compact(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, over: Bool, got: R.Got, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(R.Cfg{cap, P, A, N}, R.compact(R.Cfg{cap, P, A, N}, over, got, r, c, a, n, p), k):
  match over got:
    case over R.Built{}:
      (Inl{{==}}, Inr{capv})
    case True{} R.Kept{}:
      (Inl{{==}}, Inl{{==}})
    case False{} R.Kept{}:
      (Inl{{==}}, Inr{capv})
    case over R.Broke{}:
      (Inl{{==}}, Inl{{==}})

# one input keeps the invariant
def inv_step(+cfg: R.Cfg, +s: R.St, +k: Nat, +e: R.Ev, i: InvS(cfg, s, k)) -> InvS(cfg, R.step(cfg, s, e), R.counted(R.St.ph(s), e, k)):
  match cfg:
    case R.Cfg{cap, P, A, N}:
      match s:
        case R.St{ph, r, c, a, n, p}:
          match ph e:
            case R.Answered{} e:
              i
            case R.Aborted{} e:
              i
            case R.Failed{why} e:
              i
            case R.Prepare{} R.Abort{}:
              (cp, co) = i
              (Inl{{==}}, Inr{cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co)})
            case R.Call{} R.Abort{}:
              (cp, co) = i
              (Inl{{==}}, Inr{cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co)})
            case R.Compact{over} R.Abort{}:
              (cp, co) = i
              (Inl{{==}}, Inr{cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co)})
            case R.Tools{} R.Abort{}:
              (cp, co) = i
              (Inl{{==}}, Inr{cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co)})
            case R.Prepare{} R.Go{reply, fin, got}:
              (cp, co) = i
              inv_prepare(cap, P, A, N, reply, r, c, a, n, k, cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co))
            case R.Call{} R.Go{reply, fin, got}:
              (cp, co) = i
              inv_call(cap, P, A, N, reply, r, c, a, n, p, k, cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co))
            case R.Compact{over} R.Go{reply, fin, got}:
              (cp, co) = i
              inv_compact(cap, P, A, N, over, got, r, c, a, n, p, k, cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co))
            case R.Tools{} R.Go{reply, fin, got}:
              (cp, co) = i
              inv_tools(cap, P, A, N, fin, r, c, a, n, p, k, cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co))

def inv_run(evs: List<&2, R.Ev>, +cfg: R.Cfg, +s: R.St, +k: Nat, i: InvS(cfg, s, k)) -> InvS(cfg, R.run.go(evs, cfg, s), R.rounds.go(evs, cfg, s, k)):
  match evs:
    case Nil{}:
      i
    case +e <> rest:
      inv_run(rest, cfg, R.step(cfg, s, e), R.counted(R.St.ph(s), e, k), inv_step(cfg, s, k, e, i))

# a run starts with the invariant
def inv_init(+cfg: R.Cfg) -> InvS(cfg, R.init(cfg), 0n):
  match cfg:
    case R.Cfg{cap, P, A, N}:
      (Inl{{==}}, Inr{Equal.sym(Nat, Nat.max(cap, 1n), 1n+Nat.sub(cap, 1n), max1(cap))})

# The laws' conclusions
# ---------------------

def lt_add(x: Nat, -r: Nat) -> {Nat.is_lt(x, Nat.add(x, 1n+r)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+y:
      lt_add(y, r)

def lt_of(n: Nat, -r: Nat, -cap: Nat, eq: {Nat.add(n, 1n+r) == cap : Nat}) -> {Nat.is_lt(n, cap) == True{} : Bool}:
  %eq : {Nat.is_lt(n, _) == True{} : Bool}
  lt_add(n, r)

# a run that did not fail made fewer than max(cap, 1) rounds
def rounds_of(+cfg: R.Cfg, +s: R.St, +k: Nat, i: InvS(cfg, s, k)) -> Or({R.failed(s) == True{} : Bool}, {Nat.is_lt(k, Nat.max(R.Cfg.cap(cfg), 1n)) == True{} : Bool}):
  (cp, co) = i
  match co:
    case Inl{f}:
      Inl{f}
    case Inr{eq}:
      Inr{lt_of(k, R.St.r(s), Nat.max(R.Cfg.cap(cfg), 1n), eq)}

# a run the cap failed made max(cap, 1) rounds
def caps_of(+cfg: R.Cfg, +s: R.St, +k: Nat, i: InvS(cfg, s, k)) -> Or({R.capped(s) == False{} : Bool}, {k == Nat.max(R.Cfg.cap(cfg), 1n) : Nat}):
  (cp, co) = i
  cp

# The polls
# ---------
# After any inputs, with k = the deferred replies in a row: in a call,
# k + p = polls (the polls left and the deferred replies so far make the
# cap); a run the poll cap failed had k = polls + 1.

def PInv.why(+P: Nat, why: R.Why, +k: Nat) -> Type:
  match why:
    case R.Polls{}:
      {k == 1n+P : Nat}
    case R.Model{}:
      Unit
    case R.Rounds{}:
      Unit

def PInv.ph(+P: Nat, ph: R.Ph, +p: Nat, +k: Nat) -> Type:
  match ph:
    case R.Call{}:
      {Nat.add(k, p) == P : Nat}
    case R.Failed{why}:
      PInv.why(P, why, k)
    case R.Prepare{}:
      Unit
    case R.Compact{over}:
      Unit
    case R.Tools{}:
      Unit
    case R.Answered{}:
      Unit
    case R.Aborted{}:
      Unit

def PInv(+cfg: R.Cfg, +s: R.St, +k: Nat) -> Type:
  PInv.ph(R.Cfg.polls(cfg), R.St.ph(s), R.St.p(s), k)

def pinv_prepare_cut(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat) -> PInv(R.Cfg{cap, P, A, N}, R.prepare.cut(R.Cfg{cap, P, A, N}, cut, r, c, a, n), 0n):
  match cut c:
    case True{} 1n+d:
      Unit{}
    case True{} 0n:
      {==}
    case False{} c:
      {==}

def pinv_prepare(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: R.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat) -> PInv(R.Cfg{cap, P, A, N}, R.prepare(R.Cfg{cap, P, A, N}, reply, r, c, a, n), 0n):
  match reply:
    case R.Overflow{cut}:
      pinv_prepare_cut(cap, P, A, N, cut, r, c, a, n)
    case R.Text{}:
      {==}
    case R.Calls{}:
      {==}
    case R.Deferred{}:
      {==}
    case R.Error{retryable, noted}:
      {==}

def pinv_retry(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, +r: Nat, +c: Nat, a: Nat, +n: Nat, +p: Nat) -> PInv(R.Cfg{cap, P, A, N}, R.retry(R.Cfg{cap, P, A, N}, retryable, r, c, a, n, p), 0n):
  match retryable a:
    case True{} 1n+b:
      Unit{}
    case True{} 0n:
      Unit{}
    case False{} a:
      Unit{}

def pinv_note(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +r: Nat, +c: Nat, +a: Nat, n: Nat, +p: Nat) -> PInv(R.Cfg{cap, P, A, N}, R.note(R.Cfg{cap, P, A, N}, r, c, a, n, p), 0n):
  match n:
    case 1n+m:
      Unit{}
    case 0n:
      Unit{}

def pinv_error(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, noted: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(R.Cfg{cap, P, A, N}, R.error(R.Cfg{cap, P, A, N}, retryable, noted, r, c, a, n, p), 0n):
  match noted:
    case True{}:
      pinv_note(cap, P, A, N, r, c, a, n, p)
    case False{}:
      pinv_retry(cap, P, A, N, retryable, r, c, a, n, p)

def pinv_overflow(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(R.Cfg{cap, P, A, N}, R.overflow(cut, r, c, a, n, p), 0n):
  match cut c:
    case True{} 1n+d:
      Unit{}
    case True{} 0n:
      Unit{}
    case False{} c:
      Unit{}

# the last poll's deferred reply makes polls + 1 in a row
def polls_full(+k: Nat, -P: Nat, i: {Nat.add(k, 0n) == P : Nat}) -> {1n+k == 1n+P : Nat}:
  %i : {1n+k == 1n+_ : Nat}
  %Equal.sym(Nat, Nat.add(k, 0n), k, add_zero(k)) : {1n+k == 1n+_ : Nat}
  {==}

def pinv_call(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: R.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, p: Nat, +k: Nat, i: {Nat.add(k, p) == P : Nat}) -> PInv(R.Cfg{cap, P, A, N}, R.call(R.Cfg{cap, P, A, N}, reply, r, c, a, n, p), R.defers.reply(reply, k)):
  match reply:
    case R.Text{}:
      Unit{}
    case R.Calls{}:
      Unit{}
    case R.Deferred{}:
      match p:
        case 0n:
          polls_full(k, P, i)
        case 1n+q:
          %i : {1n+Nat.add(k, q) == _ : Nat}
          add_succ_r(k, q)
    case R.Error{retryable, noted}:
      pinv_error(cap, P, A, N, retryable, noted, r, c, a, n, p)
    case R.Overflow{cut}:
      pinv_overflow(cap, P, A, N, cut, r, c, a, n, p)

def pinv_compact(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, over: Bool, got: R.Got, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(R.Cfg{cap, P, A, N}, R.compact(R.Cfg{cap, P, A, N}, over, got, r, c, a, n, p), 0n):
  match over got:
    case over R.Built{}:
      Unit{}
    case True{} R.Kept{}:
      Unit{}
    case False{} R.Kept{}:
      Unit{}
    case over R.Broke{}:
      Unit{}

def pinv_round(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reset: Bool, r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(R.Cfg{cap, P, A, N}, R.round(R.Cfg{cap, P, A, N}, reset, r, c, a, n, p), 0n):
  match reset r:
    case reset 0n:
      Unit{}
    case True{} 1n+s:
      Unit{}
    case False{} 1n+s:
      Unit{}

def pinv_tools(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, fin: R.Fin, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> PInv(R.Cfg{cap, P, A, N}, R.tools(R.Cfg{cap, P, A, N}, fin, r, c, a, n, p), 0n):
  match fin:
    case R.Stops{}:
      Unit{}
    case R.Goes{}:
      pinv_round(cap, P, A, N, False{}, r, c, a, n, p)
    case R.Resets{}:
      pinv_round(cap, P, A, N, True{}, r, c, a, n, p)

# one input keeps the poll invariant
def pinv_step(+cfg: R.Cfg, +s: R.St, +e: R.Ev, +k: Nat, i: PInv(cfg, s, k)) -> PInv(cfg, R.step(cfg, s, e), R.defers.at(R.St.ph(s), e, k)):
  match cfg:
    case R.Cfg{cap, P, A, N}:
      match s:
        case R.St{ph, r, c, a, n, p}:
          match ph e:
            case R.Answered{} e:
              i
            case R.Aborted{} e:
              i
            case R.Failed{why} e:
              i
            case R.Prepare{} R.Abort{}:
              Unit{}
            case R.Call{} R.Abort{}:
              Unit{}
            case R.Compact{over} R.Abort{}:
              Unit{}
            case R.Tools{} R.Abort{}:
              Unit{}
            case R.Prepare{} R.Go{reply, fin, got}:
              pinv_prepare(cap, P, A, N, reply, r, c, a, n)
            case R.Call{} R.Go{reply, fin, got}:
              pinv_call(cap, P, A, N, reply, r, c, a, n, p, k, i)
            case R.Compact{over} R.Go{reply, fin, got}:
              pinv_compact(cap, P, A, N, over, got, r, c, a, n, p)
            case R.Tools{} R.Go{reply, fin, got}:
              pinv_tools(cap, P, A, N, fin, r, c, a, n, p)

def pinv_run(evs: List<&2, R.Ev>, +cfg: R.Cfg, +s: R.St, +k: Nat, i: PInv(cfg, s, k)) -> PInv(cfg, R.run.go(evs, cfg, s), R.defers.go(evs, cfg, s, k)):
  match evs:
    case Nil{}:
      i
    case +e <> rest:
      pinv_run(rest, cfg, R.step(cfg, s, e), R.defers.at(R.St.ph(s), e, k), pinv_step(cfg, s, e, k, i))

# a run the poll cap failed had polls + 1 deferred replies in a row
def polls_of(+cfg: R.Cfg, +s: R.St, +k: Nat, i: PInv(cfg, s, k)) -> Or({R.polled(s) == False{} : Bool}, {k == 1n+R.Cfg.polls(cfg) : Nat}):
  match cfg:
    case R.Cfg{cap, P, A, N}:
      match s:
        case R.St{ph, r, c, a, n, p}:
          match ph:
            case R.Failed{why}:
              match why:
                case R.Polls{}:
                  Inr{i}
                case R.Model{}:
                  Inl{{==}}
                case R.Rounds{}:
                  Inl{{==}}
            case R.Prepare{}:
              Inl{{==}}
            case R.Call{}:
              Inl{{==}}
            case R.Compact{over}:
              Inl{{==}}
            case R.Tools{}:
              Inl{{==}}
            case R.Answered{}:
              Inl{{==}}
            case R.Aborted{}:
              Inl{{==}}

# The laws
# --------

def run_ends(+cfg: R.Cfg, +xs: List<&2, R.Ev>, h: {List.length(&2, R.Ev, xs) == R.bound(cfg) : Nat}, +more: List<&2, R.Ev>) -> {R.done(R.run(cfg, List.append(&2, R.Ev, xs, more))) == True{} : Bool}:
  %Equal.sym(R.St, R.run.go(List.append(&2, R.Ev, xs, more), cfg, R.init(cfg)), R.run.go(more, cfg, R.run.go(xs, cfg, R.init(cfg))), run_append(xs, more, cfg, R.init(cfg))) : {R.done(_) == True{} : Bool}
  stays_done(more, cfg, R.run.go(xs, cfg, R.init(cfg)), ends(xs, cfg, R.init(cfg), 0n, Equal.trans(Nat, List.length(&2, R.Ev, xs), R.bound(cfg), M(cfg, R.init(cfg)), h, bound_m(cfg))))

def abort_now(+cfg: R.Cfg, s: R.St, nd: {R.done(s) == False{} : Bool}) -> {R.St.ph(R.step(cfg, s, R.Abort{})) == R.Aborted{} : R.Ph}:
  match s:
    case R.St{ph, r, c, a, n, p}:
      match ph:
        case R.Prepare{}:
          {==}
        case R.Call{}:
          {==}
        case R.Compact{over}:
          {==}
        case R.Tools{}:
          {==}
        case R.Answered{}:
          absurd({R.St.ph(R.step(cfg, R.St{R.Answered{}, r, c, a, n, p}, R.Abort{})) == R.Aborted{} : R.Ph}, Equal.sym(Bool, True{}, False{}, nd))
        case R.Aborted{}:
          {==}
        case R.Failed{why}:
          absurd({R.St.ph(R.step(cfg, R.St{R.Failed{why}, r, c, a, n, p}, R.Abort{})) == R.Aborted{} : R.Ph}, Equal.sym(Bool, True{}, False{}, nd))

def rounds_capped(+cfg: R.Cfg, +evs: List<&2, R.Ev>) -> Or({R.failed(R.run(cfg, evs)) == True{} : Bool}, {Nat.is_lt(R.rounds(cfg, evs), Nat.max(R.Cfg.cap(cfg), 1n)) == True{} : Bool}):
  rounds_of(cfg, R.run(cfg, evs), R.rounds(cfg, evs), inv_run(evs, cfg, R.init(cfg), 0n, inv_init(cfg)))

def rounds_fail_at_cap(+cfg: R.Cfg, +evs: List<&2, R.Ev>) -> Or({R.capped(R.run(cfg, evs)) == False{} : Bool}, {R.rounds(cfg, evs) == Nat.max(R.Cfg.cap(cfg), 1n) : Nat}):
  caps_of(cfg, R.run(cfg, evs), R.rounds(cfg, evs), inv_run(evs, cfg, R.init(cfg), 0n, inv_init(cfg)))

def polls_need_defers(+cfg: R.Cfg, +evs: List<&2, R.Ev>) -> Or({R.polled(R.run(cfg, evs)) == False{} : Bool}, {R.defers(cfg, evs) == 1n+R.Cfg.polls(cfg) : Nat}):
  polls_of(cfg, R.run(cfg, evs), R.defers(cfg, evs), pinv_run(evs, cfg, R.init(cfg), 0n, Unit{}))

# a message that ends the model's turn with no text and no tool call steps
# as a noted error does: a retry with a note while notes are left, else
# the run fails on the model
def no_answer(+cfg: R.Cfg, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {R.call(cfg, R.Ended.reply(R.Ended{False{}, False{}}), r, c, a, n, p) == R.note(cfg, r, c, a, n, p) : R.St}:
  {==}

# a message with a tool call goes to the tools phase, whatever its text
def calls_never_answer(+cfg: R.Cfg, -text: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {R.call(cfg, R.Ended.reply(R.Ended{text, True{}}), r, c, a, n, p) == R.St{R.Tools{}, r, c, a, n, p} : R.St}:
  {==}

# a noted error spends a note, retryable or not, and keeps the retries
def note_spends_no_retry(+cfg: R.Cfg, -retryable: Bool, +r: Nat, +c: Nat, +a: Nat, +m: Nat, +p: Nat) -> {R.call(cfg, R.Error{retryable, True{}}, r, c, a, 1n+m, p) == R.St{R.Prepare{}, r, c, a, m, R.Cfg.polls(cfg)} : R.St}:
  {==}

# a retryable error that is not noted spends a retry and keeps the notes
def retry_spends_no_note(+cfg: R.Cfg, +r: Nat, +c: Nat, +b: Nat, +n: Nat, +p: Nat) -> {R.call(cfg, R.Error{True{}, False{}}, r, c, 1n+b, n, p) == R.St{R.Prepare{}, r, c, b, n, R.Cfg.polls(cfg)} : R.St}:
  {==}
