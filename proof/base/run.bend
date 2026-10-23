# eukhe: lemmas the proofs of two or more areas share: run

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ./logic/logic.bend as LLogicLogic
import ./logic/nat.bend as LLogicNat
import ./nat.bend as LNat

# Each input
# ----------

# prepare -> compact: the generation's compaction
def prep_compact(+P: Nat, +d: Nat, +u: Nat) -> {LLogicNat.gen(P, RnState.Prepare{}, 1n+d, u, 0n) == Nat.add(1n+P, 1n+LLogicNat.gen(P, RnState.Compact{False{}}, d, u, 0n)) : Nat}:
  +mD = Nat.mul(d, 1n+LLogicNat.Q(P))
  +mU = Nat.mul(u, LLogicNat.Q(P))
  %LNat.add_assoc_r(1n+LLogicNat.Q(P), mD, mU) : {Nat.add(LLogicNat.Q(P), _) == Nat.add(1n+P, 1n+LLogicNat.gen(P, RnState.Compact{False{}}, d, u, 0n)) : Nat}
  %LNat.add_succ_r(P, LLogicNat.gen(P, RnState.Compact{False{}}, d, u, 0n)) : {Nat.add(LLogicNat.Q(P), Nat.add(1n+LLogicNat.Q(P), Nat.add(mD, mU))) == 1n+_ : Nat}
  {==}

# call -> prepare: a retry, noted or not
def call_retry(+P: Nat, +c: Nat, +b: Nat, +p: Nat) -> {LLogicNat.gen(P, RnState.Call{}, c, 1n+b, p) == Nat.add(p, 1n+LLogicNat.gen(P, RnState.Prepare{}, c, b, 0n)) : Nat}:
  +mC = Nat.mul(c, 1n+LLogicNat.Q(P))
  +mb = Nat.mul(b, LLogicNat.Q(P))
  %LNat.add_succ_r(p, LLogicNat.gen(P, RnState.Prepare{}, c, b, 0n)) : {LLogicNat.gen(P, RnState.Call{}, c, 1n+b, p) == _ : Nat}
  %LNat.add_lcomm(mC, LLogicNat.Q(P), mb) : {LLogicNat.gen(P, RnState.Call{}, c, 1n+b, p) == 1n+Nat.add(p, _) : Nat}
  {==}

# call -> prepare: a noted retry spends a note, a + (1 + m) = 1 + (a + m)
def call_note(+P: Nat, +c: Nat, +a: Nat, +m: Nat, +p: Nat) -> {LLogicNat.gen(P, RnState.Call{}, c, Nat.add(a, 1n+m), p) == Nat.add(p, 1n+LLogicNat.gen(P, RnState.Prepare{}, c, Nat.add(a, m), 0n)) : Nat}:
  %LNat.add_succ_r(a, m) : {LLogicNat.gen(P, RnState.Call{}, c, _, p) == Nat.add(p, 1n+LLogicNat.gen(P, RnState.Prepare{}, c, Nat.add(a, m), 0n)) : Nat}
  call_retry(P, c, Nat.add(a, m), p)

# call -> compact: an overflow's compaction
def call_compact(+P: Nat, +d: Nat, +u: Nat, +p: Nat) -> {LLogicNat.gen(P, RnState.Call{}, 1n+d, u, p) == Nat.add(p, 1n+LLogicNat.gen(P, RnState.Compact{True{}}, d, u, 0n)) : Nat}:
  +mD = Nat.mul(d, 1n+LLogicNat.Q(P))
  +mU = Nat.mul(u, LLogicNat.Q(P))
  %LNat.add_succ_r(p, LLogicNat.gen(P, RnState.Compact{True{}}, d, u, 0n)) : {LLogicNat.gen(P, RnState.Call{}, 1n+d, u, p) == _ : Nat}
  %LNat.add_assoc(1n+LLogicNat.Q(P), mD, mU) : {LLogicNat.gen(P, RnState.Call{}, 1n+d, u, p) == 1n+Nat.add(p, _) : Nat}
  {==}

def dec_prepare_cut(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +p: Nat) -> LLogicNat.Fall(RnState.Cfg{cap, P, A, N}, RnState.St{RnState.Prepare{}, r, c, a, n, p}, LLogicNat.K.prepare_cut(P, cut, c), RnStep.prepare.cut(RnState.Cfg{cap, P, A, N}, cut, r, c, a, n)):
  match cut c:
    case True{} 1n+d:
      LNat.lift(1n+P, LLogicNat.gen(P, RnState.Prepare{}, 1n+d, Nat.add(a, n), p), LLogicNat.gen(P, RnState.Compact{False{}}, d, Nat.add(a, n), P), LLogicNat.X(P, Nat.add(A, N), r), prep_compact(P, d, Nat.add(a, n)))
    case True{} 0n:
      LNat.lift(0n, LLogicNat.gen(P, RnState.Prepare{}, 0n, Nat.add(a, n), p), LLogicNat.gen(P, RnState.Call{}, 0n, Nat.add(a, n), P), LLogicNat.X(P, Nat.add(A, N), r), {==})
    case False{} +c:
      LNat.lift(0n, LLogicNat.gen(P, RnState.Prepare{}, c, Nat.add(a, n), p), LLogicNat.gen(P, RnState.Call{}, c, Nat.add(a, n), P), LLogicNat.X(P, Nat.add(A, N), r), {==})

def dec_prepare(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: RnState.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> LLogicNat.Fall(RnState.Cfg{cap, P, A, N}, RnState.St{RnState.Prepare{}, r, c, a, n, p}, LLogicNat.K.prepare(P, reply, c), RnStep.prepare(RnState.Cfg{cap, P, A, N}, reply, r, c, a, n)):
  match reply:
    case RnState.Overflow{cut}:
      dec_prepare_cut(cap, P, A, N, cut, r, c, a, n, p)
    case RnState.Plain{}:
      LNat.lift(0n, LLogicNat.gen(P, RnState.Prepare{}, c, Nat.add(a, n), p), LLogicNat.gen(P, RnState.Call{}, c, Nat.add(a, n), P), LLogicNat.X(P, Nat.add(A, N), r), {==})
    case RnState.Calls{}:
      LNat.lift(0n, LLogicNat.gen(P, RnState.Prepare{}, c, Nat.add(a, n), p), LLogicNat.gen(P, RnState.Call{}, c, Nat.add(a, n), P), LLogicNat.X(P, Nat.add(A, N), r), {==})
    case RnState.Deferred{}:
      LNat.lift(0n, LLogicNat.gen(P, RnState.Prepare{}, c, Nat.add(a, n), p), LLogicNat.gen(P, RnState.Call{}, c, Nat.add(a, n), P), LLogicNat.X(P, Nat.add(A, N), r), {==})
    case RnState.Error{retryable, noted}:
      LNat.lift(0n, LLogicNat.gen(P, RnState.Prepare{}, c, Nat.add(a, n), p), LLogicNat.gen(P, RnState.Call{}, c, Nat.add(a, n), P), LLogicNat.X(P, Nat.add(A, N), r), {==})

def dec_retry(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, +r: Nat, +c: Nat, a: Nat, +n: Nat, +p: Nat) -> LLogicNat.Fall(RnState.Cfg{cap, P, A, N}, RnState.St{RnState.Call{}, r, c, a, n, p}, LLogicNat.K.retry(P, Nat.add(A, N), retryable, r, c, a, n, p), RnStep.retry(RnState.Cfg{cap, P, A, N}, retryable, r, c, a, n, p)):
  match retryable a:
    case True{} 1n+b:
      LNat.lift(p, LLogicNat.gen(P, RnState.Call{}, c, Nat.add(1n+b, n), p), LLogicNat.gen(P, RnState.Prepare{}, c, Nat.add(b, n), P), LLogicNat.X(P, Nat.add(A, N), r), call_retry(P, c, Nat.add(b, n), p))
    case True{} 0n:
      LNat.call_end(P, Nat.add(A, N), r, c, Nat.add(0n, n), p)
    case False{} +a:
      LNat.call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), p)

def dec_note(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +r: Nat, +c: Nat, +a: Nat, n: Nat, +p: Nat) -> LLogicNat.Fall(RnState.Cfg{cap, P, A, N}, RnState.St{RnState.Call{}, r, c, a, n, p}, LLogicNat.K.note(P, Nat.add(A, N), r, c, a, n, p), RnStep.note(RnState.Cfg{cap, P, A, N}, r, c, a, n, p)):
  match n:
    case 1n+m:
      LNat.lift(p, LLogicNat.gen(P, RnState.Call{}, c, Nat.add(a, 1n+m), p), LLogicNat.gen(P, RnState.Prepare{}, c, Nat.add(a, m), P), LLogicNat.X(P, Nat.add(A, N), r), call_note(P, c, a, m, p))
    case 0n:
      LNat.call_end(P, Nat.add(A, N), r, c, Nat.add(a, 0n), p)

def dec_error(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, noted: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> LLogicNat.Fall(RnState.Cfg{cap, P, A, N}, RnState.St{RnState.Call{}, r, c, a, n, p}, LLogicNat.K.error(P, Nat.add(A, N), retryable, noted, r, c, a, n, p), RnStep.error(RnState.Cfg{cap, P, A, N}, retryable, noted, r, c, a, n, p)):
  match noted:
    case True{}:
      dec_note(cap, P, A, N, r, c, a, n, p)
    case False{}:
      dec_retry(cap, P, A, N, retryable, r, c, a, n, p)

def dec_overflow(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +p: Nat) -> LLogicNat.Fall(RnState.Cfg{cap, P, A, N}, RnState.St{RnState.Call{}, r, c, a, n, p}, LLogicNat.K.overflow(P, Nat.add(A, N), cut, r, c, Nat.add(a, n), p), RnStep.overflow(cut, r, c, a, n, p)):
  match cut c:
    case True{} 1n+d:
      LNat.lift(p, LLogicNat.gen(P, RnState.Call{}, 1n+d, Nat.add(a, n), p), LLogicNat.gen(P, RnState.Compact{True{}}, d, Nat.add(a, n), p), LLogicNat.X(P, Nat.add(A, N), r), call_compact(P, d, Nat.add(a, n), p))
    case True{} 0n:
      LNat.call_end(P, Nat.add(A, N), r, 0n, Nat.add(a, n), p)
    case False{} +c:
      LNat.call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), p)

def dec_deferred(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +r: Nat, +c: Nat, +a: Nat, +n: Nat, p: Nat) -> LLogicNat.Fall(RnState.Cfg{cap, P, A, N}, RnState.St{RnState.Call{}, r, c, a, n, p}, LLogicNat.K.deferred(P, Nat.add(A, N), r, c, Nat.add(a, n), p), RnStep.call(RnState.Cfg{cap, P, A, N}, RnState.Deferred{}, r, c, a, n, p)):
  match p:
    case 0n:
      LNat.call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), 0n)
    case 1n+q:
      LNat.lift(0n, LLogicNat.gen(P, RnState.Call{}, c, Nat.add(a, n), 1n+q), LLogicNat.gen(P, RnState.Call{}, c, Nat.add(a, n), q), LLogicNat.X(P, Nat.add(A, N), r), {==})

def dec_call(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: RnState.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> LLogicNat.Fall(RnState.Cfg{cap, P, A, N}, RnState.St{RnState.Call{}, r, c, a, n, p}, LLogicNat.K.call(P, Nat.add(A, N), reply, r, c, a, n, p), RnStep.call(RnState.Cfg{cap, P, A, N}, reply, r, c, a, n, p)):
  match reply:
    case RnState.Plain{}:
      LNat.call_end(P, Nat.add(A, N), r, c, Nat.add(a, n), p)
    case RnState.Calls{}:
      LNat.lift(Nat.add(p, LLogicNat.B(P, c, Nat.add(a, n))), LLogicNat.gen(P, RnState.Call{}, c, Nat.add(a, n), p), 0n, LLogicNat.X(P, Nat.add(A, N), r), LNat.call_tools(Nat.add(p, LLogicNat.B(P, c, Nat.add(a, n)))))
    case RnState.Deferred{}:
      dec_deferred(cap, P, A, N, r, c, a, n, p)
    case RnState.Error{retryable, noted}:
      dec_error(cap, P, A, N, retryable, noted, r, c, a, n, p)
    case RnState.Overflow{cut}:
      dec_overflow(cap, P, A, N, cut, r, c, a, n, p)

def dec_compact(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +over: Bool, got: RnState.Got, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> LLogicNat.Fall(RnState.Cfg{cap, P, A, N}, RnState.St{RnState.Compact{over}, r, c, a, n, p}, LLogicNat.K.compact(P, Nat.add(A, N), over, got, r, c, Nat.add(a, n), p), RnStep.compact(RnState.Cfg{cap, P, A, N}, over, got, r, c, a, n, p)):
  match over got:
    case over RnState.Built{}:
      LNat.lift(0n, LLogicNat.gen(P, RnState.Compact{over}, c, Nat.add(a, n), p), LLogicNat.gen(P, RnState.Prepare{}, c, Nat.add(a, n), P), LLogicNat.X(P, Nat.add(A, N), r), {==})
    case True{} RnState.Kept{}:
      LNat.to_end(LLogicNat.gen(P, RnState.Compact{True{}}, c, Nat.add(a, n), p), LLogicNat.X(P, Nat.add(A, N), r))
    case False{} RnState.Kept{}:
      LNat.lift(0n, LLogicNat.gen(P, RnState.Compact{False{}}, c, Nat.add(a, n), p), LLogicNat.gen(P, RnState.Prepare{}, c, Nat.add(a, n), P), LLogicNat.X(P, Nat.add(A, N), r), {==})
    case over RnState.Broke{}:
      LNat.to_end(LLogicNat.gen(P, RnState.Compact{over}, c, Nat.add(a, n), p), LLogicNat.X(P, Nat.add(A, N), r))

def dec_round(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reset: Bool, r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> LLogicNat.Fall(RnState.Cfg{cap, P, A, N}, RnState.St{RnState.Tools{}, r, c, a, n, p}, LLogicNat.K.round(P, Nat.add(A, N), reset, r), RnStep.round(RnState.Cfg{cap, P, A, N}, reset, r, c, a, n, p)):
  match reset r:
    case reset 0n:
      LNat.to_end(0n, LLogicNat.X(P, Nat.add(A, N), 0n))
    case True{} 1n+s:
      LNat.to_end(0n, LLogicNat.X(P, Nat.add(A, N), 1n+s))
    case False{} 1n+s:
      LNat.next_gen(LLogicNat.gen(P, RnState.Prepare{}, 1n, Nat.add(A, N), 0n), LLogicNat.X(P, Nat.add(A, N), s))

def dec_tools(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, fin: RnState.Fin, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> LLogicNat.Fall(RnState.Cfg{cap, P, A, N}, RnState.St{RnState.Tools{}, r, c, a, n, p}, LLogicNat.K.tools(P, Nat.add(A, N), fin, r), RnStep.tools(RnState.Cfg{cap, P, A, N}, fin, r, c, a, n, p)):
  match fin:
    case RnState.Stops{}:
      LNat.to_end(0n, LLogicNat.X(P, Nat.add(A, N), r))
    case RnState.Goes{}:
      dec_round(cap, P, A, N, False{}, r, c, a, n, p)
    case RnState.Resets{}:
      dec_round(cap, P, A, N, True{}, r, c, a, n, p)

# every input to a live run lowers M
def dec(+cfg: RnState.Cfg, +s: RnState.St, +e: RnState.Ev, nd: {RnState.done(s) == False{} : Bool}) -> LLogicNat.Fall(cfg, s, LLogicNat.K(cfg, s, e), RnStep.step(cfg, s, e)):
  match cfg:
    case RnState.Cfg{cap, pp, aa, nn}:
      match s:
        case RnState.St{ph, r, c, a, n, p}:
          match ph e:
            case RnState.Answered{} e:
              LLogicLogic.absurd(LLogicNat.FallAt(cap, pp, aa, nn, RnState.Answered{}, r, c, a, n, p, e), Equal.sym(Bool, True{}, False{}, nd))
            case RnState.Aborted{} e:
              LLogicLogic.absurd(LLogicNat.FallAt(cap, pp, aa, nn, RnState.Aborted{}, r, c, a, n, p, e), Equal.sym(Bool, True{}, False{}, nd))
            case RnState.Failed{why} e:
              LLogicLogic.absurd(LLogicNat.FallAt(cap, pp, aa, nn, RnState.Failed{why}, r, c, a, n, p, e), Equal.sym(Bool, True{}, False{}, nd))
            case RnState.Prepare{} RnState.Abort{}:
              LNat.to_end(LLogicNat.gen(pp, RnState.Prepare{}, c, Nat.add(a, n), p), LLogicNat.X(pp, Nat.add(aa, nn), r))
            case RnState.Call{} RnState.Abort{}:
              LNat.call_end(pp, Nat.add(aa, nn), r, c, Nat.add(a, n), p)
            case RnState.Compact{over} RnState.Abort{}:
              LNat.to_end(LLogicNat.gen(pp, RnState.Compact{over}, c, Nat.add(a, n), p), LLogicNat.X(pp, Nat.add(aa, nn), r))
            case RnState.Tools{} RnState.Abort{}:
              LNat.to_end(0n, LLogicNat.X(pp, Nat.add(aa, nn), r))
            case RnState.Prepare{} RnState.Go{reply, fin, got}:
              dec_prepare(cap, pp, aa, nn, reply, r, c, a, n, p)
            case RnState.Call{} RnState.Go{reply, fin, got}:
              dec_call(cap, pp, aa, nn, reply, r, c, a, n, p)
            case RnState.Compact{over} RnState.Go{reply, fin, got}:
              dec_compact(cap, pp, aa, nn, over, got, r, c, a, n, p)
            case RnState.Tools{} RnState.Go{reply, fin, got}:
              dec_tools(cap, pp, aa, nn, fin, r, c, a, n, p)

# The run ends
# ------------

# an ended run stays as it is
def end_stays(+cfg: RnState.Cfg, s: RnState.St, e: RnState.Ev, d: {RnState.done(s) == True{} : Bool}) -> {RnStep.step(cfg, s, e) == s : RnState.St}:
  match s:
    case RnState.St{ph, r, c, a, n, p}:
      match ph:
        case RnState.Answered{}:
          {==}
        case RnState.Aborted{}:
          {==}
        case RnState.Failed{why}:
          {==}
        case RnState.Prepare{}:
          LLogicLogic.absurd({RnStep.step(cfg, RnState.St{RnState.Prepare{}, r, c, a, n, p}, e) == RnState.St{RnState.Prepare{}, r, c, a, n, p} : RnState.St}, d)
        case RnState.Call{}:
          LLogicLogic.absurd({RnStep.step(cfg, RnState.St{RnState.Call{}, r, c, a, n, p}, e) == RnState.St{RnState.Call{}, r, c, a, n, p} : RnState.St}, d)
        case RnState.Compact{over}:
          LLogicLogic.absurd({RnStep.step(cfg, RnState.St{RnState.Compact{over}, r, c, a, n, p}, e) == RnState.St{RnState.Compact{over}, r, c, a, n, p} : RnState.St}, d)
        case RnState.Tools{}:
          LLogicLogic.absurd({RnStep.step(cfg, RnState.St{RnState.Tools{}, r, c, a, n, p}, e) == RnState.St{RnState.Tools{}, r, c, a, n, p} : RnState.St}, d)

def stays_done(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, +d: {RnState.done(s) == True{} : Bool}) -> {RnState.done(RnStep.run.go(evs, cfg, s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      d
    case e <> rest:
      %Equal.sym(RnState.St, RnStep.step(cfg, s, e), s, end_stays(cfg, s, e, d)) : {RnState.done(RnStep.run.go(rest, cfg, _)) == True{} : Bool}
      stays_done(rest, cfg, s, d)

# with no input left, the run has ended
def nil_done(+cfg: RnState.Cfg, +s: RnState.St, +j: Nat, h: {0n == Nat.add(j, LLogicNat.M(cfg, s)) : Nat}) -> {RnState.done(s) == True{} : Bool}:
  match cfg:
    case RnState.Cfg{cap, pp, aa, nn}:
      match s:
        case RnState.St{ph, r, c, a, n, p}:
          match ph:
            case RnState.Prepare{}:
              LNat.pos({RnState.done(RnState.St{RnState.Prepare{}, r, c, a, n, p}) == True{} : Bool}, j, LLogicNat.gen(pp, RnState.Prepare{}, c, Nat.add(a, n), p), Nat.mul(r, LLogicNat.G(pp, Nat.add(aa, nn))), h)
            case RnState.Call{}:
              LNat.pos({RnState.done(RnState.St{RnState.Call{}, r, c, a, n, p}) == True{} : Bool}, j, LLogicNat.gen(pp, RnState.Call{}, c, Nat.add(a, n), p), Nat.mul(r, LLogicNat.G(pp, Nat.add(aa, nn))), h)
            case RnState.Compact{over}:
              LNat.pos({RnState.done(RnState.St{RnState.Compact{over}, r, c, a, n, p}) == True{} : Bool}, j, LLogicNat.gen(pp, RnState.Compact{over}, c, Nat.add(a, n), p), Nat.mul(r, LLogicNat.G(pp, Nat.add(aa, nn))), h)
            case RnState.Tools{}:
              LNat.pos({RnState.done(RnState.St{RnState.Tools{}, r, c, a, n, p}) == True{} : Bool}, j, 0n, Nat.mul(r, LLogicNat.G(pp, Nat.add(aa, nn))), h)
            case RnState.Answered{}:
              {==}
            case RnState.Aborted{}:
              {==}
            case RnState.Failed{why}:
              {==}

# one input later, the inputs left still cover M
def next_len(+cfg: RnState.Cfg, +s: RnState.St, +e: RnState.Ev, +j: Nat, -rest: List<&2, RnState.Ev>, h: {1n+List.length(&2, RnState.Ev, rest) == Nat.add(j, LLogicNat.M(cfg, s)) : Nat}, nd: {RnState.done(s) == False{} : Bool}) -> {List.length(&2, RnState.Ev, rest) == Nat.add(Nat.add(j, LLogicNat.K(cfg, s, e)), LLogicNat.M(cfg, RnStep.step(cfg, s, e))) : Nat}:
  LLogicNat.succ_inj(List.length(&2, RnState.Ev, rest), Nat.add(Nat.add(j, LLogicNat.K(cfg, s, e)), LLogicNat.M(cfg, RnStep.step(cfg, s, e))), LNat.next_len1(List.length(&2, RnState.Ev, rest), j, LLogicNat.K(cfg, s, e), LLogicNat.M(cfg, s), LLogicNat.M(cfg, RnStep.step(cfg, s, e)), h, dec(cfg, s, e, nd)))

# a run whose inputs cover M has ended after them
def ends(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, +j: Nat, h: {List.length(&2, RnState.Ev, evs) == Nat.add(j, LLogicNat.M(cfg, s)) : Nat}) -> {RnState.done(RnStep.run.go(evs, cfg, s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      nil_done(cfg, s, j, h)
    case +e <> rest:
      match s:
        case RnState.St{ph, r, c, a, n, p}:
          match ph:
            case RnState.Prepare{}:
              +t = {RnState.St{RnState.Prepare{}, r, c, a, n, p} : RnState.St}
              ends(rest, cfg, RnStep.step(cfg, t, e), Nat.add(j, LLogicNat.K(cfg, t, e)), next_len(cfg, t, e, j, rest, h, {==}))
            case RnState.Call{}:
              +t = {RnState.St{RnState.Call{}, r, c, a, n, p} : RnState.St}
              ends(rest, cfg, RnStep.step(cfg, t, e), Nat.add(j, LLogicNat.K(cfg, t, e)), next_len(cfg, t, e, j, rest, h, {==}))
            case RnState.Compact{over}:
              +t = {RnState.St{RnState.Compact{over}, r, c, a, n, p} : RnState.St}
              ends(rest, cfg, RnStep.step(cfg, t, e), Nat.add(j, LLogicNat.K(cfg, t, e)), next_len(cfg, t, e, j, rest, h, {==}))
            case RnState.Tools{}:
              +t = {RnState.St{RnState.Tools{}, r, c, a, n, p} : RnState.St}
              ends(rest, cfg, RnStep.step(cfg, t, e), Nat.add(j, LLogicNat.K(cfg, t, e)), next_len(cfg, t, e, j, rest, h, {==}))
            case RnState.Answered{}:
              stays_done(rest, cfg, RnState.St{RnState.Answered{}, r, c, a, n, p}, {==})
            case RnState.Aborted{}:
              stays_done(rest, cfg, RnState.St{RnState.Aborted{}, r, c, a, n, p}, {==})
            case RnState.Failed{why}:
              stays_done(rest, cfg, RnState.St{RnState.Failed{why}, r, c, a, n, p}, {==})
