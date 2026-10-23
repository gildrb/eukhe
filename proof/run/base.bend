# eukhe: lemmas the proofs of area run share

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/retry.bend as R
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/measure.bend as RnMeasure
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/run.bend as Run
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

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

# The invariant
# -------------
# After any inputs, with k the counted rounds: the cap ended the run only
# after max(cap, 1) rounds; and a run that did not fail has made
# cap - 1 - r rounds.

def Inv(+cap: Nat, +ph: RnState.Ph, +r: Nat, +k: Nat) -> Type:
  Or({RnState.Ph.capped(ph) == False{} : Bool}, {k == Nat.max(cap, 1n) : Nat}) & Or({RnState.Ph.failed(ph) == True{} : Bool}, {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat})

def InvS(+cfg: RnState.Cfg, +s: RnState.St, +k: Nat) -> Type:
  Inv(RnState.Cfg.cap(cfg), RnState.St.ph(s), RnState.St.r(s), k)

# a live run has not failed
def cap_of(-T: Type, o: Or({False{} == True{} : Bool}, T)) -> T:
  match o:
    case Inl{x}:
      LLogicLogic.absurd(T, x)
    case Inr{y}:
      y

def cap_next(n: Nat, -s: Nat, -cap: Nat, capv: {Nat.add(n, 2n+s) == cap : Nat}) -> {1n+Nat.add(n, 1n+s) == cap : Nat}:
  %capv : {1n+Nat.add(n, 1n+s) == _ : Nat}
  LNat.add_succ_r(n, 1n+s)

# the round that meets the cap is the max(cap, 1)th
def one_more(+n: Nat, -m: Nat, capv: {Nat.add(n, 1n+0n) == m : Nat}) -> {1n+n == m : Nat}:
  %capv : {1n+n == _ : Nat}
  %LNat.add_succ_r(n, 0n) : {1n+n == _ : Nat}
  %Equal.sym(Nat, Nat.add(n, 0n), n, LNat.add_zero(n)) : {1n+n == 1n+_ : Nat}
  {==}

def inv_round(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reset: Bool, r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(RnState.Cfg{cap, P, A, N}, RnStep.round(RnState.Cfg{cap, P, A, N}, reset, r, c, a, n, p), 1n+k):
  match reset r:
    case reset 0n:
      (Inr{one_more(k, Nat.max(cap, 1n), capv)}, Inl{{==}})
    case True{} 1n+s:
      (Inl{{==}}, Inr{cap_next(k, s, Nat.max(cap, 1n), capv)})
    case False{} 1n+s:
      (Inl{{==}}, Inr{cap_next(k, s, Nat.max(cap, 1n), capv)})

def inv_tools(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, fin: RnState.Fin, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(RnState.Cfg{cap, P, A, N}, RnStep.tools(RnState.Cfg{cap, P, A, N}, fin, r, c, a, n, p), RnMeasure.counted.go(fin, k)):
  match fin:
    case RnState.Stops{}:
      (Inl{{==}}, Inr{capv})
    case RnState.Goes{}:
      inv_round(cap, P, A, N, False{}, r, c, a, n, p, k, capv)
    case RnState.Resets{}:
      inv_round(cap, P, A, N, True{}, r, c, a, n, p, k, capv)

def inv_prepare_cut(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(RnState.Cfg{cap, P, A, N}, RnStep.prepare.cut(RnState.Cfg{cap, P, A, N}, cut, r, c, a, n), k):
  match cut c:
    case True{} 1n+d:
      (Inl{{==}}, Inr{capv})
    case True{} 0n:
      (Inl{{==}}, Inr{capv})
    case False{} c:
      (Inl{{==}}, Inr{capv})

def inv_prepare(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: RnState.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(RnState.Cfg{cap, P, A, N}, RnStep.prepare(RnState.Cfg{cap, P, A, N}, reply, r, c, a, n), k):
  match reply:
    case RnState.Overflow{cut}:
      inv_prepare_cut(cap, P, A, N, cut, r, c, a, n, k, capv)
    case RnState.Plain{}:
      (Inl{{==}}, Inr{capv})
    case RnState.Calls{}:
      (Inl{{==}}, Inr{capv})
    case RnState.Deferred{}:
      (Inl{{==}}, Inr{capv})
    case RnState.Error{retryable, noted}:
      (Inl{{==}}, Inr{capv})

def inv_retry(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, +r: Nat, +c: Nat, a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(RnState.Cfg{cap, P, A, N}, RnStep.retry(RnState.Cfg{cap, P, A, N}, retryable, r, c, a, n, p), k):
  match retryable a:
    case True{} 1n+b:
      (Inl{{==}}, Inr{capv})
    case True{} 0n:
      (Inl{{==}}, Inl{{==}})
    case False{} a:
      (Inl{{==}}, Inl{{==}})

def inv_note(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +r: Nat, +c: Nat, +a: Nat, n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(RnState.Cfg{cap, P, A, N}, RnStep.note(RnState.Cfg{cap, P, A, N}, r, c, a, n, p), k):
  match n:
    case 1n+m:
      (Inl{{==}}, Inr{capv})
    case 0n:
      (Inl{{==}}, Inl{{==}})

def inv_error(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, noted: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(RnState.Cfg{cap, P, A, N}, RnStep.error(RnState.Cfg{cap, P, A, N}, retryable, noted, r, c, a, n, p), k):
  match noted:
    case True{}:
      inv_note(cap, P, A, N, r, c, a, n, p, k, capv)
    case False{}:
      inv_retry(cap, P, A, N, retryable, r, c, a, n, p, k, capv)

def inv_overflow(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(RnState.Cfg{cap, P, A, N}, RnStep.overflow(cut, r, c, a, n, p), k):
  match cut c:
    case True{} 1n+d:
      (Inl{{==}}, Inr{capv})
    case True{} 0n:
      (Inl{{==}}, Inl{{==}})
    case False{} c:
      (Inl{{==}}, Inl{{==}})

def inv_call(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: RnState.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(RnState.Cfg{cap, P, A, N}, RnStep.call(RnState.Cfg{cap, P, A, N}, reply, r, c, a, n, p), k):
  match reply:
    case RnState.Plain{}:
      (Inl{{==}}, Inr{capv})
    case RnState.Calls{}:
      (Inl{{==}}, Inr{capv})
    case RnState.Deferred{}:
      match p:
        case 0n:
          (Inl{{==}}, Inl{{==}})
        case 1n+q:
          (Inl{{==}}, Inr{capv})
    case RnState.Error{retryable, noted}:
      inv_error(cap, P, A, N, retryable, noted, r, c, a, n, p, k, capv)
    case RnState.Overflow{cut}:
      inv_overflow(cap, P, A, N, cut, r, c, a, n, p, k, capv)

def inv_compact(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, over: Bool, got: RnState.Got, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(RnState.Cfg{cap, P, A, N}, RnStep.compact(RnState.Cfg{cap, P, A, N}, over, got, r, c, a, n, p), k):
  match over got:
    case over RnState.Built{}:
      (Inl{{==}}, Inr{capv})
    case True{} RnState.Kept{}:
      (Inl{{==}}, Inl{{==}})
    case False{} RnState.Kept{}:
      (Inl{{==}}, Inr{capv})
    case over RnState.Broke{}:
      (Inl{{==}}, Inl{{==}})

# one input keeps the invariant
def inv_step(+cfg: RnState.Cfg, +s: RnState.St, +k: Nat, +e: RnState.Ev, i: InvS(cfg, s, k)) -> InvS(cfg, RnStep.step(cfg, s, e), RnMeasure.counted(RnState.St.ph(s), e, k)):
  match cfg:
    case RnState.Cfg{cap, pp, aa, nn}:
      match s:
        case RnState.St{ph, r, c, a, n, p}:
          match ph e:
            case RnState.Answered{} e:
              i
            case RnState.Aborted{} e:
              i
            case RnState.Failed{why} e:
              i
            case RnState.Prepare{} RnState.Abort{}:
              (cp, co) = i
              (Inl{{==}}, Inr{cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co)})
            case RnState.Call{} RnState.Abort{}:
              (cp, co) = i
              (Inl{{==}}, Inr{cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co)})
            case RnState.Compact{over} RnState.Abort{}:
              (cp, co) = i
              (Inl{{==}}, Inr{cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co)})
            case RnState.Tools{} RnState.Abort{}:
              (cp, co) = i
              (Inl{{==}}, Inr{cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co)})
            case RnState.Prepare{} RnState.Go{reply, fin, got}:
              (cp, co) = i
              inv_prepare(cap, pp, aa, nn, reply, r, c, a, n, k, cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co))
            case RnState.Call{} RnState.Go{reply, fin, got}:
              (cp, co) = i
              inv_call(cap, pp, aa, nn, reply, r, c, a, n, p, k, cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co))
            case RnState.Compact{over} RnState.Go{reply, fin, got}:
              (cp, co) = i
              inv_compact(cap, pp, aa, nn, over, got, r, c, a, n, p, k, cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co))
            case RnState.Tools{} RnState.Go{reply, fin, got}:
              (cp, co) = i
              inv_tools(cap, pp, aa, nn, fin, r, c, a, n, p, k, cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co))

def inv_run(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, +k: Nat, i: InvS(cfg, s, k)) -> InvS(cfg, RnStep.run.go(evs, cfg, s), RnMeasure.rounds.go(evs, cfg, s, k)):
  match evs:
    case Nil{}:
      i
    case +e <> rest:
      inv_run(rest, cfg, RnStep.step(cfg, s, e), RnMeasure.counted(RnState.St.ph(s), e, k), inv_step(cfg, s, k, e, i))

# a run starts with the invariant
def inv_init(+cfg: RnState.Cfg) -> InvS(cfg, RnState.init(cfg), 0n):
  match cfg:
    case RnState.Cfg{cap, pp, aa, nn}:
      (Inl{{==}}, Inr{Equal.sym(Nat, Nat.max(cap, 1n), 1n+Nat.sub(cap, 1n), max1(cap))})

# The decisions Rust calls (H4.9)
# --------------------------------
# rk.*: the lemmas of the laws of LAWS.bend (H4.9) and of
# rec_recover_is_the_rust_rule: each decision of bend/run.bend that
# Rust calls is the rule decide.rs wrote (the counts left are exact,
# by induction on the counts and the limits), the counts left lose
# nothing (m - (m - x) = x for x <= m), and the core's cap changes no
# decision.

def rk.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def rk.wait(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +w: Nat, +x: Nat) -> {RnDecision.Then.ph(False{}, RnState.St.ph(RnStep.call(cfg, RnState.Deferred{}, r, c, a, n, Nat.sub(w, x)))) == Run.rust.wait(Nat.is_lt(x, w)) : RnDecision.Then}:
  match w x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+v 0n:
      {==}
    case 1n+v 1n+y:
      rk.wait(cfg, r, c, a, n, v, y)

def rk.notes(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +a: Nat, +p: Nat, +m: Nat, +x: Nat) -> {RnDecision.Then.ph(True{}, RnState.St.ph(RnStep.note(cfg, r, c, a, Nat.sub(m, x), p))) == Run.rust.noted(Nat.is_lt(x, m)) : RnDecision.Then}:
  match m x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+v 0n:
      {==}
    case 1n+v 1n+y:
      rk.notes(cfg, r, c, a, p, v, y)

def rk.retry(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +n: Nat, +p: Nat, +m: Nat, +x: Nat) -> {RnDecision.Then.ph(False{}, RnState.St.ph(RnStep.retry(cfg, True{}, r, c, Nat.sub(m, x), n, p))) == Run.rust.retry(Nat.is_lt(x, m)) : RnDecision.Then}:
  match m x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+v 0n:
      {==}
    case 1n+v 1n+y:
      rk.retry(cfg, r, c, n, p, v, y)

def rk.over(+cfg: RnState.Cfg, +r: Nat, +a: Nat, +n: Nat, +p: Nat, +compacted: Bool, +cut: Bool) -> {RnDecision.Then.ph(False{}, RnState.St.ph(RnStep.call(cfg, RnState.Overflow{cut}, r, RnDecision.c.of(compacted), a, n, p))) == Run.rust.over(Bool.and(cut, Bool.not(compacted))) : RnDecision.Then}:
  match compacted cut:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def rk.run_reply_is_the_rust_rule(+l: RnDecision.Lim, +t: RnDecision.At, +reply: RnState.Reply) -> {RnDecision.decide.reply(l, t, reply) == Run.rust.after_reply(l, t, reply) : RnDecision.Then}:
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case RnDecision.At{+attempt, +notes, +waited, +compacted}:
          match reply:
            case RnState.Plain{}:
              {==}
            case RnState.Calls{}:
              {==}
            case RnState.Deferred{}:
              rk.wait(RnState.Cfg{rounds, wait, retries, most}, 0n, RnDecision.c.of(compacted), Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes)), Nat.sub(most, notes), wait, waited)
            case RnState.Error{retryable, noted}:
              match retryable noted:
                case retryable True{}:
                  rk.notes(RnState.Cfg{rounds, wait, retries, most}, 0n, RnDecision.c.of(compacted), Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes)), Nat.sub(wait, waited), most, notes)
                case True{} False{}:
                  rk.retry(RnState.Cfg{rounds, wait, retries, most}, 0n, RnDecision.c.of(compacted), Nat.sub(most, notes), Nat.sub(wait, waited), retries, Nat.sub(Nat.sub(attempt, 1n), notes))
                case False{} False{}:
                  {==}
            case RnState.Overflow{cut}:
              rk.over(RnState.Cfg{rounds, wait, retries, most}, 0n, Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes)), Nat.sub(most, notes), Nat.sub(wait, waited), compacted, cut)

def rk.eq0(+w: Nat, +x: Nat) -> {Bool.not(Nat.is_lt(x, w)) == Nat.is_eq(Nat.sub(w, x), 0n) : Bool}:
  match w x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+v 0n:
      {==}
    case 1n+v 1n+y:
      rk.eq0(v, y)

def rk.later(+b: Bool, +left: Nat, +gap: Nat) -> {Run.rust.later(Run.rust.wait(b)) == R.Step.act(R.live.pending(Bool.not(b), left, gap)) : R.Act}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : rk.BD(_, A, Unit)
  Unit{}

def rk.sub0(+x: Nat) -> {x == Nat.sub(x, 0n) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+y:
      {==}

def rk.and_l(+a: Bool, +b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      rk.absurd({False{} == True{} : Bool}, e)

def rk.and_r(+a: Bool, +b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      rk.absurd({b == True{} : Bool}, e)

def rk.add0(+n: Nat) -> {n == Nat.add(n, 0n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %rk.add0(p) : {1n+p == 1n+_ : Nat}
      {==}

def rk.adds(+a: Nat, +b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %rk.adds(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def rk.subadd(+m: Nat, +x: Nat, +e: {Nat.is_le(x, m) == True{} : Bool}) -> {Nat.add(Nat.sub(m, x), x) == m : Nat}:
  match m x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      rk.absurd({Nat.add(Nat.sub(0n, 1n+y), 1n+y) == 0n : Nat}, e)
    case 1n+v 0n:
      %rk.add0(v) : {1n+_ == 1n+v : Nat}
      {==}
    case 1n+v 1n+y:
      %rk.adds(Nat.sub(v, y), y) : {_ == 1n+v : Nat}
      %rk.subadd(v, y, e) : {1n+Nat.add(Nat.sub(v, y), y) == 1n+_ : Nat}
      {==}

def rk.addsub(+a: Nat, +b: Nat) -> {b == Nat.sub(Nat.add(a, b), a) : Nat}:
  match a:
    case 0n:
      rk.sub0(b)
    case 1n+p:
      rk.addsub(p, b)

def rk.subsub(+m: Nat, +x: Nat, +e: {Nat.is_le(x, m) == True{} : Bool}) -> {x == Nat.sub(m, Nat.sub(m, x)) : Nat}:
  %rk.subadd(m, x, e) : {x == Nat.sub(_, Nat.sub(m, x)) : Nat}
  rk.addsub(Nat.sub(m, x), x)

def rk.lt_s(+v: Nat, +x: Nat) -> {Nat.is_le(x, v) == Nat.is_lt(x, 1n+v) : Bool}:
  match v x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      match y:
        case 0n:
          {==}
        case 1n+z:
          {==}
    case 1n+u 0n:
      {==}
    case 1n+u 1n+y:
      rk.lt_s(u, y)

# ---- run_ffi ----

# The proofs of the codec laws of bend/ffi_run.bend (LAWS.bend section run_ffi):
# every request and answer reads back as itself (rk.rt_*: each field's
# encoding read back by the wire laws, in order), and the entry answers a
# request's decision, refuses input left over and a malformed request.

def rk.rt_lim(x: RnDecision.Lim, +rest: String, +h: {Run.run.lim_fits(x) == True{} : Bool}) -> {FRn.get_lim(FRn.put_lim(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnDecision.Lim>}:
  match x:
    case RnDecision.Lim{+rounds, +wait, +retries, +notes}:
      +hl0 = rk.and_l(LawsBase.wire_fits(rounds), Bool.and(LawsBase.wire_fits(wait), Bool.and(LawsBase.wire_fits(retries), LawsBase.wire_fits(notes))), h)
      +hr0 = rk.and_r(LawsBase.wire_fits(rounds), Bool.and(LawsBase.wire_fits(wait), Bool.and(LawsBase.wire_fits(retries), LawsBase.wire_fits(notes))), h)
      +hl1 = rk.and_l(LawsBase.wire_fits(wait), Bool.and(LawsBase.wire_fits(retries), LawsBase.wire_fits(notes)), hr0)
      +hr1 = rk.and_r(LawsBase.wire_fits(wait), Bool.and(LawsBase.wire_fits(retries), LawsBase.wire_fits(notes)), hr0)
      +hl2 = rk.and_l(LawsBase.wire_fits(retries), LawsBase.wire_fits(notes), hr1)
      +hr2 = rk.and_r(LawsBase.wire_fits(retries), LawsBase.wire_fits(notes), hr1)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(rounds, Wr.put_nat(wait, Wr.put_nat(retries, Wr.put_nat(notes, rest))))), Wr.Got{rounds, Wr.put_nat(wait, Wr.put_nat(retries, Wr.put_nat(notes, rest)))}, Wire.wire_nat_round_trip(rounds, Wr.put_nat(wait, Wr.put_nat(retries, Wr.put_nat(notes, rest))), hl0)) : {FRn.get_lim.f0(_) == Wr.Got{RnDecision.Lim{rounds, wait, retries, notes}, rest} : Wr.Dec<RnDecision.Lim>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(wait, Wr.put_nat(retries, Wr.put_nat(notes, rest)))), Wr.Got{wait, Wr.put_nat(retries, Wr.put_nat(notes, rest))}, Wire.wire_nat_round_trip(wait, Wr.put_nat(retries, Wr.put_nat(notes, rest)), hl1)) : {FRn.get_lim.f1(rounds, _) == Wr.Got{RnDecision.Lim{rounds, wait, retries, notes}, rest} : Wr.Dec<RnDecision.Lim>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(retries, Wr.put_nat(notes, rest))), Wr.Got{retries, Wr.put_nat(notes, rest)}, Wire.wire_nat_round_trip(retries, Wr.put_nat(notes, rest), hl2)) : {FRn.get_lim.f2(rounds, wait, _) == Wr.Got{RnDecision.Lim{rounds, wait, retries, notes}, rest} : Wr.Dec<RnDecision.Lim>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(notes, rest)), Wr.Got{notes, rest}, Wire.wire_nat_round_trip(notes, rest, hr2)) : {FRn.get_lim.f3(rounds, wait, retries, _) == Wr.Got{RnDecision.Lim{rounds, wait, retries, notes}, rest} : Wr.Dec<RnDecision.Lim>}
      {==}

def rk.rt_at(x: RnDecision.At, +rest: String, +h: {Run.run.at_fits(x) == True{} : Bool}) -> {FRn.get_at(FRn.put_at(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnDecision.At>}:
  match x:
    case RnDecision.At{+attempt, +notes, +waited, +compacted}:
      +hl0 = rk.and_l(LawsBase.wire_fits(attempt), Bool.and(LawsBase.wire_fits(notes), LawsBase.wire_fits(waited)), h)
      +hr0 = rk.and_r(LawsBase.wire_fits(attempt), Bool.and(LawsBase.wire_fits(notes), LawsBase.wire_fits(waited)), h)
      +hl1 = rk.and_l(LawsBase.wire_fits(notes), LawsBase.wire_fits(waited), hr0)
      +hr1 = rk.and_r(LawsBase.wire_fits(notes), LawsBase.wire_fits(waited), hr0)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(attempt, Wr.put_nat(notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest))))), Wr.Got{attempt, Wr.put_nat(notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest)))}, Wire.wire_nat_round_trip(attempt, Wr.put_nat(notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest))), hl0)) : {FRn.get_at.f0(_) == Wr.Got{RnDecision.At{attempt, notes, waited, compacted}, rest} : Wr.Dec<RnDecision.At>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest)))), Wr.Got{notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest))}, Wire.wire_nat_round_trip(notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest)), hl1)) : {FRn.get_at.f1(attempt, _) == Wr.Got{RnDecision.At{attempt, notes, waited, compacted}, rest} : Wr.Dec<RnDecision.At>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(waited, Wr.put_bool(compacted, rest))), Wr.Got{waited, Wr.put_bool(compacted, rest)}, Wire.wire_nat_round_trip(waited, Wr.put_bool(compacted, rest), hr1)) : {FRn.get_at.f2(attempt, notes, _) == Wr.Got{RnDecision.At{attempt, notes, waited, compacted}, rest} : Wr.Dec<RnDecision.At>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(compacted, rest)), Wr.Got{compacted, rest}, Wire.wire_bool_round_trip(compacted, rest)) : {FRn.get_at.f3(attempt, notes, waited, _) == Wr.Got{RnDecision.At{attempt, notes, waited, compacted}, rest} : Wr.Dec<RnDecision.At>}
      {==}

def rk.rt_reply(x: RnState.Reply, +rest: String) -> {FRn.get_reply(FRn.put_reply(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnState.Reply>}:
  match x:
    case RnState.Plain{}:
      {==}
    case RnState.Calls{}:
      {==}
    case RnState.Deferred{}:
      {==}
    case RnState.Error{+retryable, +noted}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(retryable, Wr.put_bool(noted, rest))), Wr.Got{retryable, Wr.put_bool(noted, rest)}, Wire.wire_bool_round_trip(retryable, Wr.put_bool(noted, rest))) : {FRn.get_reply.c3.f0(_) == Wr.Got{RnState.Error{retryable, noted}, rest} : Wr.Dec<RnState.Reply>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(noted, rest)), Wr.Got{noted, rest}, Wire.wire_bool_round_trip(noted, rest)) : {FRn.get_reply.c3.f1(retryable, _) == Wr.Got{RnState.Error{retryable, noted}, rest} : Wr.Dec<RnState.Reply>}
      {==}
    case RnState.Overflow{+cut}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(cut, rest)), Wr.Got{cut, rest}, Wire.wire_bool_round_trip(cut, rest)) : {FRn.get_reply.c4.f0(_) == Wr.Got{RnState.Overflow{cut}, rest} : Wr.Dec<RnState.Reply>}
      {==}

def rk.rt_ended(x: RnState.Ended, +rest: String) -> {FRn.get_ended(FRn.put_ended(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnState.Ended>}:
  match x:
    case RnState.Ended{+text, +calls}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(text, Wr.put_bool(calls, rest))), Wr.Got{text, Wr.put_bool(calls, rest)}, Wire.wire_bool_round_trip(text, Wr.put_bool(calls, rest))) : {FRn.get_ended.f0(_) == Wr.Got{RnState.Ended{text, calls}, rest} : Wr.Dec<RnState.Ended>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(calls, rest)), Wr.Got{calls, rest}, Wire.wire_bool_round_trip(calls, rest)) : {FRn.get_ended.f1(text, _) == Wr.Got{RnState.Ended{text, calls}, rest} : Wr.Dec<RnState.Ended>}
      {==}

def rk.rt_th(x: RnDecision.Th, +rest: String) -> {FRn.get_th(FRn.put_th(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnDecision.Th>}:
  match x:
    case RnDecision.Under{}:
      {==}
    case RnDecision.Background{}:
      {==}
    case RnDecision.Blocking{}:
      {==}

def rk.rt_got(x: RnState.Got, +rest: String) -> {FRn.get_got(FRn.put_got(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnState.Got>}:
  match x:
    case RnState.Built{}:
      {==}
    case RnState.Kept{}:
      {==}
    case RnState.Broke{}:
      {==}

def rk.rt_rcfg(x: RnRecovery.RCfg, +rest: String, +h: {Run.run.rcfg_fits(x) == True{} : Bool}) -> {FRn.get_rcfg(FRn.put_rcfg(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnRecovery.RCfg>}:
  match x:
    case RnRecovery.RCfg{+long, +leak, +redirect, +repeat}:
      +hl0 = rk.and_l(LawsBase.wire_fits(long), Bool.and(LawsBase.wire_fits(leak), Bool.and(LawsBase.wire_fits(redirect), LawsBase.wire_fits(repeat))), h)
      +hr0 = rk.and_r(LawsBase.wire_fits(long), Bool.and(LawsBase.wire_fits(leak), Bool.and(LawsBase.wire_fits(redirect), LawsBase.wire_fits(repeat))), h)
      +hl1 = rk.and_l(LawsBase.wire_fits(leak), Bool.and(LawsBase.wire_fits(redirect), LawsBase.wire_fits(repeat)), hr0)
      +hr1 = rk.and_r(LawsBase.wire_fits(leak), Bool.and(LawsBase.wire_fits(redirect), LawsBase.wire_fits(repeat)), hr0)
      +hl2 = rk.and_l(LawsBase.wire_fits(redirect), LawsBase.wire_fits(repeat), hr1)
      +hr2 = rk.and_r(LawsBase.wire_fits(redirect), LawsBase.wire_fits(repeat), hr1)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(long, Wr.put_nat(leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest))))), Wr.Got{long, Wr.put_nat(leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest)))}, Wire.wire_nat_round_trip(long, Wr.put_nat(leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest))), hl0)) : {FRn.get_rcfg.f0(_) == Wr.Got{RnRecovery.RCfg{long, leak, redirect, repeat}, rest} : Wr.Dec<RnRecovery.RCfg>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest)))), Wr.Got{leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest))}, Wire.wire_nat_round_trip(leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest)), hl1)) : {FRn.get_rcfg.f1(long, _) == Wr.Got{RnRecovery.RCfg{long, leak, redirect, repeat}, rest} : Wr.Dec<RnRecovery.RCfg>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(redirect, Wr.put_nat(repeat, rest))), Wr.Got{redirect, Wr.put_nat(repeat, rest)}, Wire.wire_nat_round_trip(redirect, Wr.put_nat(repeat, rest), hl2)) : {FRn.get_rcfg.f2(long, leak, _) == Wr.Got{RnRecovery.RCfg{long, leak, redirect, repeat}, rest} : Wr.Dec<RnRecovery.RCfg>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(repeat, rest)), Wr.Got{repeat, rest}, Wire.wire_nat_round_trip(repeat, rest, hr2)) : {FRn.get_rcfg.f3(long, leak, redirect, _) == Wr.Got{RnRecovery.RCfg{long, leak, redirect, repeat}, rest} : Wr.Dec<RnRecovery.RCfg>}
      {==}

def rk.rt_stuck(x: RnDecision.Stuck, +rest: String, +h: {Run.run.stuck_fits(x) == True{} : Bool}) -> {FRn.get_stuck(FRn.put_stuck(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnDecision.Stuck>}:
  match x:
    case RnDecision.Truncated{}:
      {==}
    case RnDecision.Leaked{}:
      {==}
    case RnDecision.Repeats{+before}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(before, rest)), Wr.Got{before, rest}, Wire.wire_nat_round_trip(before, rest, h)) : {FRn.get_stuck.c2.f0(_) == Wr.Got{RnDecision.Repeats{before}, rest} : Wr.Dec<RnDecision.Stuck>}
      {==}

def rk.rt_rk(x: RnRecovery.Rk, +rest: String) -> {FRn.get_rk(FRn.put_rk(x, rest)) == Wr.Got{x, rest} : Wr.Dec<RnRecovery.Rk>}:
  match x:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      {==}
    case RnRecovery.Leaks{}:
      {==}
    case RnRecovery.Loops{}:
      {==}

def rk.rt_ask(x: FRn.Ask, +rest: String, +h: {Run.run.ask_fits(x) == True{} : Bool}) -> {FRn.get_ask(FRn.put_ask(x, rest)) == Wr.Got{x, rest} : Wr.Dec<FRn.Ask>}:
  match x:
    case FRn.AskReply{+l, +t, +reply}:
      +hl0 = rk.and_l(Run.run.lim_fits(l), Run.run.at_fits(t), h)
      +hr0 = rk.and_r(Run.run.lim_fits(l), Run.run.at_fits(t), h)
      %Equal.sym(Wr.Dec<RnDecision.Lim>, FRn.get_lim(FRn.put_lim(l, FRn.put_at(t, FRn.put_reply(reply, rest)))), Wr.Got{l, FRn.put_at(t, FRn.put_reply(reply, rest))}, rk.rt_lim(l, FRn.put_at(t, FRn.put_reply(reply, rest)), hl0)) : {FRn.get_ask.c0.f0(_) == Wr.Got{FRn.AskReply{l, t, reply}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<RnDecision.At>, FRn.get_at(FRn.put_at(t, FRn.put_reply(reply, rest))), Wr.Got{t, FRn.put_reply(reply, rest)}, rk.rt_at(t, FRn.put_reply(reply, rest), hr0)) : {FRn.get_ask.c0.f1(l, _) == Wr.Got{FRn.AskReply{l, t, reply}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<RnState.Reply>, FRn.get_reply(FRn.put_reply(reply, rest)), Wr.Got{reply, rest}, rk.rt_reply(reply, rest)) : {FRn.get_ask.c0.f2(l, t, _) == Wr.Got{FRn.AskReply{l, t, reply}, rest} : Wr.Dec<FRn.Ask>}
      {==}
    case FRn.AskEnded{+m}:
      %Equal.sym(Wr.Dec<RnState.Ended>, FRn.get_ended(FRn.put_ended(m, rest)), Wr.Got{m, rest}, rk.rt_ended(m, rest)) : {FRn.get_ask.c1.f0(_) == Wr.Got{FRn.AskEnded{m}, rest} : Wr.Dec<FRn.Ask>}
      {==}
    case FRn.AskPrepare{+compacted, +th}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(compacted, FRn.put_th(th, rest))), Wr.Got{compacted, FRn.put_th(th, rest)}, Wire.wire_bool_round_trip(compacted, FRn.put_th(th, rest))) : {FRn.get_ask.c2.f0(_) == Wr.Got{FRn.AskPrepare{compacted, th}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<RnDecision.Th>, FRn.get_th(FRn.put_th(th, rest)), Wr.Got{th, rest}, rk.rt_th(th, rest)) : {FRn.get_ask.c2.f1(compacted, _) == Wr.Got{FRn.AskPrepare{compacted, th}, rest} : Wr.Dec<FRn.Ask>}
      {==}
    case FRn.AskCompact{+over, +got}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(over, FRn.put_got(got, rest))), Wr.Got{over, FRn.put_got(got, rest)}, Wire.wire_bool_round_trip(over, FRn.put_got(got, rest))) : {FRn.get_ask.c3.f0(_) == Wr.Got{FRn.AskCompact{over, got}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<RnState.Got>, FRn.get_got(FRn.put_got(got, rest)), Wr.Got{got, rest}, rk.rt_got(got, rest)) : {FRn.get_ask.c3.f1(over, _) == Wr.Got{FRn.AskCompact{over, got}, rest} : Wr.Dec<FRn.Ask>}
      {==}
    case FRn.AskRound{+l, +count, +stops, +reset}:
      +hl0 = rk.and_l(Run.run.lim_fits(l), LawsBase.wire_fits(count), h)
      +hr0 = rk.and_r(Run.run.lim_fits(l), LawsBase.wire_fits(count), h)
      %Equal.sym(Wr.Dec<RnDecision.Lim>, FRn.get_lim(FRn.put_lim(l, Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest))))), Wr.Got{l, Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest)))}, rk.rt_lim(l, Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest))), hl0)) : {FRn.get_ask.c4.f0(_) == Wr.Got{FRn.AskRound{l, count, stops, reset}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest)))), Wr.Got{count, Wr.put_bool(stops, Wr.put_bool(reset, rest))}, Wire.wire_nat_round_trip(count, Wr.put_bool(stops, Wr.put_bool(reset, rest)), hr0)) : {FRn.get_ask.c4.f1(l, _) == Wr.Got{FRn.AskRound{l, count, stops, reset}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(stops, Wr.put_bool(reset, rest))), Wr.Got{stops, Wr.put_bool(reset, rest)}, Wire.wire_bool_round_trip(stops, Wr.put_bool(reset, rest))) : {FRn.get_ask.c4.f2(l, count, _) == Wr.Got{FRn.AskRound{l, count, stops, reset}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(reset, rest)), Wr.Got{reset, rest}, Wire.wire_bool_round_trip(reset, rest)) : {FRn.get_ask.c4.f3(l, count, stops, _) == Wr.Got{FRn.AskRound{l, count, stops, reset}, rest} : Wr.Dec<FRn.Ask>}
      {==}
    case FRn.AskRecover{+rc, +s, +k, +row}:
      +hl0 = rk.and_l(Run.run.rcfg_fits(rc), Bool.and(Run.run.stuck_fits(s), LawsBase.wire_fits(row)), h)
      +hr0 = rk.and_r(Run.run.rcfg_fits(rc), Bool.and(Run.run.stuck_fits(s), LawsBase.wire_fits(row)), h)
      +hl1 = rk.and_l(Run.run.stuck_fits(s), LawsBase.wire_fits(row), hr0)
      +hr1 = rk.and_r(Run.run.stuck_fits(s), LawsBase.wire_fits(row), hr0)
      %Equal.sym(Wr.Dec<RnRecovery.RCfg>, FRn.get_rcfg(FRn.put_rcfg(rc, FRn.put_stuck(s, FRn.put_rk(k, Wr.put_nat(row, rest))))), Wr.Got{rc, FRn.put_stuck(s, FRn.put_rk(k, Wr.put_nat(row, rest)))}, rk.rt_rcfg(rc, FRn.put_stuck(s, FRn.put_rk(k, Wr.put_nat(row, rest))), hl0)) : {FRn.get_ask.c5.f0(_) == Wr.Got{FRn.AskRecover{rc, s, k, row}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<RnDecision.Stuck>, FRn.get_stuck(FRn.put_stuck(s, FRn.put_rk(k, Wr.put_nat(row, rest)))), Wr.Got{s, FRn.put_rk(k, Wr.put_nat(row, rest))}, rk.rt_stuck(s, FRn.put_rk(k, Wr.put_nat(row, rest)), hl1)) : {FRn.get_ask.c5.f1(rc, _) == Wr.Got{FRn.AskRecover{rc, s, k, row}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<RnRecovery.Rk>, FRn.get_rk(FRn.put_rk(k, Wr.put_nat(row, rest))), Wr.Got{k, Wr.put_nat(row, rest)}, rk.rt_rk(k, Wr.put_nat(row, rest))) : {FRn.get_ask.c5.f2(rc, s, _) == Wr.Got{FRn.AskRecover{rc, s, k, row}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(row, rest)), Wr.Got{row, rest}, Wire.wire_nat_round_trip(row, rest, hr1)) : {FRn.get_ask.c5.f3(rc, s, k, _) == Wr.Got{FRn.AskRecover{rc, s, k, row}, rest} : Wr.Dec<FRn.Ask>}
      {==}
    case FRn.AskPoll{+retryable, +failures, +retries}:
      +hl0 = rk.and_l(LawsBase.wire_fits(failures), LawsBase.wire_fits(retries), h)
      +hr0 = rk.and_r(LawsBase.wire_fits(failures), LawsBase.wire_fits(retries), h)
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(retryable, Wr.put_nat(failures, Wr.put_nat(retries, rest)))), Wr.Got{retryable, Wr.put_nat(failures, Wr.put_nat(retries, rest))}, Wire.wire_bool_round_trip(retryable, Wr.put_nat(failures, Wr.put_nat(retries, rest)))) : {FRn.get_ask.c6.f0(_) == Wr.Got{FRn.AskPoll{retryable, failures, retries}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(failures, Wr.put_nat(retries, rest))), Wr.Got{failures, Wr.put_nat(retries, rest)}, Wire.wire_nat_round_trip(failures, Wr.put_nat(retries, rest), hl0)) : {FRn.get_ask.c6.f1(retryable, _) == Wr.Got{FRn.AskPoll{retryable, failures, retries}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(retries, rest)), Wr.Got{retries, rest}, Wire.wire_nat_round_trip(retries, rest, hr0)) : {FRn.get_ask.c6.f2(retryable, failures, _) == Wr.Got{FRn.AskPoll{retryable, failures, retries}, rest} : Wr.Dec<FRn.Ask>}
      {==}
