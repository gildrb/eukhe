# eukhe: lemmas the proofs of area run share

import Base
import ../../bend/run.bend as Rn
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../bend/ffi_run.bend as FRn
import ../../LAWS.bend as Laws
import ../base.bend as L
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

def Inv(+cap: Nat, +ph: Rn.Ph, +r: Nat, +k: Nat) -> Type:
  Or({Rn.Ph.capped(ph) == False{} : Bool}, {k == Nat.max(cap, 1n) : Nat}) & Or({Rn.Ph.failed(ph) == True{} : Bool}, {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat})

def InvS(+cfg: Rn.Cfg, +s: Rn.St, +k: Nat) -> Type:
  Inv(Rn.Cfg.cap(cfg), Rn.St.ph(s), Rn.St.r(s), k)

# a live run has not failed
def cap_of(-T: Type, o: Or({False{} == True{} : Bool}, T)) -> T:
  match o:
    case Inl{x}:
      L.absurd(T, x)
    case Inr{y}:
      y

def cap_next(n: Nat, -s: Nat, -cap: Nat, capv: {Nat.add(n, 2n+s) == cap : Nat}) -> {1n+Nat.add(n, 1n+s) == cap : Nat}:
  %capv : {1n+Nat.add(n, 1n+s) == _ : Nat}
  L.add_succ_r(n, 1n+s)

# the round that meets the cap is the max(cap, 1)th
def one_more(+n: Nat, -m: Nat, capv: {Nat.add(n, 1n+0n) == m : Nat}) -> {1n+n == m : Nat}:
  %capv : {1n+n == _ : Nat}
  %L.add_succ_r(n, 0n) : {1n+n == _ : Nat}
  %Equal.sym(Nat, Nat.add(n, 0n), n, L.add_zero(n)) : {1n+n == 1n+_ : Nat}
  {==}

def inv_round(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reset: Bool, r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(Rn.Cfg{cap, P, A, N}, Rn.round(Rn.Cfg{cap, P, A, N}, reset, r, c, a, n, p), 1n+k):
  match reset r:
    case reset 0n:
      (Inr{one_more(k, Nat.max(cap, 1n), capv)}, Inl{{==}})
    case True{} 1n+s:
      (Inl{{==}}, Inr{cap_next(k, s, Nat.max(cap, 1n), capv)})
    case False{} 1n+s:
      (Inl{{==}}, Inr{cap_next(k, s, Nat.max(cap, 1n), capv)})

def inv_tools(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, fin: Rn.Fin, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(Rn.Cfg{cap, P, A, N}, Rn.tools(Rn.Cfg{cap, P, A, N}, fin, r, c, a, n, p), Rn.counted.go(fin, k)):
  match fin:
    case Rn.Stops{}:
      (Inl{{==}}, Inr{capv})
    case Rn.Goes{}:
      inv_round(cap, P, A, N, False{}, r, c, a, n, p, k, capv)
    case Rn.Resets{}:
      inv_round(cap, P, A, N, True{}, r, c, a, n, p, k, capv)

def inv_prepare_cut(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(Rn.Cfg{cap, P, A, N}, Rn.prepare.cut(Rn.Cfg{cap, P, A, N}, cut, r, c, a, n), k):
  match cut c:
    case True{} 1n+d:
      (Inl{{==}}, Inr{capv})
    case True{} 0n:
      (Inl{{==}}, Inr{capv})
    case False{} c:
      (Inl{{==}}, Inr{capv})

def inv_prepare(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: Rn.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(Rn.Cfg{cap, P, A, N}, Rn.prepare(Rn.Cfg{cap, P, A, N}, reply, r, c, a, n), k):
  match reply:
    case Rn.Overflow{cut}:
      inv_prepare_cut(cap, P, A, N, cut, r, c, a, n, k, capv)
    case Rn.Plain{}:
      (Inl{{==}}, Inr{capv})
    case Rn.Calls{}:
      (Inl{{==}}, Inr{capv})
    case Rn.Deferred{}:
      (Inl{{==}}, Inr{capv})
    case Rn.Error{retryable, noted}:
      (Inl{{==}}, Inr{capv})

def inv_retry(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, +r: Nat, +c: Nat, a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(Rn.Cfg{cap, P, A, N}, Rn.retry(Rn.Cfg{cap, P, A, N}, retryable, r, c, a, n, p), k):
  match retryable a:
    case True{} 1n+b:
      (Inl{{==}}, Inr{capv})
    case True{} 0n:
      (Inl{{==}}, Inl{{==}})
    case False{} a:
      (Inl{{==}}, Inl{{==}})

def inv_note(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, +r: Nat, +c: Nat, +a: Nat, n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(Rn.Cfg{cap, P, A, N}, Rn.note(Rn.Cfg{cap, P, A, N}, r, c, a, n, p), k):
  match n:
    case 1n+m:
      (Inl{{==}}, Inr{capv})
    case 0n:
      (Inl{{==}}, Inl{{==}})

def inv_error(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, retryable: Bool, noted: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(Rn.Cfg{cap, P, A, N}, Rn.error(Rn.Cfg{cap, P, A, N}, retryable, noted, r, c, a, n, p), k):
  match noted:
    case True{}:
      inv_note(cap, P, A, N, r, c, a, n, p, k, capv)
    case False{}:
      inv_retry(cap, P, A, N, retryable, r, c, a, n, p, k, capv)

def inv_overflow(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, cut: Bool, +r: Nat, c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(Rn.Cfg{cap, P, A, N}, Rn.overflow(cut, r, c, a, n, p), k):
  match cut c:
    case True{} 1n+d:
      (Inl{{==}}, Inr{capv})
    case True{} 0n:
      (Inl{{==}}, Inl{{==}})
    case False{} c:
      (Inl{{==}}, Inl{{==}})

def inv_call(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, reply: Rn.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(Rn.Cfg{cap, P, A, N}, Rn.call(Rn.Cfg{cap, P, A, N}, reply, r, c, a, n, p), k):
  match reply:
    case Rn.Plain{}:
      (Inl{{==}}, Inr{capv})
    case Rn.Calls{}:
      (Inl{{==}}, Inr{capv})
    case Rn.Deferred{}:
      match p:
        case 0n:
          (Inl{{==}}, Inl{{==}})
        case 1n+q:
          (Inl{{==}}, Inr{capv})
    case Rn.Error{retryable, noted}:
      inv_error(cap, P, A, N, retryable, noted, r, c, a, n, p, k, capv)
    case Rn.Overflow{cut}:
      inv_overflow(cap, P, A, N, cut, r, c, a, n, p, k, capv)

def inv_compact(+cap: Nat, +P: Nat, +A: Nat, +N: Nat, over: Bool, got: Rn.Got, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, capv: {Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}) -> InvS(Rn.Cfg{cap, P, A, N}, Rn.compact(Rn.Cfg{cap, P, A, N}, over, got, r, c, a, n, p), k):
  match over got:
    case over Rn.Built{}:
      (Inl{{==}}, Inr{capv})
    case True{} Rn.Kept{}:
      (Inl{{==}}, Inl{{==}})
    case False{} Rn.Kept{}:
      (Inl{{==}}, Inr{capv})
    case over Rn.Broke{}:
      (Inl{{==}}, Inl{{==}})

# one input keeps the invariant
def inv_step(+cfg: Rn.Cfg, +s: Rn.St, +k: Nat, +e: Rn.Ev, i: InvS(cfg, s, k)) -> InvS(cfg, Rn.step(cfg, s, e), Rn.counted(Rn.St.ph(s), e, k)):
  match cfg:
    case Rn.Cfg{cap, P, A, N}:
      match s:
        case Rn.St{ph, r, c, a, n, p}:
          match ph e:
            case Rn.Answered{} e:
              i
            case Rn.Aborted{} e:
              i
            case Rn.Failed{why} e:
              i
            case Rn.Prepare{} Rn.Abort{}:
              (cp, co) = i
              (Inl{{==}}, Inr{cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co)})
            case Rn.Call{} Rn.Abort{}:
              (cp, co) = i
              (Inl{{==}}, Inr{cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co)})
            case Rn.Compact{over} Rn.Abort{}:
              (cp, co) = i
              (Inl{{==}}, Inr{cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co)})
            case Rn.Tools{} Rn.Abort{}:
              (cp, co) = i
              (Inl{{==}}, Inr{cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co)})
            case Rn.Prepare{} Rn.Go{reply, fin, got}:
              (cp, co) = i
              inv_prepare(cap, P, A, N, reply, r, c, a, n, k, cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co))
            case Rn.Call{} Rn.Go{reply, fin, got}:
              (cp, co) = i
              inv_call(cap, P, A, N, reply, r, c, a, n, p, k, cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co))
            case Rn.Compact{over} Rn.Go{reply, fin, got}:
              (cp, co) = i
              inv_compact(cap, P, A, N, over, got, r, c, a, n, p, k, cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co))
            case Rn.Tools{} Rn.Go{reply, fin, got}:
              (cp, co) = i
              inv_tools(cap, P, A, N, fin, r, c, a, n, p, k, cap_of({Nat.add(k, 1n+r) == Nat.max(cap, 1n) : Nat}, co))

def inv_run(evs: List<&2, Rn.Ev>, +cfg: Rn.Cfg, +s: Rn.St, +k: Nat, i: InvS(cfg, s, k)) -> InvS(cfg, Rn.run.go(evs, cfg, s), Rn.rounds.go(evs, cfg, s, k)):
  match evs:
    case Nil{}:
      i
    case +e <> rest:
      inv_run(rest, cfg, Rn.step(cfg, s, e), Rn.counted(Rn.St.ph(s), e, k), inv_step(cfg, s, k, e, i))

# a run starts with the invariant
def inv_init(+cfg: Rn.Cfg) -> InvS(cfg, Rn.init(cfg), 0n):
  match cfg:
    case Rn.Cfg{cap, P, A, N}:
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

def rk.wait(+cfg: Rn.Cfg, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +w: Nat, +x: Nat) -> {Rn.Then.ph(False{}, Rn.St.ph(Rn.call(cfg, Rn.Deferred{}, r, c, a, n, Nat.sub(w, x)))) == Laws.rust.wait(Nat.is_lt(x, w)) : Rn.Then}:
  match w x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+v 0n:
      {==}
    case 1n+v 1n+y:
      rk.wait(cfg, r, c, a, n, v, y)

def rk.notes(+cfg: Rn.Cfg, +r: Nat, +c: Nat, +a: Nat, +p: Nat, +m: Nat, +x: Nat) -> {Rn.Then.ph(True{}, Rn.St.ph(Rn.note(cfg, r, c, a, Nat.sub(m, x), p))) == Laws.rust.noted(Nat.is_lt(x, m)) : Rn.Then}:
  match m x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+v 0n:
      {==}
    case 1n+v 1n+y:
      rk.notes(cfg, r, c, a, p, v, y)

def rk.retry(+cfg: Rn.Cfg, +r: Nat, +c: Nat, +n: Nat, +p: Nat, +m: Nat, +x: Nat) -> {Rn.Then.ph(False{}, Rn.St.ph(Rn.retry(cfg, True{}, r, c, Nat.sub(m, x), n, p))) == Laws.rust.retry(Nat.is_lt(x, m)) : Rn.Then}:
  match m x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+v 0n:
      {==}
    case 1n+v 1n+y:
      rk.retry(cfg, r, c, n, p, v, y)

def rk.over(+cfg: Rn.Cfg, +r: Nat, +a: Nat, +n: Nat, +p: Nat, +compacted: Bool, +cut: Bool) -> {Rn.Then.ph(False{}, Rn.St.ph(Rn.call(cfg, Rn.Overflow{cut}, r, Rn.c.of(compacted), a, n, p))) == Laws.rust.over(Bool.and(cut, Bool.not(compacted))) : Rn.Then}:
  match compacted cut:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def rk.run_reply_is_the_rust_rule(+l: Rn.Lim, +t: Rn.At, +reply: Rn.Reply) -> {Rn.decide.reply(l, t, reply) == Laws.rust.after_reply(l, t, reply) : Rn.Then}:
  match l:
    case Rn.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case Rn.At{+attempt, +notes, +waited, +compacted}:
          match reply:
            case Rn.Plain{}:
              {==}
            case Rn.Calls{}:
              {==}
            case Rn.Deferred{}:
              rk.wait(Rn.Cfg{rounds, wait, retries, most}, 0n, Rn.c.of(compacted), Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes)), Nat.sub(most, notes), wait, waited)
            case Rn.Error{retryable, noted}:
              match retryable noted:
                case retryable True{}:
                  rk.notes(Rn.Cfg{rounds, wait, retries, most}, 0n, Rn.c.of(compacted), Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes)), Nat.sub(wait, waited), most, notes)
                case True{} False{}:
                  rk.retry(Rn.Cfg{rounds, wait, retries, most}, 0n, Rn.c.of(compacted), Nat.sub(most, notes), Nat.sub(wait, waited), retries, Nat.sub(Nat.sub(attempt, 1n), notes))
                case False{} False{}:
                  {==}
            case Rn.Overflow{cut}:
              rk.over(Rn.Cfg{rounds, wait, retries, most}, 0n, Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes)), Nat.sub(most, notes), Nat.sub(wait, waited), compacted, cut)

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

def rk.later(+b: Bool, +left: Nat, +gap: Nat) -> {Laws.rust.later(Laws.rust.wait(b)) == R.Step.act(R.live.pending(Bool.not(b), left, gap)) : R.Act}:
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

def rk.rt_lim(x: Rn.Lim, +rest: String, +h: {Laws.run.lim_fits(x) == True{} : Bool}) -> {FRn.get_lim(FRn.put_lim(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Lim>}:
  match x:
    case Rn.Lim{+rounds, +wait, +retries, +notes}:
      +hl0 = rk.and_l(Laws.wire_fits(rounds), Bool.and(Laws.wire_fits(wait), Bool.and(Laws.wire_fits(retries), Laws.wire_fits(notes))), h)
      +hr0 = rk.and_r(Laws.wire_fits(rounds), Bool.and(Laws.wire_fits(wait), Bool.and(Laws.wire_fits(retries), Laws.wire_fits(notes))), h)
      +hl1 = rk.and_l(Laws.wire_fits(wait), Bool.and(Laws.wire_fits(retries), Laws.wire_fits(notes)), hr0)
      +hr1 = rk.and_r(Laws.wire_fits(wait), Bool.and(Laws.wire_fits(retries), Laws.wire_fits(notes)), hr0)
      +hl2 = rk.and_l(Laws.wire_fits(retries), Laws.wire_fits(notes), hr1)
      +hr2 = rk.and_r(Laws.wire_fits(retries), Laws.wire_fits(notes), hr1)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(rounds, Wr.put_nat(wait, Wr.put_nat(retries, Wr.put_nat(notes, rest))))), Wr.Got{rounds, Wr.put_nat(wait, Wr.put_nat(retries, Wr.put_nat(notes, rest)))}, Laws.wire_nat_round_trip(rounds, Wr.put_nat(wait, Wr.put_nat(retries, Wr.put_nat(notes, rest))), hl0)) : {FRn.get_lim.f0(_) == Wr.Got{Rn.Lim{rounds, wait, retries, notes}, rest} : Wr.Dec<Rn.Lim>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(wait, Wr.put_nat(retries, Wr.put_nat(notes, rest)))), Wr.Got{wait, Wr.put_nat(retries, Wr.put_nat(notes, rest))}, Laws.wire_nat_round_trip(wait, Wr.put_nat(retries, Wr.put_nat(notes, rest)), hl1)) : {FRn.get_lim.f1(rounds, _) == Wr.Got{Rn.Lim{rounds, wait, retries, notes}, rest} : Wr.Dec<Rn.Lim>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(retries, Wr.put_nat(notes, rest))), Wr.Got{retries, Wr.put_nat(notes, rest)}, Laws.wire_nat_round_trip(retries, Wr.put_nat(notes, rest), hl2)) : {FRn.get_lim.f2(rounds, wait, _) == Wr.Got{Rn.Lim{rounds, wait, retries, notes}, rest} : Wr.Dec<Rn.Lim>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(notes, rest)), Wr.Got{notes, rest}, Laws.wire_nat_round_trip(notes, rest, hr2)) : {FRn.get_lim.f3(rounds, wait, retries, _) == Wr.Got{Rn.Lim{rounds, wait, retries, notes}, rest} : Wr.Dec<Rn.Lim>}
      {==}

def rk.rt_at(x: Rn.At, +rest: String, +h: {Laws.run.at_fits(x) == True{} : Bool}) -> {FRn.get_at(FRn.put_at(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.At>}:
  match x:
    case Rn.At{+attempt, +notes, +waited, +compacted}:
      +hl0 = rk.and_l(Laws.wire_fits(attempt), Bool.and(Laws.wire_fits(notes), Laws.wire_fits(waited)), h)
      +hr0 = rk.and_r(Laws.wire_fits(attempt), Bool.and(Laws.wire_fits(notes), Laws.wire_fits(waited)), h)
      +hl1 = rk.and_l(Laws.wire_fits(notes), Laws.wire_fits(waited), hr0)
      +hr1 = rk.and_r(Laws.wire_fits(notes), Laws.wire_fits(waited), hr0)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(attempt, Wr.put_nat(notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest))))), Wr.Got{attempt, Wr.put_nat(notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest)))}, Laws.wire_nat_round_trip(attempt, Wr.put_nat(notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest))), hl0)) : {FRn.get_at.f0(_) == Wr.Got{Rn.At{attempt, notes, waited, compacted}, rest} : Wr.Dec<Rn.At>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest)))), Wr.Got{notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest))}, Laws.wire_nat_round_trip(notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest)), hl1)) : {FRn.get_at.f1(attempt, _) == Wr.Got{Rn.At{attempt, notes, waited, compacted}, rest} : Wr.Dec<Rn.At>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(waited, Wr.put_bool(compacted, rest))), Wr.Got{waited, Wr.put_bool(compacted, rest)}, Laws.wire_nat_round_trip(waited, Wr.put_bool(compacted, rest), hr1)) : {FRn.get_at.f2(attempt, notes, _) == Wr.Got{Rn.At{attempt, notes, waited, compacted}, rest} : Wr.Dec<Rn.At>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(compacted, rest)), Wr.Got{compacted, rest}, Laws.wire_bool_round_trip(compacted, rest)) : {FRn.get_at.f3(attempt, notes, waited, _) == Wr.Got{Rn.At{attempt, notes, waited, compacted}, rest} : Wr.Dec<Rn.At>}
      {==}

def rk.rt_reply(x: Rn.Reply, +rest: String) -> {FRn.get_reply(FRn.put_reply(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Reply>}:
  match x:
    case Rn.Plain{}:
      {==}
    case Rn.Calls{}:
      {==}
    case Rn.Deferred{}:
      {==}
    case Rn.Error{+retryable, +noted}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(retryable, Wr.put_bool(noted, rest))), Wr.Got{retryable, Wr.put_bool(noted, rest)}, Laws.wire_bool_round_trip(retryable, Wr.put_bool(noted, rest))) : {FRn.get_reply.c3.f0(_) == Wr.Got{Rn.Error{retryable, noted}, rest} : Wr.Dec<Rn.Reply>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(noted, rest)), Wr.Got{noted, rest}, Laws.wire_bool_round_trip(noted, rest)) : {FRn.get_reply.c3.f1(retryable, _) == Wr.Got{Rn.Error{retryable, noted}, rest} : Wr.Dec<Rn.Reply>}
      {==}
    case Rn.Overflow{+cut}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(cut, rest)), Wr.Got{cut, rest}, Laws.wire_bool_round_trip(cut, rest)) : {FRn.get_reply.c4.f0(_) == Wr.Got{Rn.Overflow{cut}, rest} : Wr.Dec<Rn.Reply>}
      {==}

def rk.rt_ended(x: Rn.Ended, +rest: String) -> {FRn.get_ended(FRn.put_ended(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Ended>}:
  match x:
    case Rn.Ended{+text, +calls}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(text, Wr.put_bool(calls, rest))), Wr.Got{text, Wr.put_bool(calls, rest)}, Laws.wire_bool_round_trip(text, Wr.put_bool(calls, rest))) : {FRn.get_ended.f0(_) == Wr.Got{Rn.Ended{text, calls}, rest} : Wr.Dec<Rn.Ended>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(calls, rest)), Wr.Got{calls, rest}, Laws.wire_bool_round_trip(calls, rest)) : {FRn.get_ended.f1(text, _) == Wr.Got{Rn.Ended{text, calls}, rest} : Wr.Dec<Rn.Ended>}
      {==}

def rk.rt_th(x: Rn.Th, +rest: String) -> {FRn.get_th(FRn.put_th(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Th>}:
  match x:
    case Rn.Under{}:
      {==}
    case Rn.Background{}:
      {==}
    case Rn.Blocking{}:
      {==}

def rk.rt_got(x: Rn.Got, +rest: String) -> {FRn.get_got(FRn.put_got(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Got>}:
  match x:
    case Rn.Built{}:
      {==}
    case Rn.Kept{}:
      {==}
    case Rn.Broke{}:
      {==}

def rk.rt_rcfg(x: Rn.RCfg, +rest: String, +h: {Laws.run.rcfg_fits(x) == True{} : Bool}) -> {FRn.get_rcfg(FRn.put_rcfg(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.RCfg>}:
  match x:
    case Rn.RCfg{+long, +leak, +redirect, +repeat}:
      +hl0 = rk.and_l(Laws.wire_fits(long), Bool.and(Laws.wire_fits(leak), Bool.and(Laws.wire_fits(redirect), Laws.wire_fits(repeat))), h)
      +hr0 = rk.and_r(Laws.wire_fits(long), Bool.and(Laws.wire_fits(leak), Bool.and(Laws.wire_fits(redirect), Laws.wire_fits(repeat))), h)
      +hl1 = rk.and_l(Laws.wire_fits(leak), Bool.and(Laws.wire_fits(redirect), Laws.wire_fits(repeat)), hr0)
      +hr1 = rk.and_r(Laws.wire_fits(leak), Bool.and(Laws.wire_fits(redirect), Laws.wire_fits(repeat)), hr0)
      +hl2 = rk.and_l(Laws.wire_fits(redirect), Laws.wire_fits(repeat), hr1)
      +hr2 = rk.and_r(Laws.wire_fits(redirect), Laws.wire_fits(repeat), hr1)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(long, Wr.put_nat(leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest))))), Wr.Got{long, Wr.put_nat(leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest)))}, Laws.wire_nat_round_trip(long, Wr.put_nat(leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest))), hl0)) : {FRn.get_rcfg.f0(_) == Wr.Got{Rn.RCfg{long, leak, redirect, repeat}, rest} : Wr.Dec<Rn.RCfg>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest)))), Wr.Got{leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest))}, Laws.wire_nat_round_trip(leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest)), hl1)) : {FRn.get_rcfg.f1(long, _) == Wr.Got{Rn.RCfg{long, leak, redirect, repeat}, rest} : Wr.Dec<Rn.RCfg>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(redirect, Wr.put_nat(repeat, rest))), Wr.Got{redirect, Wr.put_nat(repeat, rest)}, Laws.wire_nat_round_trip(redirect, Wr.put_nat(repeat, rest), hl2)) : {FRn.get_rcfg.f2(long, leak, _) == Wr.Got{Rn.RCfg{long, leak, redirect, repeat}, rest} : Wr.Dec<Rn.RCfg>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(repeat, rest)), Wr.Got{repeat, rest}, Laws.wire_nat_round_trip(repeat, rest, hr2)) : {FRn.get_rcfg.f3(long, leak, redirect, _) == Wr.Got{Rn.RCfg{long, leak, redirect, repeat}, rest} : Wr.Dec<Rn.RCfg>}
      {==}

def rk.rt_stuck(x: Rn.Stuck, +rest: String, +h: {Laws.run.stuck_fits(x) == True{} : Bool}) -> {FRn.get_stuck(FRn.put_stuck(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Stuck>}:
  match x:
    case Rn.Truncated{}:
      {==}
    case Rn.Leaked{}:
      {==}
    case Rn.Repeats{+before}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(before, rest)), Wr.Got{before, rest}, Laws.wire_nat_round_trip(before, rest, h)) : {FRn.get_stuck.c2.f0(_) == Wr.Got{Rn.Repeats{before}, rest} : Wr.Dec<Rn.Stuck>}
      {==}

def rk.rt_rk(x: Rn.Rk, +rest: String) -> {FRn.get_rk(FRn.put_rk(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Rk>}:
  match x:
    case Rn.Free{}:
      {==}
    case Rn.Longs{}:
      {==}
    case Rn.Leaks{}:
      {==}
    case Rn.Loops{}:
      {==}

def rk.rt_ask(x: FRn.Ask, +rest: String, +h: {Laws.run.ask_fits(x) == True{} : Bool}) -> {FRn.get_ask(FRn.put_ask(x, rest)) == Wr.Got{x, rest} : Wr.Dec<FRn.Ask>}:
  match x:
    case FRn.AskReply{+l, +t, +reply}:
      +hl0 = rk.and_l(Laws.run.lim_fits(l), Laws.run.at_fits(t), h)
      +hr0 = rk.and_r(Laws.run.lim_fits(l), Laws.run.at_fits(t), h)
      %Equal.sym(Wr.Dec<Rn.Lim>, FRn.get_lim(FRn.put_lim(l, FRn.put_at(t, FRn.put_reply(reply, rest)))), Wr.Got{l, FRn.put_at(t, FRn.put_reply(reply, rest))}, rk.rt_lim(l, FRn.put_at(t, FRn.put_reply(reply, rest)), hl0)) : {FRn.get_ask.c0.f0(_) == Wr.Got{FRn.AskReply{l, t, reply}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Rn.At>, FRn.get_at(FRn.put_at(t, FRn.put_reply(reply, rest))), Wr.Got{t, FRn.put_reply(reply, rest)}, rk.rt_at(t, FRn.put_reply(reply, rest), hr0)) : {FRn.get_ask.c0.f1(l, _) == Wr.Got{FRn.AskReply{l, t, reply}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Rn.Reply>, FRn.get_reply(FRn.put_reply(reply, rest)), Wr.Got{reply, rest}, rk.rt_reply(reply, rest)) : {FRn.get_ask.c0.f2(l, t, _) == Wr.Got{FRn.AskReply{l, t, reply}, rest} : Wr.Dec<FRn.Ask>}
      {==}
    case FRn.AskEnded{+m}:
      %Equal.sym(Wr.Dec<Rn.Ended>, FRn.get_ended(FRn.put_ended(m, rest)), Wr.Got{m, rest}, rk.rt_ended(m, rest)) : {FRn.get_ask.c1.f0(_) == Wr.Got{FRn.AskEnded{m}, rest} : Wr.Dec<FRn.Ask>}
      {==}
    case FRn.AskPrepare{+compacted, +th}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(compacted, FRn.put_th(th, rest))), Wr.Got{compacted, FRn.put_th(th, rest)}, Laws.wire_bool_round_trip(compacted, FRn.put_th(th, rest))) : {FRn.get_ask.c2.f0(_) == Wr.Got{FRn.AskPrepare{compacted, th}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Rn.Th>, FRn.get_th(FRn.put_th(th, rest)), Wr.Got{th, rest}, rk.rt_th(th, rest)) : {FRn.get_ask.c2.f1(compacted, _) == Wr.Got{FRn.AskPrepare{compacted, th}, rest} : Wr.Dec<FRn.Ask>}
      {==}
    case FRn.AskCompact{+over, +got}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(over, FRn.put_got(got, rest))), Wr.Got{over, FRn.put_got(got, rest)}, Laws.wire_bool_round_trip(over, FRn.put_got(got, rest))) : {FRn.get_ask.c3.f0(_) == Wr.Got{FRn.AskCompact{over, got}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Rn.Got>, FRn.get_got(FRn.put_got(got, rest)), Wr.Got{got, rest}, rk.rt_got(got, rest)) : {FRn.get_ask.c3.f1(over, _) == Wr.Got{FRn.AskCompact{over, got}, rest} : Wr.Dec<FRn.Ask>}
      {==}
    case FRn.AskRound{+l, +count, +stops, +reset}:
      +hl0 = rk.and_l(Laws.run.lim_fits(l), Laws.wire_fits(count), h)
      +hr0 = rk.and_r(Laws.run.lim_fits(l), Laws.wire_fits(count), h)
      %Equal.sym(Wr.Dec<Rn.Lim>, FRn.get_lim(FRn.put_lim(l, Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest))))), Wr.Got{l, Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest)))}, rk.rt_lim(l, Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest))), hl0)) : {FRn.get_ask.c4.f0(_) == Wr.Got{FRn.AskRound{l, count, stops, reset}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest)))), Wr.Got{count, Wr.put_bool(stops, Wr.put_bool(reset, rest))}, Laws.wire_nat_round_trip(count, Wr.put_bool(stops, Wr.put_bool(reset, rest)), hr0)) : {FRn.get_ask.c4.f1(l, _) == Wr.Got{FRn.AskRound{l, count, stops, reset}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(stops, Wr.put_bool(reset, rest))), Wr.Got{stops, Wr.put_bool(reset, rest)}, Laws.wire_bool_round_trip(stops, Wr.put_bool(reset, rest))) : {FRn.get_ask.c4.f2(l, count, _) == Wr.Got{FRn.AskRound{l, count, stops, reset}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(reset, rest)), Wr.Got{reset, rest}, Laws.wire_bool_round_trip(reset, rest)) : {FRn.get_ask.c4.f3(l, count, stops, _) == Wr.Got{FRn.AskRound{l, count, stops, reset}, rest} : Wr.Dec<FRn.Ask>}
      {==}
    case FRn.AskRecover{+rc, +s, +k, +row}:
      +hl0 = rk.and_l(Laws.run.rcfg_fits(rc), Bool.and(Laws.run.stuck_fits(s), Laws.wire_fits(row)), h)
      +hr0 = rk.and_r(Laws.run.rcfg_fits(rc), Bool.and(Laws.run.stuck_fits(s), Laws.wire_fits(row)), h)
      +hl1 = rk.and_l(Laws.run.stuck_fits(s), Laws.wire_fits(row), hr0)
      +hr1 = rk.and_r(Laws.run.stuck_fits(s), Laws.wire_fits(row), hr0)
      %Equal.sym(Wr.Dec<Rn.RCfg>, FRn.get_rcfg(FRn.put_rcfg(rc, FRn.put_stuck(s, FRn.put_rk(k, Wr.put_nat(row, rest))))), Wr.Got{rc, FRn.put_stuck(s, FRn.put_rk(k, Wr.put_nat(row, rest)))}, rk.rt_rcfg(rc, FRn.put_stuck(s, FRn.put_rk(k, Wr.put_nat(row, rest))), hl0)) : {FRn.get_ask.c5.f0(_) == Wr.Got{FRn.AskRecover{rc, s, k, row}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Rn.Stuck>, FRn.get_stuck(FRn.put_stuck(s, FRn.put_rk(k, Wr.put_nat(row, rest)))), Wr.Got{s, FRn.put_rk(k, Wr.put_nat(row, rest))}, rk.rt_stuck(s, FRn.put_rk(k, Wr.put_nat(row, rest)), hl1)) : {FRn.get_ask.c5.f1(rc, _) == Wr.Got{FRn.AskRecover{rc, s, k, row}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Rn.Rk>, FRn.get_rk(FRn.put_rk(k, Wr.put_nat(row, rest))), Wr.Got{k, Wr.put_nat(row, rest)}, rk.rt_rk(k, Wr.put_nat(row, rest))) : {FRn.get_ask.c5.f2(rc, s, _) == Wr.Got{FRn.AskRecover{rc, s, k, row}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(row, rest)), Wr.Got{row, rest}, Laws.wire_nat_round_trip(row, rest, hr1)) : {FRn.get_ask.c5.f3(rc, s, k, _) == Wr.Got{FRn.AskRecover{rc, s, k, row}, rest} : Wr.Dec<FRn.Ask>}
      {==}
    case FRn.AskPoll{+retryable, +failures, +retries}:
      +hl0 = rk.and_l(Laws.wire_fits(failures), Laws.wire_fits(retries), h)
      +hr0 = rk.and_r(Laws.wire_fits(failures), Laws.wire_fits(retries), h)
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(retryable, Wr.put_nat(failures, Wr.put_nat(retries, rest)))), Wr.Got{retryable, Wr.put_nat(failures, Wr.put_nat(retries, rest))}, Laws.wire_bool_round_trip(retryable, Wr.put_nat(failures, Wr.put_nat(retries, rest)))) : {FRn.get_ask.c6.f0(_) == Wr.Got{FRn.AskPoll{retryable, failures, retries}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(failures, Wr.put_nat(retries, rest))), Wr.Got{failures, Wr.put_nat(retries, rest)}, Laws.wire_nat_round_trip(failures, Wr.put_nat(retries, rest), hl0)) : {FRn.get_ask.c6.f1(retryable, _) == Wr.Got{FRn.AskPoll{retryable, failures, retries}, rest} : Wr.Dec<FRn.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(retries, rest)), Wr.Got{retries, rest}, Laws.wire_nat_round_trip(retries, rest, hr0)) : {FRn.get_ask.c6.f2(retryable, failures, _) == Wr.Got{FRn.AskPoll{retryable, failures, retries}, rest} : Wr.Dec<FRn.Ask>}
      {==}
