# eukhe: the proof of LAW run_cut_names_the_last_sent
#
# PROOF: an invariant of the requests, by induction on the inputs (ct.run): every cut names the request sent last before it, and in the call phase the request sent last is the one the requests name (ct.Inv). Preparation that ends in a call sends that request; a noted reply cuts it; only a deferred reply stays in the call phase, with the requests unchanged.

import Base
import ../../bend/run/request.bend as RnRequest
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/model.bend as Run

# Equality
# --------

def ct.eq_refl(+n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      ct.eq_refl(m)

def ct.same_refl(+ctx: Nat, +note: Nat) -> {Run.same_req(RnRequest.Req{ctx, note}, RnRequest.Req{ctx, note}) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(ctx, ctx), True{}, ct.eq_refl(ctx)) : {Bool.and(_, Nat.is_eq(note, note)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(note, note), True{}, ct.eq_refl(note)) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# The invariant
# -------------
# Every cut of the log names the request sent before it, and while a
# request is out (the call phase) the newest request sent is the one the
# requests name (their context and note).

def ct.Head(ph: RnState.Ph, t: RnRequest.Reqs) -> Type:
  match ph:
    case RnState.Call{}:
      {Run.sent_last_is(RnRequest.Req{RnRequest.Reqs.ctx(t), RnRequest.Reqs.note(t)}, RnRequest.Reqs.log(t)) == True{} : Bool}
    case RnState.Prepare{}:
      Unit
    case RnState.Compact{over}:
      Unit
    case RnState.Tools{}:
      Unit
    case RnState.Answered{}:
      Unit
    case RnState.Aborted{}:
      Unit
    case RnState.Failed{why}:
      Unit

def ct.Inv(ph: RnState.Ph, t: RnRequest.Reqs) -> Type:
  {Run.cuts_name_sends(RnRequest.Reqs.log(t)) == True{} : Bool} & ct.Head(ph, t)

# a cut of the request sent last keeps every cut named
def ct.cut_ok(+q: RnRequest.Req, +log: List<&2, RnRequest.Sent>, hd: {Run.sent_last_is(q, log) == True{} : Bool}, cu: {Run.cuts_name_sends(log) == True{} : Bool}) -> {Run.cuts_name_sends(RnRequest.Cut{q} <> log) == True{} : Bool}:
  %Equal.sym(Bool, Run.sent_last_is(q, log), True{}, hd) : {Bool.and(_, Run.cuts_name_sends(log)) == True{} : Bool}
  cu

# Each input
# ----------

# preparation that ends in a call sends the request the requests name
def ct.prepared(pa: RnState.Ph, +ctx: Nat, n: Nat, +note: Nat, log: List<&2, RnRequest.Sent>, cu: {Run.cuts_name_sends(log) == True{} : Bool}) -> ct.Inv(pa, RnRequest.Reqs.prepared(pa, ctx, n, note, log)):
  match pa:
    case RnState.Call{}:
      (cu, ct.same_refl(ctx, note))
    case RnState.Prepare{}:
      (cu, Unit{})
    case RnState.Compact{over}:
      (cu, Unit{})
    case RnState.Tools{}:
      (cu, Unit{})
    case RnState.Answered{}:
      (cu, Unit{})
    case RnState.Aborted{}:
      (cu, Unit{})
    case RnState.Failed{why}:
      (cu, Unit{})

# a reply to the request out: a noted error cuts the request sent last;
# only a deferred reply stays in the call phase, with the requests as
# they were
# the requests a reply leaves outside the call phase keep every cut named
def ct.unit(-ctx: Nat, -k: Nat, -note: Nat, -log: List<&2, RnRequest.Sent>, i: ct.Inv(RnState.Call{}, RnRequest.Reqs{ctx, k, note, log})) -> {Run.cuts_name_sends(log) == True{} : Bool} & Unit:
  (cu, hd) = i
  (cu, Unit{})

# a noted reply cuts the request sent last
def ct.noted(+ctx: Nat, -k: Nat, +note: Nat, +log: List<&2, RnRequest.Sent>, i: ct.Inv(RnState.Call{}, RnRequest.Reqs{ctx, k, note, log})) -> {Run.cuts_name_sends(RnRequest.Cut{RnRequest.Req{ctx, note}} <> log) == True{} : Bool} & Unit:
  (cu, hd) = i
  (ct.cut_ok(RnRequest.Req{ctx, note}, log, hd, cu), Unit{})

def ct.call(+cfg: RnState.Cfg, reply: RnState.Reply, +r: Nat, c: Nat, a: Nat, n: Nat, p: Nat, +ctx: Nat, +k: Nat, +note: Nat, +log: List<&2, RnRequest.Sent>, i: ct.Inv(RnState.Call{}, RnRequest.Reqs{ctx, k, note, log})) -> ct.Inv(RnState.St.ph(RnStep.call(cfg, reply, r, c, a, n, p)), RnRequest.Reqs.reply(reply, ctx, k, note, log)):
  match reply:
    case RnState.Plain{}:
      ct.unit(ctx, k, note, log, i)
    case RnState.Calls{}:
      ct.unit(ctx, k, note, log, i)
    case RnState.Deferred{}:
      match p:
        case 0n:
          ct.unit(ctx, k, note, log, i)
        case 1n+q:
          i
    case RnState.Error{retryable, noted}:
      match retryable noted:
        case retryable True{}:
          match n:
            case 0n:
              ct.noted(ctx, k, note, log, i)
            case 1n+m:
              ct.noted(ctx, k, note, log, i)
        case True{} False{}:
          match a:
            case 0n:
              ct.unit(ctx, k, note, log, i)
            case 1n+b:
              ct.unit(ctx, k, note, log, i)
        case False{} False{}:
          ct.unit(ctx, k, note, log, i)
    case RnState.Overflow{cut}:
      match cut c:
        case True{} 1n+d:
          ct.unit(ctx, k, note, log, i)
        case True{} 0n:
          ct.unit(ctx, k, note, log, i)
        case False{} c:
          ct.unit(ctx, k, note, log, i)

# a compaction's end leaves the log as it was
def ct.compact(+cfg: RnState.Cfg, over: Bool, got: RnState.Got, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +ctx: Nat, +k: Nat, +note: Nat, +log: List<&2, RnRequest.Sent>, cu: {Run.cuts_name_sends(log) == True{} : Bool}) -> ct.Inv(RnState.St.ph(RnStep.compact(cfg, over, got, r, c, a, n, p)), RnRequest.Reqs.compacted(got, ctx, k, note, log)):
  match over got:
    case True{} RnState.Built{}:
      (cu, Unit{})
    case True{} RnState.Kept{}:
      (cu, Unit{})
    case True{} RnState.Broke{}:
      (cu, Unit{})
    case False{} RnState.Built{}:
      (cu, Unit{})
    case False{} RnState.Kept{}:
      (cu, Unit{})
    case False{} RnState.Broke{}:
      (cu, Unit{})

# a round's end leaves the log as it was
def ct.tools(+cfg: RnState.Cfg, fin: RnState.Fin, r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +ctx: Nat, +k: Nat, +note: Nat, +log: List<&2, RnRequest.Sent>, cu: {Run.cuts_name_sends(log) == True{} : Bool}) -> ct.Inv(RnState.St.ph(RnStep.tools(cfg, fin, r, c, a, n, p)), RnRequest.Reqs.rounded(RnState.St.ph(RnStep.tools(cfg, fin, r, c, a, n, p)), ctx, k, note, log)):
  match fin:
    case RnState.Stops{}:
      (cu, Unit{})
    case RnState.Goes{}:
      match r:
        case 0n:
          (cu, Unit{})
        case 1n+s:
          (cu, Unit{})
    case RnState.Resets{}:
      match r:
        case 0n:
          (cu, Unit{})
        case 1n+s:
          (cu, Unit{})

# the cuts of an invariant
def ct.cuts(-ph: RnState.Ph, -t: RnRequest.Reqs, i: ct.Inv(ph, t)) -> {Run.cuts_name_sends(RnRequest.Reqs.log(t)) == True{} : Bool}:
  (cu, hd) = i
  cu

# one input keeps the invariant
def ct.step(+cfg: RnState.Cfg, s: RnState.St, e: RnState.Ev, t: RnRequest.Reqs, i: ct.Inv(RnState.St.ph(s), t)) -> ct.Inv(RnState.St.ph(RnStep.step(cfg, s, e)), RnRequest.Reqs.step(RnState.St.ph(s), e, RnState.St.ph(RnStep.step(cfg, s, e)), t)):
  match s:
    case RnState.St{ph, r, c, a, n, p}:
      match ph:
        case RnState.Prepare{}:
          match e:
            case RnState.Abort{}:
              match t:
                case RnRequest.Reqs{ctx, k, note, log}:
                  ct.prepared(RnState.Aborted{}, ctx, k, note, log, ct.cuts(RnState.Prepare{}, RnRequest.Reqs{ctx, k, note, log}, i))
            case RnState.Go{reply, fin, got}:
              match t:
                case RnRequest.Reqs{ctx, k, note, log}:
                  ct.prepared(RnState.St.ph(RnStep.prepare(cfg, reply, r, c, a, n)), ctx, k, note, log, ct.cuts(RnState.Prepare{}, RnRequest.Reqs{ctx, k, note, log}, i))
        case RnState.Call{}:
          match e:
            case RnState.Abort{}:
              match t:
                case RnRequest.Reqs{ctx, k, note, log}:
                  ct.unit(ctx, k, note, log, i)
            case RnState.Go{reply, fin, got}:
              match t:
                case RnRequest.Reqs{ctx, k, note, log}:
                  ct.call(cfg, reply, r, c, a, n, p, ctx, k, note, log, i)
        case RnState.Compact{over}:
          match e:
            case RnState.Abort{}:
              match t:
                case RnRequest.Reqs{ctx, k, note, log}:
                  (ct.cuts(RnState.Compact{over}, RnRequest.Reqs{ctx, k, note, log}, i), Unit{})
            case RnState.Go{reply, fin, got}:
              match t:
                case RnRequest.Reqs{ctx, k, note, log}:
                  ct.compact(cfg, over, got, r, c, a, n, p, ctx, k, note, log, ct.cuts(RnState.Compact{over}, RnRequest.Reqs{ctx, k, note, log}, i))
        case RnState.Tools{}:
          match e:
            case RnState.Abort{}:
              match t:
                case RnRequest.Reqs{ctx, k, note, log}:
                  (ct.cuts(RnState.Tools{}, RnRequest.Reqs{ctx, k, note, log}, i), Unit{})
            case RnState.Go{reply, fin, got}:
              match t:
                case RnRequest.Reqs{ctx, k, note, log}:
                  ct.tools(cfg, fin, r, c, a, n, p, ctx, k, note, log, ct.cuts(RnState.Tools{}, RnRequest.Reqs{ctx, k, note, log}, i))
        case RnState.Answered{}:
          match t:
            case RnRequest.Reqs{ctx, k, note, log}:
              i
        case RnState.Aborted{}:
          match t:
            case RnRequest.Reqs{ctx, k, note, log}:
              i
        case RnState.Failed{why}:
          match t:
            case RnRequest.Reqs{ctx, k, note, log}:
              i

# by induction on the inputs
def ct.run(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, +t: RnRequest.Reqs, i: ct.Inv(RnState.St.ph(s), t)) -> {Run.cuts_name_sends(RnRequest.Reqs.log(RnRequest.reqs.go(evs, cfg, s, t))) == True{} : Bool}:
  match evs:
    case Nil{}:
      ct.cuts(RnState.St.ph(s), t, i)
    case +e <> rest:
      +s2 = RnStep.step(cfg, s, e)
      ct.run(rest, cfg, s2, RnRequest.Reqs.step(RnState.St.ph(s), e, RnState.St.ph(s2), t), ct.step(cfg, s, e, t, i))

def Run.run_cut_names_the_last_sent(cfg, evs):
  ct.run(evs, cfg, RnState.init(cfg), RnRequest.Reqs.init(), ({==}, Unit{}))
