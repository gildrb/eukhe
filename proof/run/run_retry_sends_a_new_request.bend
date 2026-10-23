# eukhe: the proof of LAW run_retry_sends_a_new_request

import Base
import ../../bend/run/request.bend as RnRequest
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run
import ../base/bool/misc.bend as LBoolMisc

def eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

# ---- retry ----

# proof_retry: the H4.7 retry laws of LAWS.bend about the requests of
# bend/run.bend.
#
# - retry_sends_a_new_request: an invariant of the requests (Ok), by
#   induction on the inputs. Every request the run cut is behind the
#   request it sends next: from an older context, or from this context
#   with an attempt up to the current one and another note. A noted error
#   moves the note to the next attempt, which no cut request of this
#   context names; a grown context leaves every cut request behind. So
#   the request the run sends is never one it cut.
# - cut_names_the_request: by computation.
# - note_is_never_logged: by computation on the note.

# Order
# -----

# a < b
def lt(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      False{}
    case 0n 1n+q:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      lt(p, q)

def lt_up(a: Nat, b: Nat, h: {lt(a, b) == True{} : Bool}) -> {lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LBoolMisc.absurd({lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      lt_up(p, q, h)

def lt_self(a: Nat) -> {lt(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      lt_self(p)

def lt_ne(a: Nat, b: Nat, h: {lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      LBoolMisc.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lt_ne(p, q, h)

# c = ctx, so c < ctx + 1
def lt_eq_up(+c: Nat, +ctx: Nat, e: {c == ctx : Nat}) -> {lt(c, 1n+ctx) == True{} : Bool}:
  %Equal.sym(Nat, c, ctx, e) : {lt(_, 1n+ctx) == True{} : Bool}
  lt_self(ctx)

# The invariant
# -------------

# a cut request q is behind the next request of context ctx, attempt n
# and note: from an older context, or from this one with an attempt up to
# n and another note
def OkQ(+ctx: Nat, +n: Nat, +note: Nat, q: RnRequest.Req) -> Type:
  match q:
    case RnRequest.Req{c, m}:
      Or({lt(c, ctx) == True{} : Bool}, Here(c, m, ctx, n, note))

# the request (c, m) is from context ctx, with an attempt up to n and
# another note
def Here(-c: Nat, -m: Nat, -ctx: Nat, -n: Nat, -note: Nat) -> Type:
  {c == ctx : Nat} & {lt(m, 1n+n) == True{} : Bool} & {Nat.is_eq(m, note) == False{} : Bool}

# every cut request of xs is
def OkL(+ctx: Nat, +n: Nat, +note: Nat, xs: List<&2, RnRequest.Sent>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case RnRequest.Sent{q} <> t:
      OkL(ctx, n, note, t)
    case RnRequest.Cut{q} <> t:
      OkQ(ctx, n, note, q) & OkL(ctx, n, note, t)

# the note names an attempt up to the current one, every cut request is
# behind the next request, and no sent request was cut before
def Ok3(+ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, RnRequest.Sent>) -> Type:
  {lt(note, 1n+n) == True{} : Bool} & OkL(ctx, n, note, log) & {RnRequest.fresh(log) == True{} : Bool}

def Ok(t: RnRequest.Reqs) -> Type:
  match t:
    case RnRequest.Reqs{ctx, n, note, log}:
      Ok3(ctx, n, note, log)

# The next request was not cut
# ----------------------------
# Each lemma hands its invariant back, as a proof is used once.

def or_ff(a: Bool, -b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case False{}:
      eb
    case True{}:
      LBoolMisc.absurd({Bool.or(True{}, b) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, ea))

# an older context
def not_older(+c: Nat, +ctx: Nat, -m: Nat, -note: Nat, l: {lt(c, ctx) == True{} : Bool}) -> {RnRequest.Req.is(RnRequest.Req{c, m}, RnRequest.Req{ctx, note}) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(c, ctx), False{}, lt_ne(c, ctx, l)) : {Bool.and(_, Nat.is_eq(m, note)) == False{} : Bool}
  {==}

# this context, another note
def not_noted(+c: Nat, +ctx: Nat, +m: Nat, +note: Nat, e: {c == ctx : Nat}, ne: {Nat.is_eq(m, note) == False{} : Bool}) -> {RnRequest.Req.is(RnRequest.Req{c, m}, RnRequest.Req{ctx, note}) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(m, note), False{}, ne) : {Bool.and(Nat.is_eq(c, ctx), _) == False{} : Bool}
  %Equal.sym(Nat, c, ctx, e) : {Bool.and(Nat.is_eq(_, ctx), False{}) == False{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(ctx, ctx), True{}, eq_refl(ctx)) : {Bool.and(_, False{}) == False{} : Bool}
  {==}

def not_noted.back(+c: Nat, +ctx: Nat, +m: Nat, -n: Nat, +note: Nat, +e: {c == ctx : Nat}, l: {lt(m, 1n+n) == True{} : Bool}, +ne: {Nat.is_eq(m, note) == False{} : Bool}) -> {RnRequest.Req.is(RnRequest.Req{c, m}, RnRequest.Req{ctx, note}) == False{} : Bool} & OkQ(ctx, n, note, RnRequest.Req{c, m}):
  (not_noted(c, ctx, m, note, e, ne), Inr{{(e, l, ne) : Here(c, m, ctx, n, note)}})

def not_cutq(+ctx: Nat, +n: Nat, +note: Nat, q: RnRequest.Req, oq: OkQ(ctx, n, note, q)) -> {RnRequest.Req.is(q, RnRequest.Req{ctx, note}) == False{} : Bool} & OkQ(ctx, n, note, q):
  match q:
    case RnRequest.Req{+c, +m}:
      match oq:
        case Inl{+l}:
          (not_older(c, ctx, m, note, l), Inl{l})
        case Inr{y}:
          (e, l, ne) = y
          not_noted.back(c, ctx, m, n, note, e, l, ne)

def not_cut.cons(+ctx: Nat, -n: Nat, +note: Nat, +q: RnRequest.Req, -t: List<&2, RnRequest.Sent>, pq: {RnRequest.Req.is(q, RnRequest.Req{ctx, note}) == False{} : Bool} & OkQ(ctx, n, note, q), pt: {RnRequest.cut_in(RnRequest.Req{ctx, note}, t) == False{} : Bool} & OkL(ctx, n, note, t)) -> {RnRequest.cut_in(RnRequest.Req{ctx, note}, RnRequest.Cut{q} <> t) == False{} : Bool} & OkL(ctx, n, note, RnRequest.Cut{q} <> t):
  (nq, oq) = pq
  (nt, ot) = pt
  (or_ff(RnRequest.Req.is(q, RnRequest.Req{ctx, note}), RnRequest.cut_in(RnRequest.Req{ctx, note}, t), nq, nt), (oq, ot))

def not_cut(+ctx: Nat, +n: Nat, +note: Nat, xs: List<&2, RnRequest.Sent>, ok: OkL(ctx, n, note, xs)) -> {RnRequest.cut_in(RnRequest.Req{ctx, note}, xs) == False{} : Bool} & OkL(ctx, n, note, xs):
  match xs:
    case Nil{}:
      ({==}, ok)
    case RnRequest.Sent{q} <> t:
      not_cut(ctx, n, note, t, ok)
    case RnRequest.Cut{+q} <> t:
      (oq, ot) = ok
      not_cut.cons(ctx, n, note, q, t, not_cutq(ctx, n, note, q, oq), not_cut(ctx, n, note, t, ot))

# sending the next request keeps the log fresh
def fresh_send(+ctx: Nat, +note: Nat, +log: List<&2, RnRequest.Sent>, nc: {RnRequest.cut_in(RnRequest.Req{ctx, note}, log) == False{} : Bool}, fr: {RnRequest.fresh(log) == True{} : Bool}) -> {RnRequest.fresh(RnRequest.Sent{RnRequest.Req{ctx, note}} <> log) == True{} : Bool}:
  %Equal.sym(Bool, RnRequest.cut_in(RnRequest.Req{ctx, note}, log), False{}, nc) : {Bool.and(Bool.not(_), RnRequest.fresh(log)) == True{} : Bool}
  fr

# Each change keeps it
# --------------------

# a grown context leaves every cut request behind, whatever the attempt
# and the note
def okq_ctx(+ctx: Nat, -n: Nat, -note: Nat, -n2: Nat, -note2: Nat, q: RnRequest.Req, oq: OkQ(ctx, n, note, q)) -> OkQ(1n+ctx, n2, note2, q):
  match q:
    case RnRequest.Req{+c, m}:
      match oq:
        case Inl{l}:
          Inl{lt_up(c, ctx, l)}
        case Inr{y}:
          (e, l, ne) = y
          Inl{lt_eq_up(c, ctx, e)}

def ok_ctx(+ctx: Nat, -n: Nat, -note: Nat, -n2: Nat, -note2: Nat, xs: List<&2, RnRequest.Sent>, ok: OkL(ctx, n, note, xs)) -> OkL(1n+ctx, n2, note2, xs):
  match xs:
    case Nil{}:
      Unit{}
    case RnRequest.Sent{q} <> t:
      ok_ctx(ctx, n, note, n2, note2, t, ok)
    case RnRequest.Cut{q} <> t:
      (oq, ot) = ok
      (okq_ctx(ctx, n, note, n2, note2, q, oq), ok_ctx(ctx, n, note, n2, note2, t, ot))

# an attempt more keeps every cut request behind, with the same note
def okq_n(-ctx: Nat, +n: Nat, -note: Nat, q: RnRequest.Req, oq: OkQ(ctx, n, note, q)) -> OkQ(ctx, 1n+n, note, q):
  match q:
    case RnRequest.Req{c, +m}:
      match oq:
        case Inl{l}:
          Inl{l}
        case Inr{y}:
          (e, l, ne) = y
          Inr{{(e, lt_up(m, 1n+n, l), ne) : Here(c, m, ctx, 1n+n, note)}}

def ok_n(-ctx: Nat, +n: Nat, -note: Nat, xs: List<&2, RnRequest.Sent>, ok: OkL(ctx, n, note, xs)) -> OkL(ctx, 1n+n, note, xs):
  match xs:
    case Nil{}:
      Unit{}
    case RnRequest.Sent{q} <> t:
      ok_n(ctx, n, note, t, ok)
    case RnRequest.Cut{q} <> t:
      (oq, ot) = ok
      (okq_n(ctx, n, note, q, oq), ok_n(ctx, n, note, t, ot))

# and with the note of the next attempt, which no cut request of this
# context names
def next_here(-c: Nat, +m: Nat, -ctx: Nat, +n: Nat, -note: Nat, e: {c == ctx : Nat}, +l: {lt(m, 1n+n) == True{} : Bool}) -> Here(c, m, ctx, 1n+n, 1n+n):
  (e, lt_up(m, 1n+n, l), lt_ne(m, 1n+n, l))

def okq_cut(-ctx: Nat, +n: Nat, -note: Nat, q: RnRequest.Req, oq: OkQ(ctx, n, note, q)) -> OkQ(ctx, 1n+n, 1n+n, q):
  match q:
    case RnRequest.Req{c, +m}:
      match oq:
        case Inl{l}:
          Inl{l}
        case Inr{y}:
          (e, l, ne) = y
          Inr{next_here(c, m, ctx, n, note, e, l)}

def ok_cut(-ctx: Nat, +n: Nat, -note: Nat, xs: List<&2, RnRequest.Sent>, ok: OkL(ctx, n, note, xs)) -> OkL(ctx, 1n+n, 1n+n, xs):
  match xs:
    case Nil{}:
      Unit{}
    case RnRequest.Sent{q} <> t:
      ok_cut(ctx, n, note, t, ok)
    case RnRequest.Cut{q} <> t:
      (oq, ot) = ok
      (okq_cut(ctx, n, note, q, oq), ok_cut(ctx, n, note, t, ot))

# Each input
# ----------

def send_ok(+ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, RnRequest.Sent>, le: {lt(note, 1n+n) == True{} : Bool}, fr: {RnRequest.fresh(log) == True{} : Bool}, p: {RnRequest.cut_in(RnRequest.Req{ctx, note}, log) == False{} : Bool} & OkL(ctx, n, note, log)) -> Ok3(ctx, n, note, RnRequest.Sent{RnRequest.Req{ctx, note}} <> log):
  (nc, okl) = p
  (le, okl, fresh_send(ctx, note, log, nc, fr))

def ok_prepared(pa: RnState.Ph, +ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, RnRequest.Sent>, ok: Ok3(ctx, n, note, log)) -> Ok(RnRequest.Reqs.prepared(pa, ctx, n, note, log)):
  match pa:
    case RnState.Call{}:
      (le, okl, fr) = ok
      send_ok(ctx, n, note, log, le, fr, not_cut(ctx, n, note, log, okl))
    case RnState.Prepare{}:
      ok
    case RnState.Compact{over}:
      ok
    case RnState.Tools{}:
      ok
    case RnState.Answered{}:
      ok
    case RnState.Aborted{}:
      ok
    case RnState.Failed{why}:
      ok

def ok_error(noted: Bool, +ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, RnRequest.Sent>, ok: Ok3(ctx, n, note, log)) -> Ok(RnRequest.Reqs.error(noted, ctx, n, note, log)):
  match noted:
    case True{}:
      (le, okl, fr) = ok
      (lt_self(1n+n), (Inr{next_here(ctx, note, ctx, n, note, {==}, le)}, ok_cut(ctx, n, note, log, okl)), fr)
    case False{}:
      (le, okl, fr) = ok
      (lt_up(note, 1n+n, le), ok_n(ctx, n, note, log, okl), fr)

def ok_reply(reply: RnState.Reply, +ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, RnRequest.Sent>, ok: Ok3(ctx, n, note, log)) -> Ok(RnRequest.Reqs.reply(reply, ctx, n, note, log)):
  match reply:
    case RnState.Error{retryable, noted}:
      ok_error(noted, ctx, n, note, log, ok)
    case RnState.Plain{}:
      ok
    case RnState.Calls{}:
      ok
    case RnState.Deferred{}:
      ok
    case RnState.Overflow{cut}:
      ok

def ok_compacted(got: RnState.Got, +ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, RnRequest.Sent>, ok: Ok3(ctx, n, note, log)) -> Ok(RnRequest.Reqs.compacted(got, ctx, n, note, log)):
  match got:
    case RnState.Built{}:
      (le, okl, fr) = ok
      (le, ok_ctx(ctx, n, note, n, note, log, okl), fr)
    case RnState.Kept{}:
      ok
    case RnState.Broke{}:
      ok

def ok_rounded(pa: RnState.Ph, +ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, RnRequest.Sent>, ok: Ok3(ctx, n, note, log)) -> Ok(RnRequest.Reqs.rounded(pa, ctx, n, note, log)):
  match pa:
    case RnState.Prepare{}:
      (le, okl, fr) = ok
      ({==}, ok_ctx(ctx, n, note, 1n, 0n, log, okl), fr)
    case RnState.Call{}:
      ok
    case RnState.Compact{over}:
      ok
    case RnState.Tools{}:
      ok
    case RnState.Answered{}:
      ok
    case RnState.Aborted{}:
      ok
    case RnState.Failed{why}:
      ok

def ok_go(pb: RnState.Ph, e: RnState.Ev, pa: RnState.Ph, +ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, RnRequest.Sent>, ok: Ok3(ctx, n, note, log)) -> Ok(RnRequest.Reqs.go(pb, e, pa, ctx, n, note, log)):
  match pb e:
    case RnState.Prepare{} e:
      ok_prepared(pa, ctx, n, note, log, ok)
    case RnState.Call{} RnState.Go{reply, fin, got}:
      ok_reply(reply, ctx, n, note, log, ok)
    case RnState.Call{} RnState.Abort{}:
      ok
    case RnState.Compact{over} RnState.Go{reply, fin, got}:
      ok_compacted(got, ctx, n, note, log, ok)
    case RnState.Compact{over} RnState.Abort{}:
      ok
    case RnState.Tools{} e:
      ok_rounded(pa, ctx, n, note, log, ok)
    case RnState.Answered{} e:
      ok
    case RnState.Aborted{} e:
      ok
    case RnState.Failed{why} e:
      ok

def ok_step(pb: RnState.Ph, e: RnState.Ev, pa: RnState.Ph, t: RnRequest.Reqs, ok: Ok(t)) -> Ok(RnRequest.Reqs.step(pb, e, pa, t)):
  match t:
    case RnRequest.Reqs{+ctx, +n, +note, +log}:
      ok_go(pb, e, pa, ctx, n, note, log, ok)

def ok_run(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, +t: RnRequest.Reqs, ok: Ok(t)) -> Ok(RnRequest.reqs.go(evs, cfg, s, t)):
  match evs:
    case Nil{}:
      ok
    case +e <> rest:
      +s2 = RnStep.step(cfg, s, e)
      ok_run(rest, cfg, s2, RnRequest.Reqs.step(RnState.St.ph(s), e, RnState.St.ph(s2), t), ok_step(RnState.St.ph(s), e, RnState.St.ph(s2), t, ok))

def fresh_of(t: RnRequest.Reqs, ok: Ok(t)) -> {RnRequest.fresh(RnRequest.Reqs.log(t)) == True{} : Bool}:
  match t:
    case RnRequest.Reqs{ctx, n, note, log}:
      (le, okl, fr) = ok
      fr

# The laws
# --------

# no request the run sends equals one it sent before and had cut
def retry_sends_a_new_request(+cfg: RnState.Cfg, +evs: List<&2, RnState.Ev>) -> {RnRequest.fresh(RnRequest.Reqs.log(RnRequest.reqs(cfg, evs))) == True{} : Bool}:
  +t = RnRequest.reqs.go(evs, cfg, RnState.init(cfg), RnRequest.Reqs.init())
  fresh_of(t, ok_run(evs, cfg, RnState.init(cfg), RnRequest.Reqs.init(), ({==}, Unit{}, {==})))

# (H4.7) A retry never resends a request it cut

def Run.run_retry_sends_a_new_request(cfg, evs):
  retry_sends_a_new_request(cfg, evs)
