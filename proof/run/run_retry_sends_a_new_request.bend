# eukhe: the proof of LAW run_retry_sends_a_new_request

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run
import ../base.bend as L

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
      L.absurd({lt(1n+p, 1n) == True{} : Bool}, h)
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
      L.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
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
def OkQ(+ctx: Nat, +n: Nat, +note: Nat, q: Rn.Req) -> Type:
  match q:
    case Rn.Req{c, m}:
      Or({lt(c, ctx) == True{} : Bool}, Here(c, m, ctx, n, note))

# the request (c, m) is from context ctx, with an attempt up to n and
# another note
def Here(-c: Nat, -m: Nat, -ctx: Nat, -n: Nat, -note: Nat) -> Type:
  {c == ctx : Nat} & {lt(m, 1n+n) == True{} : Bool} & {Nat.is_eq(m, note) == False{} : Bool}

# every cut request of xs is
def OkL(+ctx: Nat, +n: Nat, +note: Nat, xs: List<&2, Rn.Sent>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Rn.Sent{q} <> t:
      OkL(ctx, n, note, t)
    case Rn.Cut{q} <> t:
      OkQ(ctx, n, note, q) & OkL(ctx, n, note, t)

# the note names an attempt up to the current one, every cut request is
# behind the next request, and no sent request was cut before
def Ok3(+ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, Rn.Sent>) -> Type:
  {lt(note, 1n+n) == True{} : Bool} & OkL(ctx, n, note, log) & {Rn.fresh(log) == True{} : Bool}

def Ok(t: Rn.Reqs) -> Type:
  match t:
    case Rn.Reqs{ctx, n, note, log}:
      Ok3(ctx, n, note, log)

# The next request was not cut
# ----------------------------
# Each lemma hands its invariant back, as a proof is used once.

def or_ff(a: Bool, -b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case False{}:
      eb
    case True{}:
      L.absurd({Bool.or(True{}, b) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, ea))

# an older context
def not_older(+c: Nat, +ctx: Nat, -m: Nat, -note: Nat, l: {lt(c, ctx) == True{} : Bool}) -> {Rn.Req.is(Rn.Req{c, m}, Rn.Req{ctx, note}) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(c, ctx), False{}, lt_ne(c, ctx, l)) : {Bool.and(_, Nat.is_eq(m, note)) == False{} : Bool}
  {==}

# this context, another note
def not_noted(+c: Nat, +ctx: Nat, +m: Nat, +note: Nat, e: {c == ctx : Nat}, ne: {Nat.is_eq(m, note) == False{} : Bool}) -> {Rn.Req.is(Rn.Req{c, m}, Rn.Req{ctx, note}) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(m, note), False{}, ne) : {Bool.and(Nat.is_eq(c, ctx), _) == False{} : Bool}
  %Equal.sym(Nat, c, ctx, e) : {Bool.and(Nat.is_eq(_, ctx), False{}) == False{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(ctx, ctx), True{}, eq_refl(ctx)) : {Bool.and(_, False{}) == False{} : Bool}
  {==}

def not_noted.back(+c: Nat, +ctx: Nat, +m: Nat, -n: Nat, +note: Nat, +e: {c == ctx : Nat}, l: {lt(m, 1n+n) == True{} : Bool}, +ne: {Nat.is_eq(m, note) == False{} : Bool}) -> {Rn.Req.is(Rn.Req{c, m}, Rn.Req{ctx, note}) == False{} : Bool} & OkQ(ctx, n, note, Rn.Req{c, m}):
  (not_noted(c, ctx, m, note, e, ne), Inr{{(e, l, ne) : Here(c, m, ctx, n, note)}})

def not_cutq(+ctx: Nat, +n: Nat, +note: Nat, q: Rn.Req, oq: OkQ(ctx, n, note, q)) -> {Rn.Req.is(q, Rn.Req{ctx, note}) == False{} : Bool} & OkQ(ctx, n, note, q):
  match q:
    case Rn.Req{+c, +m}:
      match oq:
        case Inl{+l}:
          (not_older(c, ctx, m, note, l), Inl{l})
        case Inr{y}:
          (e, l, ne) = y
          not_noted.back(c, ctx, m, n, note, e, l, ne)

def not_cut.cons(+ctx: Nat, -n: Nat, +note: Nat, +q: Rn.Req, -t: List<&2, Rn.Sent>, pq: {Rn.Req.is(q, Rn.Req{ctx, note}) == False{} : Bool} & OkQ(ctx, n, note, q), pt: {Rn.cut_in(Rn.Req{ctx, note}, t) == False{} : Bool} & OkL(ctx, n, note, t)) -> {Rn.cut_in(Rn.Req{ctx, note}, Rn.Cut{q} <> t) == False{} : Bool} & OkL(ctx, n, note, Rn.Cut{q} <> t):
  (nq, oq) = pq
  (nt, ot) = pt
  (or_ff(Rn.Req.is(q, Rn.Req{ctx, note}), Rn.cut_in(Rn.Req{ctx, note}, t), nq, nt), (oq, ot))

def not_cut(+ctx: Nat, +n: Nat, +note: Nat, xs: List<&2, Rn.Sent>, ok: OkL(ctx, n, note, xs)) -> {Rn.cut_in(Rn.Req{ctx, note}, xs) == False{} : Bool} & OkL(ctx, n, note, xs):
  match xs:
    case Nil{}:
      ({==}, ok)
    case Rn.Sent{q} <> t:
      not_cut(ctx, n, note, t, ok)
    case Rn.Cut{+q} <> t:
      (oq, ot) = ok
      not_cut.cons(ctx, n, note, q, t, not_cutq(ctx, n, note, q, oq), not_cut(ctx, n, note, t, ot))

# sending the next request keeps the log fresh
def fresh_send(+ctx: Nat, +note: Nat, +log: List<&2, Rn.Sent>, nc: {Rn.cut_in(Rn.Req{ctx, note}, log) == False{} : Bool}, fr: {Rn.fresh(log) == True{} : Bool}) -> {Rn.fresh(Rn.Sent{Rn.Req{ctx, note}} <> log) == True{} : Bool}:
  %Equal.sym(Bool, Rn.cut_in(Rn.Req{ctx, note}, log), False{}, nc) : {Bool.and(Bool.not(_), Rn.fresh(log)) == True{} : Bool}
  fr

# Each change keeps it
# --------------------

# a grown context leaves every cut request behind, whatever the attempt
# and the note
def okq_ctx(+ctx: Nat, -n: Nat, -note: Nat, -n2: Nat, -note2: Nat, q: Rn.Req, oq: OkQ(ctx, n, note, q)) -> OkQ(1n+ctx, n2, note2, q):
  match q:
    case Rn.Req{+c, m}:
      match oq:
        case Inl{l}:
          Inl{lt_up(c, ctx, l)}
        case Inr{y}:
          (e, l, ne) = y
          Inl{lt_eq_up(c, ctx, e)}

def ok_ctx(+ctx: Nat, -n: Nat, -note: Nat, -n2: Nat, -note2: Nat, xs: List<&2, Rn.Sent>, ok: OkL(ctx, n, note, xs)) -> OkL(1n+ctx, n2, note2, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Rn.Sent{q} <> t:
      ok_ctx(ctx, n, note, n2, note2, t, ok)
    case Rn.Cut{q} <> t:
      (oq, ot) = ok
      (okq_ctx(ctx, n, note, n2, note2, q, oq), ok_ctx(ctx, n, note, n2, note2, t, ot))

# an attempt more keeps every cut request behind, with the same note
def okq_n(-ctx: Nat, +n: Nat, -note: Nat, q: Rn.Req, oq: OkQ(ctx, n, note, q)) -> OkQ(ctx, 1n+n, note, q):
  match q:
    case Rn.Req{c, +m}:
      match oq:
        case Inl{l}:
          Inl{l}
        case Inr{y}:
          (e, l, ne) = y
          Inr{{(e, lt_up(m, 1n+n, l), ne) : Here(c, m, ctx, 1n+n, note)}}

def ok_n(-ctx: Nat, +n: Nat, -note: Nat, xs: List<&2, Rn.Sent>, ok: OkL(ctx, n, note, xs)) -> OkL(ctx, 1n+n, note, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Rn.Sent{q} <> t:
      ok_n(ctx, n, note, t, ok)
    case Rn.Cut{q} <> t:
      (oq, ot) = ok
      (okq_n(ctx, n, note, q, oq), ok_n(ctx, n, note, t, ot))

# and with the note of the next attempt, which no cut request of this
# context names
def next_here(-c: Nat, +m: Nat, -ctx: Nat, +n: Nat, -note: Nat, e: {c == ctx : Nat}, +l: {lt(m, 1n+n) == True{} : Bool}) -> Here(c, m, ctx, 1n+n, 1n+n):
  (e, lt_up(m, 1n+n, l), lt_ne(m, 1n+n, l))

def okq_cut(-ctx: Nat, +n: Nat, -note: Nat, q: Rn.Req, oq: OkQ(ctx, n, note, q)) -> OkQ(ctx, 1n+n, 1n+n, q):
  match q:
    case Rn.Req{c, +m}:
      match oq:
        case Inl{l}:
          Inl{l}
        case Inr{y}:
          (e, l, ne) = y
          Inr{next_here(c, m, ctx, n, note, e, l)}

def ok_cut(-ctx: Nat, +n: Nat, -note: Nat, xs: List<&2, Rn.Sent>, ok: OkL(ctx, n, note, xs)) -> OkL(ctx, 1n+n, 1n+n, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Rn.Sent{q} <> t:
      ok_cut(ctx, n, note, t, ok)
    case Rn.Cut{q} <> t:
      (oq, ot) = ok
      (okq_cut(ctx, n, note, q, oq), ok_cut(ctx, n, note, t, ot))

# Each input
# ----------

def send_ok(+ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, Rn.Sent>, le: {lt(note, 1n+n) == True{} : Bool}, fr: {Rn.fresh(log) == True{} : Bool}, p: {Rn.cut_in(Rn.Req{ctx, note}, log) == False{} : Bool} & OkL(ctx, n, note, log)) -> Ok3(ctx, n, note, Rn.Sent{Rn.Req{ctx, note}} <> log):
  (nc, okl) = p
  (le, okl, fresh_send(ctx, note, log, nc, fr))

def ok_prepared(pa: Rn.Ph, +ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, Rn.Sent>, ok: Ok3(ctx, n, note, log)) -> Ok(Rn.Reqs.prepared(pa, ctx, n, note, log)):
  match pa:
    case Rn.Call{}:
      (le, okl, fr) = ok
      send_ok(ctx, n, note, log, le, fr, not_cut(ctx, n, note, log, okl))
    case Rn.Prepare{}:
      ok
    case Rn.Compact{over}:
      ok
    case Rn.Tools{}:
      ok
    case Rn.Answered{}:
      ok
    case Rn.Aborted{}:
      ok
    case Rn.Failed{why}:
      ok

def ok_error(noted: Bool, +ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, Rn.Sent>, ok: Ok3(ctx, n, note, log)) -> Ok(Rn.Reqs.error(noted, ctx, n, note, log)):
  match noted:
    case True{}:
      (le, okl, fr) = ok
      (lt_self(1n+n), (Inr{next_here(ctx, note, ctx, n, note, {==}, le)}, ok_cut(ctx, n, note, log, okl)), fr)
    case False{}:
      (le, okl, fr) = ok
      (lt_up(note, 1n+n, le), ok_n(ctx, n, note, log, okl), fr)

def ok_reply(reply: Rn.Reply, +ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, Rn.Sent>, ok: Ok3(ctx, n, note, log)) -> Ok(Rn.Reqs.reply(reply, ctx, n, note, log)):
  match reply:
    case Rn.Error{retryable, noted}:
      ok_error(noted, ctx, n, note, log, ok)
    case Rn.Plain{}:
      ok
    case Rn.Calls{}:
      ok
    case Rn.Deferred{}:
      ok
    case Rn.Overflow{cut}:
      ok

def ok_compacted(got: Rn.Got, +ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, Rn.Sent>, ok: Ok3(ctx, n, note, log)) -> Ok(Rn.Reqs.compacted(got, ctx, n, note, log)):
  match got:
    case Rn.Built{}:
      (le, okl, fr) = ok
      (le, ok_ctx(ctx, n, note, n, note, log, okl), fr)
    case Rn.Kept{}:
      ok
    case Rn.Broke{}:
      ok

def ok_rounded(pa: Rn.Ph, +ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, Rn.Sent>, ok: Ok3(ctx, n, note, log)) -> Ok(Rn.Reqs.rounded(pa, ctx, n, note, log)):
  match pa:
    case Rn.Prepare{}:
      (le, okl, fr) = ok
      ({==}, ok_ctx(ctx, n, note, 1n, 0n, log, okl), fr)
    case Rn.Call{}:
      ok
    case Rn.Compact{over}:
      ok
    case Rn.Tools{}:
      ok
    case Rn.Answered{}:
      ok
    case Rn.Aborted{}:
      ok
    case Rn.Failed{why}:
      ok

def ok_go(pb: Rn.Ph, e: Rn.Ev, pa: Rn.Ph, +ctx: Nat, +n: Nat, +note: Nat, +log: List<&2, Rn.Sent>, ok: Ok3(ctx, n, note, log)) -> Ok(Rn.Reqs.go(pb, e, pa, ctx, n, note, log)):
  match pb e:
    case Rn.Prepare{} e:
      ok_prepared(pa, ctx, n, note, log, ok)
    case Rn.Call{} Rn.Go{reply, fin, got}:
      ok_reply(reply, ctx, n, note, log, ok)
    case Rn.Call{} Rn.Abort{}:
      ok
    case Rn.Compact{over} Rn.Go{reply, fin, got}:
      ok_compacted(got, ctx, n, note, log, ok)
    case Rn.Compact{over} Rn.Abort{}:
      ok
    case Rn.Tools{} e:
      ok_rounded(pa, ctx, n, note, log, ok)
    case Rn.Answered{} e:
      ok
    case Rn.Aborted{} e:
      ok
    case Rn.Failed{why} e:
      ok

def ok_step(pb: Rn.Ph, e: Rn.Ev, pa: Rn.Ph, t: Rn.Reqs, ok: Ok(t)) -> Ok(Rn.Reqs.step(pb, e, pa, t)):
  match t:
    case Rn.Reqs{+ctx, +n, +note, +log}:
      ok_go(pb, e, pa, ctx, n, note, log, ok)

def ok_run(evs: List<&2, Rn.Ev>, +cfg: Rn.Cfg, +s: Rn.St, +t: Rn.Reqs, ok: Ok(t)) -> Ok(Rn.reqs.go(evs, cfg, s, t)):
  match evs:
    case Nil{}:
      ok
    case +e <> rest:
      +s2 = Rn.step(cfg, s, e)
      ok_run(rest, cfg, s2, Rn.Reqs.step(Rn.St.ph(s), e, Rn.St.ph(s2), t), ok_step(Rn.St.ph(s), e, Rn.St.ph(s2), t, ok))

def fresh_of(t: Rn.Reqs, ok: Ok(t)) -> {Rn.fresh(Rn.Reqs.log(t)) == True{} : Bool}:
  match t:
    case Rn.Reqs{ctx, n, note, log}:
      (le, okl, fr) = ok
      fr

# The laws
# --------

# no request the run sends equals one it sent before and had cut
def retry_sends_a_new_request(+cfg: Rn.Cfg, +evs: List<&2, Rn.Ev>) -> {Rn.fresh(Rn.Reqs.log(Rn.reqs(cfg, evs))) == True{} : Bool}:
  +t = Rn.reqs.go(evs, cfg, Rn.init(cfg), Rn.Reqs.init())
  fresh_of(t, ok_run(evs, cfg, Rn.init(cfg), Rn.Reqs.init(), ({==}, Unit{}, {==})))

# (H4.7) A retry never resends a request it cut

def Run.run_retry_sends_a_new_request(cfg, evs):
  retry_sends_a_new_request(cfg, evs)
