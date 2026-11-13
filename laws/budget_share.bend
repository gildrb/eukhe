# eukhe: the laws of area budget_share

import Base
import ../bend/budget.bend as B
import ../bend/budget_share.bend as Bs
import ../bend/ffi_budget_share.bend as FBs
import ../bend/wire.bend as Wr
import ../spec/budget/ledger.bend as S
import ./budget.bend as Budget
import ./base.bend as LawsBase

# (B13) Agents that share an account share what is free
# -----------------------------------------------------
# spec/README.md B13. bend/budget_share.bend: the place among the offers
# (the wanted ask, then smaller ones) a reservation of an agent drawing
# from a shared account starts from; Rust reserves the offers from that
# place on (bend/budget.bend reserve, whose laws are laws/budget.bend). It
# runs as the compiled core by bend/ffi_budget_share.bend (eukhe-bend
# rules/budget.rs share_start). n is the number of the account's Working
# agents that hold nothing, the asker among them. Every input is free:
# every n (0 counts as the asker alone), use, reserve, offer list, free
# amount, time and deadline. An offer fits as spec/budget/ledger.bend
# says (S3: S.fits).
#
# R1: the share of an agent, in money and in tokens, is what is free past
#     the reserves (base, and the agent's own keep), never below zero,
#     divided by n (at least 1); an offer is within it when its amount is
#     at most the share in both. A final answer is not shared: every offer
#     is within.
# R2: the start is the place of the first offer that fits and is within
#     the share; when no offer that fits is within it, the place of the
#     last offer that fits (the smallest); when none fits, 0 (the wanted
#     one).
# R3: a lone agent (n = 1) and a final answer start from the first offer
#     that fits: the share changes nothing for them.
# R4: a start within the share leaves the other n - 1 agents a share as
#     large: n times what is left past it is at least n - 1 times what was
#     free past the reserves.
# R5: reserving from the start's offer on is granted exactly when
#     reserving from the wanted one would be, for every phase, id, step and
#     account, and a grant holds the start's offer; a grant is within what
#     was free with the reserves and ends by the deadline (the tree never
#     passes its budget); for a lone agent and a final answer it answers
#     what reserving all the offers answers.
# R6: the entry answers each request Rust writes with the place of R2,
#     reads exactly the request and nothing after it, and answers any
#     other input with the exact error form
#     `E budget_share: malformed request`.
#
# Not pinned here: that Rust counts n as the account's Working agents that
# hold nothing (eukhe-budget), and that it reserves from the start's place
# (eukhe-budget ledger tests); the settlement of the hold is a settlement
# of laws/budget.bend (budget_settle_charges).

# Spec helpers
# ------------

# R1: what is free past the reserves in spent dimension d: what is free,
# less the reserves above and the agent's own, never below zero
def ss_room(+d: B.Dim, base: B.Ask, keep: B.Ask, free: B.Amt) -> Nat:
  Nat.sub(S.at(d, free), Nat.add(S.at(d, S.amt(base)), S.at(d, S.amt(keep))))

# R1: the ask c is within the share of n agents in spent dimension d: at
# most what is free past the reserves divided by n, at least 1
def ss_share_in(+n: Nat, +d: B.Dim, base: B.Ask, keep: B.Ask, free: B.Amt, c: B.Ask) -> Bool:
  Nat.is_le(S.at(d, S.amt(c)), Nat.div(ss_room(d, base, keep, free), Nat.max(n, 1n)))

# R1: the ask c is within the share: in money and in tokens for work and a
# side request; a final answer is not shared
def ss_within(+n: Nat, u: B.Use, +base: B.Ask, +keep: B.Ask, +free: B.Amt, +c: B.Ask) -> Bool:
  match u:
    case B.Work{}:
      Bool.and(ss_share_in(n, B.Cost{}, base, keep, free, c), ss_share_in(n, B.Tok{}, base, keep, free, c))
    case B.Final{}:
      True{}
    case B.Side{}:
      Bool.and(ss_share_in(n, B.Cost{}, base, keep, free, c), ss_share_in(n, B.Tok{}, base, keep, free, c))

# R2: the ask c fits and is within the share
def ss_ok(+n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +until: Nat) -> Bool:
  Bool.and(S.fits(u, base, keep, c, f, now, until), ss_within(n, u, base, keep, f, c))

# R2: no offer of xs fits and is within the share
def ss_none_ok(+n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, xs: List<&2, B.Ask>, +f: B.Amt, +now: Nat, +until: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(Bool.not(ss_ok(n, u, base, keep, x, f, now, until)), ss_none_ok(n, u, base, keep, t, f, now, until))

# R2: the offer m, if any, fits and is within the share
def ss_mok(+n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, m: Maybe<&2, B.Ask>, +f: B.Amt, +now: Nat, +until: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      ss_ok(n, u, base, keep, x, f, now, until)

# R2: the offer m, if any, fits
def ss_mfits(+u: B.Use, +base: B.Ask, +keep: B.Ask, m: Maybe<&2, B.Ask>, +f: B.Amt, +now: Nat, +until: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      S.fits(u, base, keep, x, f, now, until)

# R2, R5: the offers after place i
def ss_after(i: Nat, xs: List<&2, B.Ask>) -> List<&2, B.Ask>:
  match i:
    case 0n:
      match xs:
        case Nil{}:
          Nil{}
        case Con{x, t}:
          t
    case 1n+j:
      match xs:
        case Nil{}:
          Nil{}
        case Con{x, t}:
          ss_after(j, t)

# R4: the uses that are shared: work and a side request
def ss_shared(u: B.Use) -> Bool:
  match u:
    case B.Work{}:
      True{}
    case B.Final{}:
      False{}
    case B.Side{}:
      True{}

def ss_offer.of(m: Maybe<&2, B.Ask>, want: B.Ask) -> B.Ask:
  match m:
    case None{}:
      want
    case Some{x}:
      x

# R5: the offer at place i of want and then less (want past the end)
def ss_offer(+i: Nat, +want: B.Ask, +less: List<&2, B.Ask>) -> B.Ask:
  ss_offer.of(S.nth(i, want <> less), want)

# R5: a grant holds the offer m; a refusal holds nothing
def ss_holds_offer(g: B.Grant, m: Maybe<&2, B.Ask>) -> Type:
  match g:
    case B.Granted{i, c, a, lo}:
      {m == Some{c} : Maybe<&2, B.Ask>}
    case B.Refused{w, p}:
      Unit

# R3, R5: the share changes nothing: a final answer, or a lone agent
def ss_unshared(n: Nat, u: B.Use) -> Bool:
  match u:
    case B.Work{}:
      Nat.is_eq(n, 1n)
    case B.Final{}:
      True{}
    case B.Side{}:
      Nat.is_eq(n, 1n)

# R5: an answer of a reservation from place k of the offers, read as a
# place among all of them: a grant's place k later, a refusal as it is
def ss_shift(+k: Nat, g: B.Grant) -> B.Grant:
  match g:
    case B.Granted{i, c, a, lo}:
      B.Granted{Nat.add(i, k), c, a, lo}
    case B.Refused{w, p}:
      B.Refused{w, p}

# R6: the spelling of a request: n, the use's tag, base, keep, the wanted
# ask, the smaller offers, what is free, now, the deadline
def sh_w_req(q: FBs.Req, rest: String) -> String:
  match q:
    case FBs.Req{n, u, base, keep, want, less, free, now, until}:
      Wr.put_nat(n, Wr.put_nat(Budget.sp_use_tag(u), Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(want, Wr.put_list(~B.Ask, ~Budget.sp_w_ask, less, Budget.sp_w_amt(free, Wr.put_nat(now, Wr.put_nat(until, rest)))))))))

# R6: every number and count of a request fits the wire
def sh_fit_req(q: FBs.Req) -> Bool:
  match q:
    case FBs.Req{n, u, base, keep, want, +less, free, now, until}:
      Bool.and(LawsBase.wire_fits(n), Bool.and(Budget.sp_fit_ask(base), Bool.and(Budget.sp_fit_ask(keep), Bool.and(Budget.sp_fit_ask(want), Bool.and(LawsBase.wire_fits(List.length(&2, B.Ask, less)), Bool.and(Budget.sp_fit_asks(less), Bool.and(Budget.sp_fit_amt(free), Bool.and(LawsBase.wire_fits(now), LawsBase.wire_fits(until)))))))))

# R6: the spelling of the model's answer to a request
def sh_reply(q: FBs.Req) -> String:
  match q:
    case FBs.Req{n, u, base, keep, want, less, free, now, until}:
      Wr.put_nat(Bs.start(n, u, base, keep, want, less, free, now, until), "")

# Laws: the start (R1-R3)
# -----------------------

# LAW budget_share_first_within (R1, R2): when some offer fits and is
# within the share, the start's offer fits and is within it, and no offer
# before it does
# EXCLUDES: the first offer that fits taken past the share (the first
#   sibling holds what the others need), a later offer within the share
#   taken while an earlier one is, a share divided by another number than
#   n (or n + 1, or n - 1), a share taken from free with no reserve kept
#   out, a share in money only (or tokens only), the smallest offer always
law budget_share_first_within:
  for +n: Nat
  for +use: B.Use
  for +base: B.Ask
  for +keep: B.Ask
  for +want: B.Ask
  for +less: List<&2, B.Ask>
  for +free: B.Amt
  for +now: Nat
  for +until: Nat
  for some: {ss_none_ok(n, use, base, keep, want <> less, free, now, until) == False{} : Bool}
  {ss_mok(n, use, base, keep, S.nth(Bs.start(n, use, base, keep, want, less, free, now, until), want <> less), free, now, until) == True{} : Bool} &
  {ss_none_ok(n, use, base, keep, S.before(Bs.start(n, use, base, keep, want, less, free, now, until), want <> less), free, now, until) == True{} : Bool}

# LAW budget_share_smallest_fit (R2): when no offer that fits is within
# the share but some offer fits, the start's offer fits and no offer
# after it does
# EXCLUDES: the wanted offer (or the first that fits) taken past the
#   share when a smaller one fits, a place past the offers, an offer that
#   does not fit (so the request is refused though one fits)
law budget_share_smallest_fit:
  for +n: Nat
  for +use: B.Use
  for +base: B.Ask
  for +keep: B.Ask
  for +want: B.Ask
  for +less: List<&2, B.Ask>
  for +free: B.Amt
  for +now: Nat
  for +until: Nat
  for none: {ss_none_ok(n, use, base, keep, want <> less, free, now, until) == True{} : Bool}
  for some: {S.none_fit(use, base, keep, want <> less, free, now, until) == False{} : Bool}
  {ss_mfits(use, base, keep, S.nth(Bs.start(n, use, base, keep, want, less, free, now, until), want <> less), free, now, until) == True{} : Bool} &
  {S.none_fit(use, base, keep, ss_after(Bs.start(n, use, base, keep, want, less, free, now, until), want <> less), free, now, until) == True{} : Bool}

# LAW budget_share_none_fits_first (R2): when no offer fits, the start is
# the wanted offer (place 0)
# EXCLUDES: a refused request started from a smaller offer (so its
#   refusal names another dimension than reserve's), a place past the
#   offers
law budget_share_none_fits_first:
  for +n: Nat
  for +use: B.Use
  for +base: B.Ask
  for +keep: B.Ask
  for +want: B.Ask
  for +less: List<&2, B.Ask>
  for +free: B.Amt
  for +now: Nat
  for +until: Nat
  for none: {S.none_fit(use, base, keep, want <> less, free, now, until) == True{} : Bool}
  {Bs.start(n, use, base, keep, want, less, free, now, until) == 0n : Nat}

# LAW budget_share_lone_is_first_fit (R3): a lone agent (n = 1), for every
# use, starts from the first offer that fits, when one fits
# EXCLUDES: a share that cuts a lone agent's request (divided by n + 1, a
#   reserve counted twice, the whole free amount kept out), a lone agent
#   started from the smallest offer
law budget_share_lone_is_first_fit:
  for +use: B.Use
  for +base: B.Ask
  for +keep: B.Ask
  for +want: B.Ask
  for +less: List<&2, B.Ask>
  for +free: B.Amt
  for +now: Nat
  for +until: Nat
  for some: {S.none_fit(use, base, keep, want <> less, free, now, until) == False{} : Bool}
  {ss_mfits(use, base, keep, S.nth(Bs.start(1n, use, base, keep, want, less, free, now, until), want <> less), free, now, until) == True{} : Bool} &
  {S.none_fit(use, base, keep, S.before(Bs.start(1n, use, base, keep, want, less, free, now, until), want <> less), free, now, until) == True{} : Bool}

# LAW budget_share_final_unshared (R3): a final answer, for every n,
# starts from the first offer that fits, when one fits
# EXCLUDES: a final answer cut to a share (an agent's last answer starved
#   by its siblings' count), a final answer started from the smallest
#   offer
law budget_share_final_unshared:
  for +n: Nat
  for +base: B.Ask
  for +keep: B.Ask
  for +want: B.Ask
  for +less: List<&2, B.Ask>
  for +free: B.Amt
  for +now: Nat
  for +until: Nat
  for some: {S.none_fit(B.Final{}, base, keep, want <> less, free, now, until) == False{} : Bool}
  {ss_mfits(B.Final{}, base, keep, S.nth(Bs.start(n, B.Final{}, base, keep, want, less, free, now, until), want <> less), free, now, until) == True{} : Bool} &
  {S.none_fit(B.Final{}, base, keep, S.before(Bs.start(n, B.Final{}, base, keep, want, less, free, now, until), want <> less), free, now, until) == True{} : Bool}

# Laws: the others (R4)
# ---------------------

# LAW budget_share_leaves_others (R4): for work and a side request among n
# = m + 1 agents, when some offer fits and is within the share, what the
# start's offer leaves past the reserves, n times, is at least m times
# what was free past them, in money and in tokens: the other m agents can
# each still have a share as large
# EXCLUDES: a share of what is free with the reserves counted in (the
#   siblings' share eaten by a reserve), a share rounded up, a share of
#   another divisor than n, a share in one dimension only
law budget_share_leaves_others:
  for +m: Nat
  for +use: B.Use
  for +base: B.Ask
  for +keep: B.Ask
  for +want: B.Ask
  for +less: List<&2, B.Ask>
  for +free: B.Amt
  for +now: Nat
  for +until: Nat
  for +c: B.Ask
  for shared: {ss_shared(use) == True{} : Bool}
  for some: {ss_none_ok(1n+m, use, base, keep, want <> less, free, now, until) == False{} : Bool}
  for at: {S.nth(Bs.start(1n+m, use, base, keep, want, less, free, now, until), want <> less) == Some{c} : Maybe<&2, B.Ask>}
  {Nat.is_le(Nat.mul(m, ss_room(B.Cost{}, base, keep, free)), Nat.mul(1n+m, Nat.sub(ss_room(B.Cost{}, base, keep, free), S.at(B.Cost{}, S.amt(c))))) == True{} : Bool} &
  {Nat.is_le(Nat.mul(m, ss_room(B.Tok{}, base, keep, free)), Nat.mul(1n+m, Nat.sub(ss_room(B.Tok{}, base, keep, free), S.at(B.Tok{}, S.amt(c))))) == True{} : Bool}

# Laws: the reservation (R5)
# --------------------------

# LAW budget_share_refuses_alike (R5): for every phase, id, step and
# account, reserving the start's offer and the offers after it (start
# taken on the account's free amount and deadline) is granted exactly when
# reserving the wanted offer and the smaller ones is, and a grant holds
# the start's offer
# EXCLUDES: a start past every offer that fits (a request refused that
#   reserve would grant), a start whose offer does not fit (a smaller
#   offer granted than the start), a start read on another free amount or
#   deadline than the account's
law budget_share_refuses_alike:
  for +n: Nat
  for +use: B.Use
  for +p: B.Phase
  for +id: Nat
  for +now: Nat
  for +base: B.Ask
  for +keep: B.Ask
  for +step: B.Ask
  for +want: B.Ask
  for +less: List<&2, B.Ask>
  for +a: B.Acct
  {S.granted(B.reserve(use, p, id, now, base, keep, step, ss_offer(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), want, less), ss_after(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), want <> less), a)) == S.granted(B.reserve(use, p, id, now, base, keep, step, want, less, a)) : Bool} &
  ss_holds_offer(B.reserve(use, p, id, now, base, keep, step, ss_offer(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), want, less), ss_after(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), want <> less), a), S.nth(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), want <> less))

# LAW budget_share_never_exceeds (R5): a grant of the reservation from the
# start's offer on takes exactly the granted amount out of what was free,
# in every spent dimension, and that amount, with the reserves above and,
# for work and a side request, the agent's own, was within what was free;
# started now, it ends by the deadline with their durations: sharing never
# lets the tree pass its budget
# EXCLUDES: a start that hands reserve an ask no offer was (a hold past
#   what is free), a start read on another free amount or deadline than
#   the account's
law budget_share_never_exceeds:
  for +n: Nat
  for +use: B.Use
  for +p: B.Phase
  for +id: Nat
  for +now: Nat
  for +base: B.Ask
  for +keep: B.Ask
  for +step: B.Ask
  for +want: B.Ask
  for +less: List<&2, B.Ask>
  for +a: B.Acct
  for +i: Nat
  for +c: B.Ask
  for +a2: B.Acct
  for +lo: Bool
  for +d: B.Dim
  for g: {B.reserve(use, p, id, now, base, keep, step, ss_offer(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), want, less), ss_after(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), want <> less), a) == B.Granted{i, c, a2, lo} : B.Grant}
  {Nat.add(S.at(d, S.free(a2)), S.at(d, S.amt(c))) == S.at(d, S.free(a)) : Nat} &
  {S.fits_in(use, base, keep, c, S.free(a), d) == True{} : Bool} &
  {S.on_time(use, base, keep, c, now, S.until(a)) == True{} : Bool}

# LAW budget_share_lone_identical (R3, R5): for a lone agent (n = 1) and
# for a final answer (any n), the reservation from the start's offer on
# answers what the reservation of all the offers answers: the same grant
# (offer, account, low), its place counted among all the offers, or the
# same refusal (reason, phase)
# EXCLUDES: a lone agent or a final answer granted a smaller offer than
#   without the share, a grant whose place is counted from the start (Rust
#   would read another offer), a refusal with another reason or phase
law budget_share_lone_identical:
  for +n: Nat
  for +use: B.Use
  for +p: B.Phase
  for +id: Nat
  for +now: Nat
  for +base: B.Ask
  for +keep: B.Ask
  for +step: B.Ask
  for +want: B.Ask
  for +less: List<&2, B.Ask>
  for +a: B.Acct
  for plain: {ss_unshared(n, use) == True{} : Bool}
  {ss_shift(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), B.reserve(use, p, id, now, base, keep, step, ss_offer(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), want, less), ss_after(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), want <> less), a)) == B.reserve(use, p, id, now, base, keep, step, want, less, a) : B.Grant}

# LAW budget_share_example (R1-R3): anchor: four agents working at once on
# 12 free in money and 120 in tokens (10 and 120 in tool calls and model
# requests), each keeping (2, 20) for its own answer, offering (8, 80),
# (4, 40), (2, 20), (1, 10), one call and one request each, 10 ms, until
# 1000: each starts from (2, 20), a share of (2, 25); alone it starts from
# (8, 80), with one sibling from (4, 40), among twenty from (1, 10) (the
# smallest that fits: no share); a final answer starts from (8, 80); on 1
# free nothing fits: 0; n = 0 counts the asker: 0
# EXCLUDES: a start that drifts from the bench it fixes (2 of 4 siblings
#   refused)
law budget_share_example:
  {[Bs.start(4n, B.Work{}, S.nothing(), B.Ask{B.Amt{2n, 20n, 0n, 0n}, 0n}, B.Ask{B.Amt{8n, 80n, 1n, 1n}, 10n}, [B.Ask{B.Amt{4n, 40n, 1n, 1n}, 10n}, B.Ask{B.Amt{2n, 20n, 1n, 1n}, 10n}, B.Ask{B.Amt{1n, 10n, 1n, 1n}, 10n}], B.Amt{12n, 120n, 10n, 10n}, 0n, 1000n), Bs.start(1n, B.Work{}, S.nothing(), B.Ask{B.Amt{2n, 20n, 0n, 0n}, 0n}, B.Ask{B.Amt{8n, 80n, 1n, 1n}, 10n}, [B.Ask{B.Amt{4n, 40n, 1n, 1n}, 10n}, B.Ask{B.Amt{2n, 20n, 1n, 1n}, 10n}, B.Ask{B.Amt{1n, 10n, 1n, 1n}, 10n}], B.Amt{12n, 120n, 10n, 10n}, 0n, 1000n), Bs.start(2n, B.Side{}, S.nothing(), B.Ask{B.Amt{2n, 20n, 0n, 0n}, 0n}, B.Ask{B.Amt{8n, 80n, 1n, 1n}, 10n}, [B.Ask{B.Amt{4n, 40n, 1n, 1n}, 10n}, B.Ask{B.Amt{2n, 20n, 1n, 1n}, 10n}, B.Ask{B.Amt{1n, 10n, 1n, 1n}, 10n}], B.Amt{12n, 120n, 10n, 10n}, 0n, 1000n), Bs.start(20n, B.Work{}, S.nothing(), B.Ask{B.Amt{2n, 20n, 0n, 0n}, 0n}, B.Ask{B.Amt{8n, 80n, 1n, 1n}, 10n}, [B.Ask{B.Amt{4n, 40n, 1n, 1n}, 10n}, B.Ask{B.Amt{2n, 20n, 1n, 1n}, 10n}, B.Ask{B.Amt{1n, 10n, 1n, 1n}, 10n}], B.Amt{12n, 120n, 10n, 10n}, 0n, 1000n), Bs.start(4n, B.Final{}, S.nothing(), B.Ask{B.Amt{2n, 20n, 0n, 0n}, 0n}, B.Ask{B.Amt{8n, 80n, 1n, 1n}, 10n}, [B.Ask{B.Amt{4n, 40n, 1n, 1n}, 10n}, B.Ask{B.Amt{2n, 20n, 1n, 1n}, 10n}, B.Ask{B.Amt{1n, 10n, 1n, 1n}, 10n}], B.Amt{12n, 120n, 10n, 10n}, 0n, 1000n), Bs.start(4n, B.Work{}, S.nothing(), B.Ask{B.Amt{2n, 20n, 0n, 0n}, 0n}, B.Ask{B.Amt{8n, 80n, 1n, 1n}, 10n}, [B.Ask{B.Amt{4n, 40n, 1n, 1n}, 10n}, B.Ask{B.Amt{2n, 20n, 1n, 1n}, 10n}, B.Ask{B.Amt{1n, 10n, 1n, 1n}, 10n}], B.Amt{1n, 120n, 10n, 10n}, 0n, 1000n), Bs.start(0n, B.Work{}, S.nothing(), B.Ask{B.Amt{2n, 20n, 0n, 0n}, 0n}, B.Ask{B.Amt{8n, 80n, 1n, 1n}, 10n}, [B.Ask{B.Amt{4n, 40n, 1n, 1n}, 10n}, B.Ask{B.Amt{2n, 20n, 1n, 1n}, 10n}, B.Ask{B.Amt{1n, 10n, 1n, 1n}, 10n}], B.Amt{12n, 120n, 10n, 10n}, 0n, 1000n)] == [2n, 0n, 1n, 3n, 0n, 0n, 0n] : List<&2, Nat>}

# Laws: the entry (R6)
# --------------------

# LAW budget_share_entry_answers (R6): the entry answers every request
# Rust spells, every number and count within the wire, with the model's
# start spelled
# EXCLUDES: fields read in another order (keep and base swapped, now read
#   as the deadline), a dimension swapped, an offer lost, the use tags
#   swapped, a default
law budget_share_entry_answers:
  for +q: FBs.Req
  for fit: {sh_fit_req(q) == True{} : Bool}
  {FBs.ffi(sh_w_req(q, "")) == sh_reply(q) : String}

# LAW budget_share_entry_reads (R6): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law budget_share_entry_reads:
  for +q: FBs.Req
  for +rest: String
  for fit: {sh_fit_req(q) == True{} : Bool}
  {FBs.get_req(sh_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FBs.Req>}

# LAW budget_share_entry_exact (R6): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: a start answered on input that is no request (an unknown use
#   tag read as a known one, a short offer list, input left over)
law budget_share_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FBs.ffi(s)) == False{} : Bool}
  exs q: FBs.Req
  {s == sh_w_req(q, "") : String} & {sh_fit_req(q) == True{} : Bool}

# LAW budget_share_entry_refuses (R6): every error the entry answers is
# exactly `E budget_share: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law budget_share_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FBs.ffi(s)) == True{} : Bool}
  {FBs.ffi(s) == Wr.err("budget_share: malformed request") : String}

# LAW budget_share_entry_example (R6): anchor: the wire strings Rust sends
# and the replies it reads: the four agents of budget_share_example (place
# 2), the lone agent (place 0), a final answer (place 0); an unknown use
# tag, a short offer list and input left over are refused
# EXCLUDES: a field order other than Rust's, another reply spelling
law budget_share_entry_example:
  {[FBs.ffi("4,0,0,0,0,0,0,2,20,0,0,0,8,80,1,1,10,3,4,40,1,1,10,2,20,1,1,10,1,10,1,1,10,12,120,10,10,0,1000,"), FBs.ffi("1,0,0,0,0,0,0,2,20,0,0,0,8,80,1,1,10,3,4,40,1,1,10,2,20,1,1,10,1,10,1,1,10,12,120,10,10,0,1000,"), FBs.ffi("4,1,0,0,0,0,0,2,20,0,0,0,8,80,1,1,10,3,4,40,1,1,10,2,20,1,1,10,1,10,1,1,10,12,120,10,10,0,1000,"), FBs.ffi("4,3,0,0,0,0,0,2,20,0,0,0,8,80,1,1,10,0,12,120,10,10,0,1000,"), FBs.ffi("4,0,0,0,0,0,0,2,20,0,0,0,8,80,1,1,10,2,4,40,1,1,10,12,120,10,10,0,1000,"), FBs.ffi("4,0,0,0,0,0,0,2,20,0,0,0,8,80,1,1,10,0,12,120,10,10,0,1000,0,")] == ["2,", "0,", "0,", Wr.err("budget_share: malformed request"), Wr.err("budget_share: malformed request"), Wr.err("budget_share: malformed request")] : List<&2, String>}
