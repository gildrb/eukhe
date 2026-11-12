# eukhe: the laws of area budget

import Base
import ../bend/budget.bend as B
import ../bend/ffi_budget.bend as FBg
import ../bend/wire.bend as Wr
import ../spec/budget/ledger.bend as S
import ./base.bend as LawsBase

# (B1-B11) A budget is never exceeded
# -----------------------------------
# spec/README.md B1-B11. bend/budget.bend: the ledger of a task tree's
# budget: money, tokens, tool calls and model requests are spent from an
# account, time is
# the account's deadline. It runs as the compiled core by
# bend/ffi_budget.bend (eukhe-bend rules/budget.rs), asked by eukhe-budget
# ledger.rs before every provider request, tool call and child spawn
# (reserve, carve) and after each (settle, close), and when budget is
# added (fund). Every agent of the tree without a budget of its own asks
# the same account; its phase is its own. spec/budget/ledger.bend
# restates what the laws measure (S1-S6). Every input is free: every
# account (also one no run of the ledger reaches), phase, time, ask, id
# and offer list.
#
# R1: nothing is spent that was not reserved first: a grant moves exactly
#     the granted amount from free into a hold, the amount is within what
#     was free with the reserves (B1, B6).
# R2: of the offers the first that fits is granted, and a request that
#     has an offer that fits is granted: a reduced cap before a refusal
#     (B2).
# R3: a refusal holds nothing and leaves the account as it was. A phase
#     that does not admit the request refuses it in that phase; an id
#     already held is refused; when no offer fits, work moves the agent
#     to WrapUp, a final answer to Exhausted, and a side request (a
#     request of the agent that is not its own turn: a title, a
#     classifier, a compaction, a memory or side question) leaves the
#     phase as it was; a refused side request never changes the phase
#     (B6).
# R4: after granted work or a granted side request, its agent's final
#     answer within its reserve is granted (B6); the grant says the
#     budget runs low exactly when two steps of the size of the agent's
#     largest recent step as spent (`step`: this one and one more),
#     started now, with the reserves, would not fit what was free before
#     the grant by the deadline, whichever offer was granted (B7).
# R5: a settlement charges exactly the actual spend, once: the hold is
#     gone, the other holds stay, what was not spent is free again, the
#     budget of the account is conserved, and a spend within the hold
#     makes no overrun (B3, B9). An id that is not held changes nothing,
#     so a second settlement of an id changes nothing (B5).
# R6: a hold left open by a crash, settled at what it holds, is charged
#     in full: nothing is lost, nothing returns (B5).
# R7: a carve moves the child's own budget from the parent's free to
#     lent and leaves the reserves above; the child's deadline is its
#     duration from now and ends before the reserves above; a close of an
#     idle child returns what it has free, adds its spend to the parent's
#     and conserves the parent's budget, an overrun included; a busy
#     child is not closed; a child closed at once returns everything (B4).
# R8: funding adds exactly the amount to the budget and the duration to
#     the deadline, repays an overrun first; funding a request's need and
#     the overrun gets that request granted (B6, B8).
# R9: the entry answers each request Rust writes with the model's
#     decision, reads nothing after the request, and answers any other
#     input with the exact error form `E budget: malformed request`.
# R10: every grant ends by the deadline, the durations of the reserves
#     included; time is wall-clock time from the request's start (B10).
# R11: the reserves of the agents above the asking one (base) are never
#     taken: after any grant, a final answer within base still fits (B11).
#
# Not pinned here: that Rust asks the entry before every spend and
# persists each answer before acting on it (eukhe-budget ledger tests,
# the crash e2e), that it stops a request at its granted duration, that
# the worst case Rust offers bounds the provider's charge (eukhe-budget
# worst_case tests), that base is the sum of the reserves of the agents
# above (eukhe-budget ledger tests), and that funding makes every agent
# Working again (eukhe-budget ledger tests).

# Spec helpers
# ------------

# R9: the spelling of an amount: money, tokens, tool calls, model
# requests
def sp_w_amt(x: B.Amt, rest: String) -> String:
  match x:
    case B.Amt{c, k, n, r}:
      Wr.put_nat(c, Wr.put_nat(k, Wr.put_nat(n, Wr.put_nat(r, rest))))

# R9: the spelling of an ask: its amount, then its duration
def sp_w_ask(x: B.Ask, rest: String) -> String:
  match x:
    case B.Ask{a, m}:
      sp_w_amt(a, Wr.put_nat(m, rest))

# R9: the spelling of a hold: its id, then its amount
def sp_w_hold(h: B.Hold, rest: String) -> String:
  match h:
    case B.Hold{i, x}:
      Wr.put_nat(i, sp_w_amt(x, rest))

# R9: the tag of a phase: 0 Working, 1 WrapUp, 2 Exhausted
def sp_phase_tag(p: B.Phase) -> Nat:
  match p:
    case B.Working{}:
      0n
    case B.WrapUp{}:
      1n
    case B.Exhausted{}:
      2n

# R9: the spelling of an account: free, spent, lent, over, the holds,
# the deadline
def sp_w_acct(a: B.Acct, rest: String) -> String:
  match a:
    case B.Acct{f, s, l, o, h, u}:
      sp_w_amt(f, sp_w_amt(s, sp_w_amt(l, sp_w_amt(o, Wr.put_list(~B.Hold, ~sp_w_hold, h, Wr.put_nat(u, rest))))))

# R9: the tag of a use: 0 work, 1 a final answer, 2 a side request
def sp_use_tag(u: B.Use) -> Nat:
  match u:
    case B.Work{}:
      0n
    case B.Final{}:
      1n
    case B.Side{}:
      2n

# R9: the tag of a dimension: 0 money, 1 tokens, 2 time, 3 tool calls,
# 4 model requests
def sp_dim_tag(d: B.Dim) -> Nat:
  match d:
    case B.Cost{}:
      0n
    case B.Tok{}:
      1n
    case B.Time{}:
      2n
    case B.Calls{}:
      3n
    case B.Reqs{}:
      4n

# R9: the spelling of a request: its tag, then its fields
def sp_w_req(q: FBg.Req, rest: String) -> String:
  match q:
    case FBg.QReserve{u, p, id, now, base, keep, step, want, less, a}:
      Wr.put_nat(0n, Wr.put_nat(sp_use_tag(u), Wr.put_nat(sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, sp_w_ask(base, sp_w_ask(keep, sp_w_ask(step, sp_w_ask(want, Wr.put_list(~B.Ask, ~sp_w_ask, less, sp_w_acct(a, rest)))))))))))
    case FBg.QSettle{id, act, a}:
      Wr.put_nat(1n, Wr.put_nat(id, sp_w_amt(act, sp_w_acct(a, rest))))
    case FBg.QCarve{p, now, want, base, a}:
      Wr.put_nat(2n, Wr.put_nat(sp_phase_tag(p), Wr.put_nat(now, sp_w_ask(want, sp_w_ask(base, sp_w_acct(a, rest))))))
    case FBg.QClose{c, p}:
      Wr.put_nat(3n, sp_w_acct(c, sp_w_acct(p, rest)))
    case FBg.QFund{n, a}:
      Wr.put_nat(4n, sp_w_ask(n, sp_w_acct(a, rest)))

# R9: the spelling of a reason: 0 short and the dimension, 1 held,
# 2 stopped
def sp_w_why(w: B.Why, rest: String) -> String:
  match w:
    case B.Short{d}:
      Wr.put_nat(0n, Wr.put_nat(sp_dim_tag(d), rest))
    case B.Held{}:
      Wr.put_nat(1n, rest)
    case B.Stopped{}:
      Wr.put_nat(2n, rest)

# R9: the spelling of the answer to a reservation
def sp_w_grant(g: B.Grant) -> String:
  match g:
    case B.Granted{i, c, a, lo}:
      Wr.put_nat(0n, Wr.put_nat(i, sp_w_ask(c, sp_w_acct(a, Wr.put_bool(lo, "")))))
    case B.Refused{w, p}:
      Wr.put_nat(1n, sp_w_why(w, Wr.put_nat(sp_phase_tag(p), "")))

# R9: the spelling of the answer to a carve
def sp_w_carve(c: B.Carve) -> String:
  match c:
    case B.Carved{p, k}:
      Wr.put_nat(0n, sp_w_acct(p, sp_w_acct(k, "")))
    case B.Kept{w}:
      Wr.put_nat(1n, sp_w_why(w, ""))

# R9: the spelling of the answer to a close
def sp_w_close(c: B.Close) -> String:
  match c:
    case B.Closed{p, k}:
      Wr.put_nat(0n, sp_w_acct(p, sp_w_acct(k, "")))
    case B.Busy{}:
      Wr.put_nat(1n, "")

# R9: the spelling of the model's answer to a request
def sp_w_reply(q: FBg.Req) -> String:
  match q:
    case FBg.QReserve{+u, +p, +id, +now, +base, +keep, +step, +want, less, a}:
      sp_w_grant(B.reserve(u, p, id, now, base, keep, step, want, less, a))
    case FBg.QSettle{+id, +act, a}:
      sp_w_acct(B.settle(id, act, a), "")
    case FBg.QCarve{p, +now, +want, base, a}:
      sp_w_carve(B.carve(p, now, want, base, a))
    case FBg.QClose{c, p}:
      sp_w_close(B.close(c, p))
    case FBg.QFund{+n, a}:
      sp_w_acct(B.fund(n, a), "")

# R9: every number of an amount fits the wire
def sp_fit_amt(x: B.Amt) -> Bool:
  match x:
    case B.Amt{c, k, n, r}:
      Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(r))))

# R9: every number of an ask fits the wire
def sp_fit_ask(x: B.Ask) -> Bool:
  match x:
    case B.Ask{a, m}:
      Bool.and(sp_fit_amt(a), LawsBase.wire_fits(m))

def sp_fit_asks(xs: List<&2, B.Ask>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(sp_fit_ask(x), sp_fit_asks(t))

def sp_fit_holds(hs: List<&2, B.Hold>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, t}:
      match h:
        case B.Hold{i, x}:
          Bool.and(LawsBase.wire_fits(i), Bool.and(sp_fit_amt(x), sp_fit_holds(t)))

# R9: every number and count of an account fits the wire
def sp_fit_acct(a: B.Acct) -> Bool:
  match a:
    case B.Acct{f, s, l, o, +h, u}:
      Bool.and(sp_fit_amt(f), Bool.and(sp_fit_amt(s), Bool.and(sp_fit_amt(l), Bool.and(sp_fit_amt(o), Bool.and(LawsBase.wire_fits(List.length(&2, B.Hold, h)), Bool.and(sp_fit_holds(h), LawsBase.wire_fits(u)))))))

# R9: every number and count of a request fits the wire
def sp_fit_req(q: FBg.Req) -> Bool:
  match q:
    case FBg.QReserve{u, p, id, now, base, keep, step, want, +less, a}:
      Bool.and(LawsBase.wire_fits(id), Bool.and(LawsBase.wire_fits(now), Bool.and(sp_fit_ask(base), Bool.and(sp_fit_ask(keep), Bool.and(sp_fit_ask(step), Bool.and(sp_fit_ask(want), Bool.and(LawsBase.wire_fits(List.length(&2, B.Ask, less)), Bool.and(sp_fit_asks(less), sp_fit_acct(a)))))))))
    case FBg.QSettle{id, act, a}:
      Bool.and(LawsBase.wire_fits(id), Bool.and(sp_fit_amt(act), sp_fit_acct(a)))
    case FBg.QCarve{p, now, want, base, a}:
      Bool.and(LawsBase.wire_fits(now), Bool.and(sp_fit_ask(want), Bool.and(sp_fit_ask(base), sp_fit_acct(a))))
    case FBg.QClose{c, p}:
      Bool.and(sp_fit_acct(c), sp_fit_acct(p))
    case FBg.QFund{n, a}:
      Bool.and(sp_fit_ask(n), sp_fit_acct(a))

# Laws: reserve (R1-R4, R10, R11)
# -------------------------------

# LAW budget_grant_within (R1): a grant takes exactly the granted amount
# out of what was free, in every spent dimension, and that amount, with
# the reserves above and, for work and a side request, the agent's own
# reserve, was within what was free
# EXCLUDES: a request sent that the remainder cannot pay, free not
#   reduced or reduced by the wanted amount instead of the granted one,
#   work or a side request that eats its agent's final-answer reserve, a
#   request that eats the reserve of an agent above, a check in one
#   dimension only
law budget_grant_within:
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
  for +t: Bool
  for +d: B.Dim
  for g: {B.reserve(use, p, id, now, base, keep, step, want, less, a) == B.Granted{i, c, a2, t} : B.Grant}
  {Nat.add(S.at(d, S.free(a2)), S.at(d, S.amt(c))) == S.at(d, S.free(a)) : Nat} &
  {S.fits_in(use, base, keep, c, S.free(a), d) == True{} : Bool}

# LAW budget_grant_on_time (R10): a grant, started now, ends by the
# deadline with the durations of the reserves above and, for work and a
# side request, of the agent's own reserve; the deadline stays
# EXCLUDES: a request let run past the deadline, work or a side request
#   that leaves no time for its agent's final answer or for the final
#   answer of an agent above, a deadline moved by a reservation
law budget_grant_on_time:
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
  for +t: Bool
  for g: {B.reserve(use, p, id, now, base, keep, step, want, less, a) == B.Granted{i, c, a2, t} : B.Grant}
  {S.on_time(use, base, keep, c, now, S.until(a)) == True{} : Bool} &
  {S.until(a2) == S.until(a) : Nat}

# LAW budget_grant_holds (R1): a grant opens one hold of the granted
# amount under the id, before the other holds, and changes nothing else
# of the account
# EXCLUDES: a grant with no hold (a spend that no settlement finds), a
#   hold of another amount or id, a lost hold, spent, lent or overrun
#   touched by a reservation
law budget_grant_holds:
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
  for +t: Bool
  for g: {B.reserve(use, p, id, now, base, keep, step, want, less, a) == B.Granted{i, c, a2, t} : B.Grant}
  {S.holds(a2) == B.Hold{id, S.amt(c)} <> S.holds(a) : List<&2, B.Hold>} &
  {S.spent(a2) == S.spent(a) : B.Amt} &
  {S.lent(a2) == S.lent(a) : B.Amt} &
  {S.over(a2) == S.over(a) : B.Amt}

# LAW budget_grant_first (R2): the granted ask is the offer at the
# granted place, and no offer before it fits
# EXCLUDES: a smaller offer granted while a larger one fits, the last
#   offer always, an ask that is no offer, a wrong place
law budget_grant_first:
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
  for +t: Bool
  for g: {B.reserve(use, p, id, now, base, keep, step, want, less, a) == B.Granted{i, c, a2, t} : B.Grant}
  {S.nth(i, want <> less) == Some{c} : Maybe<&2, B.Ask>} &
  {S.none_fit(use, base, keep, S.before(i, want <> less), S.free(a), now, S.until(a)) == True{} : Bool}

# LAW budget_grant_when_fits (R2): a request the phase admits, under an
# id that is not held, with an offer that fits, is granted
# EXCLUDES: a refusal while a reduced offer fits, only the wanted ask
#   tried, a budget or a deadline exactly met refused
law budget_grant_when_fits:
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
  for ok: {S.allows(p, use) == True{} : Bool}
  for fresh: {S.has(id, S.holds(a)) == False{} : Bool}
  for some: {S.none_fit(use, base, keep, want <> less, S.free(a), now, S.until(a)) == False{} : Bool}
  {S.granted(B.reserve(use, p, id, now, base, keep, step, want, less, a)) == True{} : Bool}

# LAW budget_refuse_short (R3): a refusal for a short dimension means no
# offer fits and the last offer fails in that dimension; nothing is held,
# and the agent moves to WrapUp (work) or Exhausted (a final answer) or
# stays in its phase (a side request)
# EXCLUDES: a refusal while an offer fits, a dimension named that has
#   room, work refused without the wrap-up, an agent still Working after
#   its work was refused, a refused side request that wraps the agent up
law budget_refuse_short:
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
  for +d: B.Dim
  for +p2: B.Phase
  for g: {B.reserve(use, p, id, now, base, keep, step, want, less, a) == B.Refused{B.Short{d}, p2} : B.Grant}
  {S.none_fit(use, base, keep, want <> less, S.free(a), now, S.until(a)) == True{} : Bool} &
  {S.short_in(use, base, keep, S.last(less, want), S.free(a), now, S.until(a), d) == True{} : Bool} &
  {p2 == S.after(use, p) : B.Phase}

# LAW budget_refuse_stopped (R3): a request the phase does not admit is
# refused as stopped, the phase unchanged: work after the wrap-up,
# anything once exhausted
# EXCLUDES: work admitted after the agent was told to wrap up, a request
#   admitted to an exhausted agent, an exhausted agent that a refused
#   request moves back
law budget_refuse_stopped:
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
  for no: {S.allows(p, use) == False{} : Bool}
  {B.reserve(use, p, id, now, base, keep, step, want, less, a) == B.Refused{B.Stopped{}, p} : B.Grant}

# LAW budget_refuse_held (R3): a request the phase admits under an id
# that is already held is refused as held, the phase unchanged
# EXCLUDES: one id holding twice (a replayed reservation that doubles the
#   hold), a held id overwritten
law budget_refuse_held:
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
  for ok: {S.allows(p, use) == True{} : Bool}
  for dup: {S.has(id, S.holds(a)) == True{} : Bool}
  {B.reserve(use, p, id, now, base, keep, step, want, less, a) == B.Refused{B.Held{}, p} : B.Grant}

# LAW budget_refuse_when_none_fits (R3): a request the phase admits,
# under an id that is not held, with no offer that fits, is refused as
# short and moves the agent to WrapUp (work) or Exhausted (a final
# answer) or leaves it in its phase (a side request)
# EXCLUDES: a request no offer fits answered as held or stopped (so the
#   same request sent again is granted past the budget), an agent left
#   Working after its work found no room, an agent wrapped up by a side
#   request that found no room
law budget_refuse_when_none_fits:
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
  for ok: {S.allows(p, use) == True{} : Bool}
  for fresh: {S.has(id, S.holds(a)) == False{} : Bool}
  for none: {S.none_fit(use, base, keep, want <> less, S.free(a), now, S.until(a)) == True{} : Bool}
  {S.short_to(B.reserve(use, p, id, now, base, keep, step, want, less, a)) == Some{S.after(use, p)} : Maybe<&2, B.Phase>}

# LAW budget_side_refused_keeps_phase (R3): a side request that is
# refused, for whatever reason (no offer fits, its id is held, its phase
# does not admit it), leaves its agent in the phase it was in
# EXCLUDES: a refused title, classifier, compaction or memory request that
#   wraps the agent up (taking its work away) or exhausts it (taking its
#   final answer away), a refused side request that moves an exhausted
#   or wrapping-up agent back to Working
law budget_side_refused_keeps_phase:
  for +p: B.Phase
  for +id: Nat
  for +now: Nat
  for +base: B.Ask
  for +keep: B.Ask
  for +step: B.Ask
  for +want: B.Ask
  for +less: List<&2, B.Ask>
  for +a: B.Acct
  for +w: B.Why
  for +p2: B.Phase
  for g: {B.reserve(B.Side{}, p, id, now, base, keep, step, want, less, a) == B.Refused{w, p2} : B.Grant}
  {p2 == p : B.Phase}

# LAW budget_low_by_steps (R4): a grant is low exactly when two steps of
# the agent's largest recent step as spent (this one and one more),
# started now, with the reserves above and, for work and a side request,
# the agent's own reserve, would not fit what was free before the grant
# by the deadline
# EXCLUDES: a low budget judged against the hold, which fills what is
#   free, so every grant is low; a first step (no step spent yet) told
#   its budget runs low; low never told; told only once nothing fits
law budget_low_by_steps:
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
  for g: {B.reserve(use, p, id, now, base, keep, step, want, less, a) == B.Granted{i, c, a2, lo} : B.Grant}
  {lo == Bool.not(S.fits(use, base, keep, S.plus(step, step), S.free(a), now, S.until(a))) : Bool}

# LAW budget_low_by_spend (R4): whether a grant is low does not depend on
# the offers: two reservations alike but for the wanted ask and the
# smaller offers, both granted, are both low or both not
# EXCLUDES: a low budget judged against the offer granted (a large hold
#   told low, the same request with a smaller cap not), every grant of a
#   full-size offer low
law budget_low_by_spend:
  for +use: B.Use
  for +p: B.Phase
  for +id: Nat
  for +now: Nat
  for +base: B.Ask
  for +keep: B.Ask
  for +step: B.Ask
  for +want: B.Ask
  for +less: List<&2, B.Ask>
  for +want2: B.Ask
  for +less2: List<&2, B.Ask>
  for +a: B.Acct
  for +i: Nat
  for +c: B.Ask
  for +a2: B.Acct
  for +lo: Bool
  for +i2: Nat
  for +c2: B.Ask
  for +a3: B.Acct
  for +lo2: Bool
  for g: {B.reserve(use, p, id, now, base, keep, step, want, less, a) == B.Granted{i, c, a2, lo} : B.Grant}
  for g2: {B.reserve(use, p, id, now, base, keep, step, want2, less2, a) == B.Granted{i2, c2, a3, lo2} : B.Grant}
  {lo == lo2 : Bool}

# LAW budget_low_steps_example (R4): anchor: at 100 ms, work of
# (16,16,1,1) for 50 ms with reserves above and its own of (2,2,0,0) and
# (2,2,0,1) for 10 ms each, on 20 free in every dimension until 1000: its
# hold fills what is free, yet with a largest step of (1,1,0,0)
# for 10 ms it is not low, nor with no step spent yet; with a largest
# step of (9,1,1,1) for 10 ms (two of them and the reserves past 20) it
# is low
# EXCLUDES: a low budget judged against the hold, a first step told low
law budget_low_steps_example:
  {[FBg.ffi("0,0,0,7,100,2,2,0,0,10,2,2,0,1,10,1,1,0,0,10,16,16,1,1,50,0,20,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,1000,"), FBg.ffi("0,0,0,7,100,2,2,0,0,10,2,2,0,1,10,0,0,0,0,0,16,16,1,1,50,0,20,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,1000,"), FBg.ffi("0,0,0,7,100,2,2,0,0,10,2,2,0,1,10,9,1,1,1,10,16,16,1,1,50,0,20,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,1000,")] == ["0,0,16,16,1,1,50,4,4,19,19,0,0,0,0,0,0,0,0,0,0,0,0,1,7,16,16,1,1,1000,F", "0,0,16,16,1,1,50,4,4,19,19,0,0,0,0,0,0,0,0,0,0,0,0,1,7,16,16,1,1,1000,F", "0,0,16,16,1,1,50,4,4,19,19,0,0,0,0,0,0,0,0,0,0,0,0,1,7,16,16,1,1,1000,T"] : List<&2, String>}

# LAW budget_final_reserve_kept (R4): after granted work, a final answer
# of the same agent within that work's reserve, under an id not held,
# asked before the work's time is up, is granted
# EXCLUDES: work that leaves less than the reserve, work that runs into
#   the final answer's time, a final answer held to the reserve of work,
#   a final answer refused in WrapUp
law budget_final_reserve_kept:
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
  for +t: Bool
  for +f: B.Ask
  for +p2: B.Phase
  for +id2: Nat
  for +now2: Nat
  for +k2: B.Ask
  for +s2: B.Ask
  for g: {B.reserve(B.Work{}, p, id, now, base, keep, step, want, less, a) == B.Granted{i, c, a2, t} : B.Grant}
  for within: {S.le(f, keep) == True{} : Bool}
  for ok: {S.allows(p2, B.Final{}) == True{} : Bool}
  for fresh: {S.has(id2, S.holds(a2)) == False{} : Bool}
  for soon: {Nat.is_le(now2, Nat.add(now, S.ms(c))) == True{} : Bool}
  {S.granted(B.reserve(B.Final{}, p2, id2, now2, base, k2, s2, f, Nil{}, a2)) == True{} : Bool}

# LAW budget_side_final_reserve_kept (R4): after a granted side request
# (a title, a classifier, a compaction, a memory or side question), a
# final answer of the same agent within its reserve, under an id not
# held, asked before the side request's time is up, is granted
# EXCLUDES: a side request that leaves less than the reserve (fitted as a
#   final answer, with base only), a side request that runs into the
#   final answer's time, a final answer held to the reserve of a side
#   request
law budget_side_final_reserve_kept:
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
  for +t: Bool
  for +f: B.Ask
  for +p2: B.Phase
  for +id2: Nat
  for +now2: Nat
  for +k2: B.Ask
  for +s2: B.Ask
  for g: {B.reserve(B.Side{}, p, id, now, base, keep, step, want, less, a) == B.Granted{i, c, a2, t} : B.Grant}
  for within: {S.le(f, keep) == True{} : Bool}
  for ok: {S.allows(p2, B.Final{}) == True{} : Bool}
  for fresh: {S.has(id2, S.holds(a2)) == False{} : Bool}
  for soon: {Nat.is_le(now2, Nat.add(now, S.ms(c))) == True{} : Bool}
  {S.granted(B.reserve(B.Final{}, p2, id2, now2, base, k2, s2, f, Nil{}, a2)) == True{} : Bool}

# LAW budget_base_kept (R11): after any grant, the final answer of an
# agent above, within the reserves above and on time, is granted: no
# request of an agent below (work, a side request or a final answer)
# takes the reserve of an agent above
# EXCLUDES: a child drawing from the shared account into its parent's
#   final-answer reserve, a child's final answer or side request that
#   eats it, a check of the asking agent's own reserve only
law budget_base_kept:
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
  for +t: Bool
  for +f: B.Ask
  for +p2: B.Phase
  for +id2: Nat
  for +now2: Nat
  for +k2: B.Ask
  for +s2: B.Ask
  for g: {B.reserve(use, p, id, now, base, keep, step, want, less, a) == B.Granted{i, c, a2, t} : B.Grant}
  for within: {S.le(f, base) == True{} : Bool}
  for ok: {S.allows(p2, B.Final{}) == True{} : Bool}
  for fresh: {S.has(id2, S.holds(a2)) == False{} : Bool}
  for ontime: {Nat.is_le(Nat.add(now2, S.ms(f)), S.until(a)) == True{} : Bool}
  {S.granted(B.reserve(B.Final{}, p2, id2, now2, S.nothing(), k2, s2, f, Nil{}, a2)) == True{} : Bool}

# Laws: settle (R5, R6)
# ---------------------

# LAW budget_settle_unknown_inert (R5): settling an id that is not held
# changes nothing
# EXCLUDES: a spend charged with no reservation, a settlement replayed
#   after a crash charged again
law budget_settle_unknown_inert:
  for +id: Nat
  for +act: B.Amt
  for +a: B.Acct
  for miss: {S.has(id, S.holds(a)) == False{} : Bool}
  {B.settle(id, act, a) == a : B.Acct}

# LAW budget_settle_once (R5): a second settlement of an id changes
# nothing, whatever amount it names
# EXCLUDES: double spending: a retried or replayed settlement charged
#   twice, a hold that survives its settlement
law budget_settle_once:
  for +id: Nat
  for +act: B.Amt
  for +again: B.Amt
  for +a: B.Acct
  {B.settle(id, again, B.settle(id, act, a)) == B.settle(id, act, a) : B.Acct}

# LAW budget_settle_conserves (R5): a settlement keeps the budget of the
# account in every dimension: free, held, spent and lent add up to what
# they did, plus what the overrun grew by
# EXCLUDES: budget created or lost by a settlement (the unspent part of
#   a hold not returned, returned twice, a spend not charged), an overrun
#   hidden
law budget_settle_conserves:
  for +id: Nat
  for +act: B.Amt
  for +a: B.Acct
  for +d: B.Dim
  {Nat.add(S.net(d, B.settle(id, act, a)), S.at(d, S.over(a))) == Nat.add(S.net(d, a), S.at(d, S.over(B.settle(id, act, a)))) : Nat}

# LAW budget_settle_charges (R5): settling a held id adds exactly the
# actual spend to spent, in every dimension, leaves no hold under the id
# and keeps lent and the deadline
# EXCLUDES: the reservation charged instead of the actual spend, a spend
#   lost or rounded, a settled id still held
law budget_settle_charges:
  for +id: Nat
  for +act: B.Amt
  for +a: B.Acct
  for +d: B.Dim
  for open: {S.has(id, S.holds(a)) == True{} : Bool}
  {S.at(d, S.spent(B.settle(id, act, a))) == Nat.add(S.at(d, S.spent(a)), S.at(d, act)) : Nat} &
  {S.has(id, S.holds(B.settle(id, act, a))) == False{} : Bool} &
  {S.lent(B.settle(id, act, a)) == S.lent(a) : B.Amt} &
  {S.until(B.settle(id, act, a)) == S.until(a) : Nat}

# LAW budget_settle_keeps_others (R5): a settlement leaves what every
# other id holds as it was
# EXCLUDES: a settlement that drops or shrinks another request's hold
#   (that request's spend would then be charged to nobody)
law budget_settle_keeps_others:
  for +id: Nat
  for +act: B.Amt
  for +a: B.Acct
  for +j: Nat
  for +d: B.Dim
  for other: {Nat.is_eq(j, id) == False{} : Bool}
  {S.held_of(j, d, S.holds(B.settle(id, act, a))) == S.held_of(j, d, S.holds(a)) : Nat}

# LAW budget_settle_within (R5): a spend within its hold makes no
# overrun, and the rest of the hold is free again: free and the spend
# add up to what was free and held under the id
# EXCLUDES: an overrun booked for a request that kept its cap, the
#   unspent part of a reservation kept from the task
law budget_settle_within:
  for +id: Nat
  for +act: B.Amt
  for +a: B.Acct
  for +d: B.Dim
  for open: {S.has(id, S.holds(a)) == True{} : Bool}
  for within: {Nat.is_le(S.at(d, act), S.held_of(id, d, S.holds(a))) == True{} : Bool}
  {S.at(d, S.over(B.settle(id, act, a))) == S.at(d, S.over(a)) : Nat} &
  {Nat.add(S.at(d, S.free(B.settle(id, act, a))), S.at(d, act)) == Nat.add(S.at(d, S.free(a)), S.held_of(id, d, S.holds(a))) : Nat}

# LAW budget_settle_overrun_from_free (R5): a spend past its hold is
# taken from what is free, and only past that is it an overrun: after a
# settlement of a held id, free is what was free and held under the id
# less the spend (never below zero), and the overrun grew by what the spend
# passed that
# EXCLUDES: an overrun booked while free could pay the spend, free left
#   untouched or grown by a spend past its hold
law budget_settle_overrun_from_free:
  for +id: Nat
  for +act: B.Amt
  for +a: B.Acct
  for +d: B.Dim
  for open: {S.has(id, S.holds(a)) == True{} : Bool}
  {S.at(d, S.free(B.settle(id, act, a))) == Nat.sub(Nat.add(S.at(d, S.free(a)), S.held_of(id, d, S.holds(a))), S.at(d, act)) : Nat} &
  {S.at(d, S.over(B.settle(id, act, a))) == Nat.add(S.at(d, S.over(a)), Nat.sub(S.at(d, act), Nat.add(S.at(d, S.free(a)), S.held_of(id, d, S.holds(a))))) : Nat}

# LAW budget_settle_keeps_other_ids (R5): a settlement neither opens nor
# closes a reservation under any other id
# EXCLUDES: a settlement that adds a hold (even of nothing) under another
#   id, which then refuses that id as held and keeps a child from closing,
#   or drops another id's hold
law budget_settle_keeps_other_ids:
  for +id: Nat
  for +act: B.Amt
  for +a: B.Acct
  for +j: Nat
  for other: {Nat.is_eq(j, id) == False{} : Bool}
  {S.has(j, S.holds(B.settle(id, act, a))) == S.has(j, S.holds(a)) : Bool}

# LAW budget_recover_charges_in_full (R6): a hold left open by a crash,
# settled at what it holds, adds that to spent and nothing to free or to
# the overrun
# EXCLUDES: lost spend: a request in flight at a crash refunded, or
#   charged less than its reservation, or charged twice
law budget_recover_charges_in_full:
  for +id: Nat
  for +act: B.Amt
  for +a: B.Acct
  for +d: B.Dim
  for open: {S.has(id, S.holds(a)) == True{} : Bool}
  for full: {S.at(d, act) == S.held_of(id, d, S.holds(a)) : Nat}
  {S.at(d, S.spent(B.settle(id, act, a))) == Nat.add(S.at(d, S.spent(a)), S.held_of(id, d, S.holds(a))) : Nat} &
  {S.at(d, S.free(B.settle(id, act, a))) == S.at(d, S.free(a)) : Nat} &
  {S.at(d, S.over(B.settle(id, act, a))) == S.at(d, S.over(a)) : Nat}

# Laws: children (R7)
# -------------------

# LAW budget_carve_moves (R7): a carve takes exactly the child's amount
# out of the parent's free into lent, leaves the reserves above free,
# changes nothing else of the parent, and the child starts with the
# amount free, nothing spent, lent, overrun or held, its deadline its
# duration from now, which ends the reserves' durations before the
# parent's
# EXCLUDES: a child funded from nothing (the parent's free not reduced),
#   a child given more than was taken, an allotment that eats the
#   parent's final-answer reserve, a child that may run past its parent's
#   deadline or into its parent's final-answer time
law budget_carve_moves:
  for +ph: B.Phase
  for +now: Nat
  for +want: B.Ask
  for +base: B.Ask
  for +a: B.Acct
  for +p: B.Acct
  for +c: B.Acct
  for +d: B.Dim
  for g: {B.carve(ph, now, want, base, a) == B.Carved{p, c} : B.Carve}
  {Nat.add(S.at(d, S.free(p)), S.at(d, S.amt(want))) == S.at(d, S.free(a)) : Nat} &
  {S.at(d, S.lent(p)) == Nat.add(S.at(d, S.lent(a)), S.at(d, S.amt(want))) : Nat} &
  {Nat.is_le(S.at(d, S.amt(base)), S.at(d, S.free(p))) == True{} : Bool} &
  {S.spent(p) == S.spent(a) : B.Amt} &
  {S.over(p) == S.over(a) : B.Amt} &
  {S.holds(p) == S.holds(a) : List<&2, B.Hold>} &
  {S.until(p) == S.until(a) : Nat} &
  {c == B.Acct{S.amt(want), B.Amt{0n, 0n, 0n, 0n}, B.Amt{0n, 0n, 0n, 0n}, B.Amt{0n, 0n, 0n, 0n}, Nil{}, Nat.add(now, S.ms(want))} : B.Acct} &
  {Nat.is_le(Nat.add(Nat.add(now, S.ms(want)), S.ms(base)), S.until(a)) == True{} : Bool}

# LAW budget_carve_iff (R7): a carve happens exactly when the parent
# agent is Working and the child's ask with the reserves above fits what
# is free by the deadline
# EXCLUDES: a child spawned on a budget that cannot pay it, a child
#   spawned while wrapping up, a carve refused though it fits
law budget_carve_iff:
  for +ph: B.Phase
  for +now: Nat
  for +want: B.Ask
  for +base: B.Ask
  for +a: B.Acct
  {S.carved(B.carve(ph, now, want, base, a)) == Bool.and(S.working(ph), S.fits(B.Final{}, base, S.nothing(), want, S.free(a), now, S.until(a))) : Bool}

# LAW budget_carve_kept_why (R7): a carve asked by an agent that is not
# Working is kept as stopped; one asked by a Working agent whose ask does
# not fit is kept as short
# EXCLUDES: a refused spawn that names the wrong reason (held, stopped
#   while Working, short while wrapping up)
law budget_carve_kept_why:
  for +now: Nat
  for +want: B.Ask
  for +base: B.Ask
  for +a: B.Acct
  {B.carve(B.WrapUp{}, now, want, base, a) == B.Kept{B.Stopped{}} : B.Carve} &
  {B.carve(B.Exhausted{}, now, want, base, a) == B.Kept{B.Stopped{}} : B.Carve} &
  {Bool.or(S.fits(B.Final{}, base, S.nothing(), want, S.free(a), now, S.until(a)), S.kept_short(B.carve(B.Working{}, now, want, base, a))) == True{} : Bool}

# LAW budget_carve_kept_short (R7): a carve a Working agent cannot fit is
# kept short only for a dimension the ask with the reserves above really
# lacks: an amount past what is free, or (time) past the deadline
# EXCLUDES: a refused spawn that names a dimension with room (time short
#   when money is), so the agent plans with a wrong remainder
law budget_carve_kept_short:
  for +now: Nat
  for +want: B.Ask
  for +base: B.Ask
  for +a: B.Acct
  for +d: B.Dim
  for g: {B.carve(B.Working{}, now, want, base, a) == B.Kept{B.Short{d}} : B.Carve}
  {S.short_in(B.Final{}, base, S.nothing(), want, S.free(a), now, S.until(a), d) == True{} : Bool}

# LAW budget_close_returns (R7): closing a child with no overrun returns
# exactly what it has free to the parent's free, adds exactly its spend
# to the parent's spent, takes both out of lent, and leaves the child
# empty; the parent's overrun, holds and deadline stay
# EXCLUDES: unspent allotment not returned or returned twice, a child's
#   spend lost from the parent's total, a closed child that can still
#   spend
law budget_close_returns:
  for +c: B.Acct
  for +p: B.Acct
  for +p2: B.Acct
  for +c2: B.Acct
  for +d: B.Dim
  for g: {B.close(c, p) == B.Closed{p2, c2} : B.Close}
  for clean: {S.at(d, S.over(c)) == 0n : Nat}
  {S.at(d, S.free(p2)) == Nat.add(S.at(d, S.free(p)), S.at(d, S.free(c))) : Nat} &
  {S.at(d, S.spent(p2)) == Nat.add(S.at(d, S.spent(p)), S.at(d, S.spent(c))) : Nat} &
  {S.at(d, S.lent(p2)) == Nat.sub(S.at(d, S.lent(p)), Nat.add(S.at(d, S.free(c)), S.at(d, S.spent(c)))) : Nat} &
  {S.at(d, S.over(p2)) == S.at(d, S.over(p)) : Nat} &
  {S.holds(p2) == S.holds(p) : List<&2, B.Hold>} &
  {S.until(p2) == S.until(p) : Nat} &
  {c2 == S.empty() : B.Acct}

# LAW budget_close_iff (R7): a child is closed exactly when it is idle:
# no open reservation, nothing lent
# EXCLUDES: a child closed while a request of it is in flight or while it
#   has live children (their spend would escape the parent), an idle
#   child never closed
law budget_close_iff:
  for +c: B.Acct
  for +p: B.Acct
  {S.closed(B.close(c, p)) == S.idle(c) : Bool}

# LAW budget_close_conserves (R7): closing a child that was funded from
# this parent keeps the parent's budget in every dimension: its free,
# held, spent and lent add up to what they did, plus what its overrun
# grew by (a child's overrun is the parent's spend too)
# EXCLUDES: budget created or lost at a close, a child's overrun dropped
#   instead of taken from the parent
law budget_close_conserves:
  for +c: B.Acct
  for +p: B.Acct
  for +p2: B.Acct
  for +c2: B.Acct
  for +d: B.Dim
  for g: {B.close(c, p) == B.Closed{p2, c2} : B.Close}
  for funded: {Nat.is_le(S.at(d, S.over(c)), Nat.add(S.at(d, S.free(c)), S.at(d, S.spent(c)))) == True{} : Bool}
  for ours: {Nat.is_le(Nat.sub(Nat.add(S.at(d, S.free(c)), S.at(d, S.spent(c))), S.at(d, S.over(c))), S.at(d, S.lent(p))) == True{} : Bool}
  {Nat.add(S.net(d, p2), S.at(d, S.over(p))) == Nat.add(S.net(d, p), S.at(d, S.over(p2))) : Nat}

# LAW budget_close_takes_overrun (R7): closing a child takes its overrun
# from what the parent and the child have free, and only past that is it
# the parent's overrun; the child's spend is the parent's, the parent's
# holds and deadline stay, the child is left empty
# EXCLUDES: a child's overrun handed back to the parent as free budget, a
#   parent's overrun booked while free could pay it, the parent's holds or
#   deadline changed by a close
law budget_close_takes_overrun:
  for +c: B.Acct
  for +p: B.Acct
  for +p2: B.Acct
  for +c2: B.Acct
  for +d: B.Dim
  for g: {B.close(c, p) == B.Closed{p2, c2} : B.Close}
  {S.at(d, S.free(p2)) == Nat.sub(Nat.add(S.at(d, S.free(p)), S.at(d, S.free(c))), S.at(d, S.over(c))) : Nat} &
  {S.at(d, S.over(p2)) == Nat.add(S.at(d, S.over(p)), Nat.sub(S.at(d, S.over(c)), Nat.add(S.at(d, S.free(p)), S.at(d, S.free(c))))) : Nat} &
  {S.at(d, S.spent(p2)) == Nat.add(S.at(d, S.spent(p)), S.at(d, S.spent(c))) : Nat} &
  {S.holds(p2) == S.holds(p) : List<&2, B.Hold>} &
  {S.until(p2) == S.until(p) : Nat} &
  {c2 == S.empty() : B.Acct}

# LAW budget_carve_close_round_trip (R7): a child closed before it spent
# anything gives the parent's account back as it was
# EXCLUDES: budget lost or gained by a spawn that did nothing
law budget_carve_close_round_trip:
  for +ph: B.Phase
  for +now: Nat
  for +want: B.Ask
  for +base: B.Ask
  for +a: B.Acct
  for +p: B.Acct
  for +c: B.Acct
  for g: {B.carve(ph, now, want, base, a) == B.Carved{p, c} : B.Carve}
  {B.close(c, p) == B.Closed{a, S.empty()} : B.Close}

# Laws: funding (R8)
# ------------------

# LAW budget_fund_conserves (R8): funding adds exactly the amount to the
# budget of the account in every dimension (what repays the overrun
# included), its duration to the deadline, and keeps spent, lent and the
# holds
# EXCLUDES: added budget or time lost or doubled, an overrun forgiven
#   without being repaid
law budget_fund_conserves:
  for +n: B.Ask
  for +a: B.Acct
  for +d: B.Dim
  {Nat.add(S.net(d, B.fund(n, a)), S.at(d, S.over(a))) == Nat.add(Nat.add(S.net(d, a), S.at(d, S.amt(n))), S.at(d, S.over(B.fund(n, a)))) : Nat} &
  {S.until(B.fund(n, a)) == Nat.add(S.until(a), S.ms(n)) : Nat} &
  {S.spent(B.fund(n, a)) == S.spent(a) : B.Amt} &
  {S.lent(B.fund(n, a)) == S.lent(a) : B.Amt} &
  {S.holds(B.fund(n, a)) == S.holds(a) : List<&2, B.Hold>}

# LAW budget_fund_repays_first (R8): funding repays the overrun first and
# only the rest becomes free
# EXCLUDES: an overrun never repaid, added budget made free while an
#   overrun stands, more freed than was added
law budget_fund_repays_first:
  for +n: B.Ask
  for +a: B.Acct
  for +d: B.Dim
  {S.at(d, S.over(B.fund(n, a))) == Nat.sub(S.at(d, S.over(a)), S.at(d, S.amt(n))) : Nat} &
  {S.at(d, S.free(B.fund(n, a))) == Nat.add(S.at(d, S.free(a)), Nat.sub(S.at(d, S.amt(n)), S.at(d, S.over(a)))) : Nat}

# LAW budget_fund_resumes (R8): funding a request's ask with the
# reserves, the overrun and the time it lacks gets that work granted to a
# Working agent, under an id not held
# EXCLUDES: an exhausted task that added budget cannot resume, funding
#   that does not reach free, added time that does not move the deadline
law budget_fund_resumes:
  for +id: Nat
  for +now: Nat
  for +base: B.Ask
  for +keep: B.Ask
  for +step: B.Ask
  for +c: B.Ask
  for +a: B.Acct
  for fresh: {S.has(id, S.holds(a)) == False{} : Bool}
  {S.granted(B.reserve(B.Work{}, B.Working{}, id, now, base, keep, step, c, Nil{}, B.fund(B.Ask{S.amt(S.plus(S.plus(S.plus(c, base), keep), B.Ask{S.over(a), 0n})), Nat.sub(Nat.add(now, S.ms(S.plus(S.plus(c, base), keep))), S.until(a))}, a))) == True{} : Bool}

# Laws: the entry (R9)
# --------------------

# LAW budget_entry_answers (R9): the entry answers every request Rust
# spells, every number and count within the wire, with the model's
# decision spelled
# EXCLUDES: fields read in another order (keep and the wanted ask
#   swapped, now read as a duration, the child's account read as the
#   parent's), a dimension swapped, a hold lost, the tags swapped, a
#   default
law budget_entry_answers:
  for +q: FBg.Req
  for fit: {sp_fit_req(q) == True{} : Bool}
  {FBg.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW budget_entry_left_over (R9): a spelled request followed by more
# input answers the error form
# EXCLUDES: the input after the request ignored or read into a field
law budget_entry_left_over:
  for +q: FBg.Req
  for +ch: Char
  for +t: String
  for fit: {sp_fit_req(q) == True{} : Bool}
  {FBg.ffi(sp_w_req(q, SCon{ch, t})) == Wr.err("budget: malformed request") : String}

# LAW budget_entry_malformed_exact (R9): every error the entry answers is
# exactly `E budget: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law budget_entry_malformed_exact:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FBg.ffi(s)) == True{} : Bool}
  {FBg.ffi(s) == Wr.err("budget: malformed request") : String}

# LAW budget_entry_unknown_tag (R9): a tag past the known ones answers the
# error form, whatever follows it: a request tag past 4 (fund), a use tag
# past 2 (a side request), a phase tag past 2 (Exhausted) in a reserve
# (after any use) or in a carve; every such tag within the wire
# EXCLUDES: an unknown tag read as a known one (a corrupt or newer
#   caller's reservation answered as a side request, as work or a final
#   answer, an unknown phase read as Exhausted, an unknown request read as
#   a fund)
law budget_entry_unknown_tag:
  for +u: B.Use
  for +m: Nat
  for +n: Nat
  for +rest: String
  for fm: {LawsBase.wire_fits(5n+m) == True{} : Bool}
  for +fn: {LawsBase.wire_fits(3n+n) == True{} : Bool}
  {FBg.ffi(Wr.put_nat(5n+m, rest)) == Wr.err("budget: malformed request") : String} &
  {FBg.ffi(Wr.put_nat(0n, Wr.put_nat(3n+n, rest))) == Wr.err("budget: malformed request") : String} &
  {FBg.ffi(Wr.put_nat(0n, Wr.put_nat(sp_use_tag(u), Wr.put_nat(3n+n, rest)))) == Wr.err("budget: malformed request") : String} &
  {FBg.ffi(Wr.put_nat(2n, Wr.put_nat(3n+n, rest))) == Wr.err("budget: malformed request") : String}

# LAW budget_entry_example (R1-R11): anchor: the wire strings Rust sends
# and the replies it reads. At 100 ms, work of (5,5,1,1) for 50 ms with
# reserves above and its own of (2,2,0,0) and (2,2,0,1) for 10 ms each, on
# 20 free in every dimension until 1000, its largest step the same, is
# granted and not low; until 160 its 50 ms offer runs past the deadline
# but its 30 ms offer fits, at place 1, and two 30 ms steps do not: low;
# work of (30,1,1,1) is refused for money and wraps the
# agent up; a final answer one ms past the deadline is refused for time
# and exhausts the agent; work of 3 requests on 2 free is refused for
# requests; an exhausted agent is stopped; a hold of (5,5,1,1) settled at
# (3,2,1,1) returns the rest; a carve of (4,4,1,1) for 200 ms at 100 gives
# the child a deadline of 300, and the close of that child; funding
# (3,3,3,3) for 500 ms repays an overrun of 1 and moves the deadline to
# 1500; an unknown tag, a missing field and input left over are refused
# EXCLUDES: a field order other than Rust's, another reply spelling
law budget_entry_example:
  {[FBg.ffi("0,0,0,7,100,2,2,0,0,10,2,2,0,1,10,5,5,1,1,50,5,5,1,1,50,0,20,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,1000,"), FBg.ffi("0,0,0,7,100,2,2,0,0,10,2,2,0,1,10,5,5,1,1,30,5,5,1,1,50,1,5,5,1,1,30,20,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,160,"), FBg.ffi("0,0,0,7,100,2,2,0,0,10,2,2,0,1,10,0,0,0,0,0,30,1,1,1,50,0,20,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,1000,"), FBg.ffi("0,1,1,7,100,0,0,0,0,0,2,2,0,1,10,0,0,0,0,0,1,1,1,1,1,0,20,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,100,"), FBg.ffi("0,0,0,7,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,3,1,0,20,20,20,2,0,0,0,0,0,0,0,0,0,0,0,0,0,1000,"), FBg.ffi("0,1,2,7,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,0,20,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,1000,")] == ["0,0,5,5,1,1,50,15,15,19,19,0,0,0,0,0,0,0,0,0,0,0,0,1,7,5,5,1,1,1000,F", "0,1,5,5,1,1,30,15,15,19,19,0,0,0,0,0,0,0,0,0,0,0,0,1,7,5,5,1,1,160,T", "1,0,0,1,", "1,0,2,2,", "1,0,4,1,", "1,2,2,"] : List<&2, String>} &
  {[FBg.ffi("1,7,3,2,1,1,5,5,9,9,0,0,0,0,0,0,0,0,0,0,0,0,1,7,5,5,1,1,1000,"), FBg.ffi("2,0,100,4,4,1,1,200,2,2,0,1,10,10,10,10,10,0,0,0,0,0,0,0,0,0,0,0,0,0,1000,"), FBg.ffi("3,4,4,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,300,5,5,8,8,0,0,0,0,4,4,1,1,0,0,0,0,0,1000,"), FBg.ffi("4,3,3,3,3,500,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,0,1000,")] == ["7,8,9,9,3,2,1,1,0,0,0,0,0,0,0,0,0,1000,", "0,6,6,9,9,0,0,0,0,4,4,1,1,0,0,0,0,0,1000,4,4,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,300,", "0,9,9,9,9,0,0,0,0,0,0,0,0,0,0,0,0,0,1000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,", "2,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,1500,"] : List<&2, String>} &
  {[FBg.ffi("5,"), FBg.ffi("1,"), FBg.ffi("4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,x")] == [Wr.err("budget: malformed request"), Wr.err("budget: malformed request"), Wr.err("budget: malformed request")] : List<&2, String>}
