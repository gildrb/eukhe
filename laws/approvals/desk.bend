# eukhe: the laws of area approvals, section desk: one session's desk, the
# state machine of its open questions (bend/approvals.bend `dstep`), which
# the compiled core runs as the stepper of bend/ffi_approvals.bend
# (laws/approvals/entry.bend ties the entry to it)

import Base
import ../../bend/approvals.bend as Am
import ../base.bend as LawsBase

# LAWS (G5): Rust (crates/eukhe-daemon/src/shell_approval.rs) sends each
# event of a session as it arrives and does what the desk answers; the
# desk decides what the event means. Every input is free: any desk, any
# request ids, effects, sessions, answers, detaches, keys, fates, in any
# order.
#
# D1: a question that reaches the session gets the desk's next key; the
#     session's decision sends it to its clients (shown; open, waiting on
#     the clients), to the parent session (relayed; open, waiting on the
#     parent), or ends it (woken with its fate; not kept). The decision:
#     an interactive client shows it; the phone gateway alone ends it by
#     the gateway rule; no client relays it to the parent, or at a root
#     ends it unanswered.
# D2: a client's answer goes to the oldest open question waiting on the
#     clients whose frame names its request id (char by char): that one is
#     settled, woken with the fate of the answer (`route([Says{yes}])`),
#     the answer taken, the question removed; with no such question the
#     answer is refused (gone) and the desk is unchanged: the first answer
#     wins.
# D3: a detach that leaves no interactive client sends every question
#     waiting on the clients where the session's decision now sends it: up
#     to the parent (settled, relayed) or ended (settled, woken), in order;
#     a detach that leaves an interactive client changes nothing.
# D4: a step that stops waiting removes its question (settled if it waited
#     on the clients); another key changes nothing.
# D5: the parent's answer to a relayed question wakes it with that fate and
#     removes it; for any other key (one waiting on the clients, or none)
#     it changes nothing.
# D6: a question waits on the clients only
#     while an interactive client is attached (no lost wake-up); a session
#     whose only client is the phone gateway never shows or relays; a root
#     never relays.
# D7: the desks of a chain of sessions route a question exactly as
#     bend/approvals.bend `route` does (the transcript the Rust bridge test
#     compared, restated over the stepper).
# D8: over every sequence of events from the empty desk, no key is woken
#     twice: Rust wakes each waiting step at most once, whatever the order
#     of answers, detaches, cancels and the parent's answers.

# Spec helpers
# ------------

# x is one of xs
def sp_has(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), sp_has(rest, x))

# D1: the gateway rule: a step that writes a protected path (effect 5) or
# reads or writes a secret (effect 6) is refused; any other runs
def sp_guard(g: Bool) -> Am.Fate:
  match g:
    case True{}:
      Am.GatewayRefused{}
    case False{}:
      Am.Runs{}

def sp_rule(+es: List<&2, Nat>) -> Am.Fate:
  sp_guard(Bool.or(sp_has(es, 5n), sp_has(es, 6n)))

# D2: the clients' answer: yes runs the step, no denies it
def sp_answered(+es: List<&2, Nat>, yes: Bool) -> Am.Fate:
  match yes:
    case True{}:
      Am.Runs{}
    case False{}:
      Am.Denied{}

# D1: what a session that is h, with a parent or not, does with the
# question of a step with the effects es: an interactive client shows it;
# the phone gateway alone ends it by the gateway rule; with no client it
# goes to the parent, or at a root no one answers (unanswered)
def sp_next(+es: List<&2, Nat>, h: Am.Here, p: Bool) -> Am.Next:
  match h:
    case Am.Nobody{}:
      match p:
        case True{}:
          Am.Relay{}
        case False{}:
          Am.Ends{Am.Unheard{}}
    case Am.GatewayOnly{}:
      Am.Ends{sp_rule(es)}
    case Am.Clients{}:
      Am.Show{}

# D1, D2: what becomes of a step whose question ended so: the clients'
# answer, no one, or the gateway rule
def sp_fate(+es: List<&2, Nat>, e: Am.End) -> Am.Fate:
  match e:
    case Am.Answered{a, y}:
      sp_answered(es, y)
    case Am.Unanswered{}:
      Am.Unheard{}
    case Am.Ruled{a}:
      sp_rule(es)

def sp_cons(q: Am.Q, r: Am.QF) -> Am.QF:
  match r:
    case Am.QFound{q2, r2}:
      Am.QFound{q2, q <> r2}
    case Am.QNone{}:
      Am.QNone{}

def sp_hit(b: Bool, q: Am.Q, +rest: List<&2, Am.Q>, r: Am.QF) -> Am.QF:
  match b:
    case True{}:
      Am.QFound{q, rest}
    case False{}:
      sp_cons(q, r)

def sp_clients(w: Am.Wait) -> Bool:
  match w:
    case Am.OnClients{}:
      True{}
    case Am.OnParent{}:
      False{}

# D2: the oldest question waiting on the clients whose frame names id, and
# the others in order
def sp_find(qs: List<&2, Am.Q>, +id: String) -> Am.QF:
  match qs:
    case Nil{}:
      Am.QNone{}
    case q <> +rest:
      match q:
        case Am.Q{k, +i, es, +w}:
          sp_hit(Bool.and(sp_clients(w), LawsBase.text_same(i, id)), Am.Q{k, i, es, w}, rest, sp_find(rest, id))

# D4, D5: the question with key key, and the others in order
def sp_take(qs: List<&2, Am.Q>, +key: Nat) -> Am.QF:
  match qs:
    case Nil{}:
      Am.QNone{}
    case q <> +rest:
      match q:
        case Am.Q{+k, i, es, w}:
          sp_hit(Nat.is_eq(k, key), Am.Q{k, i, es, w}, rest, sp_take(rest, key))

def sp_reroute.q(w: Am.Wait, +k: Nat, +i: String, +es: List<&2, Nat>, x: Am.Next, r: List<&2, Am.Q> & List<&2, Am.Act>) -> List<&2, Am.Q> & List<&2, Am.Act>:
  match w:
    case Am.OnParent{}:
      (qs, as) = r
      (Am.Q{k, i, es, Am.OnParent{}} <> qs, as)
    case Am.OnClients{}:
      match x:
        case Am.Show{}:
          (qs, as) = r
          (Am.Q{k, i, es, Am.OnClients{}} <> qs, as)
        case Am.Relay{}:
          (qs, as) = r
          (Am.Q{k, i, es, Am.OnParent{}} <> qs, Am.ASettle{k} <> Am.ARelay{k} <> as)
        case Am.Ends{f}:
          (qs, as) = r
          (qs, Am.ASettle{k} <> Am.AWake{k, f} <> as)

# D3: each question waiting on the clients goes where the decision sends it
def sp_reroute(qs: List<&2, Am.Q>, +h: Am.Here, +p: Bool) -> List<&2, Am.Q> & List<&2, Am.Act>:
  match qs:
    case Nil{}:
      (Nil{}, Nil{})
    case q <> rest:
      match q:
        case Am.Q{k, i, +es, w}:
          sp_reroute.q(w, k, i, es, sp_next(es, h, p), sp_reroute(rest, h, p))

def sp_ask(+n: Nat, +id: String, +es: List<&2, Nat>, +qs: List<&2, Am.Q>, x: Am.Next) -> Am.D & List<&2, Am.Act>:
  match x:
    case Am.Show{}:
      (Am.D{1n+n, List.append(&2, Am.Q, qs, [Am.Q{n, id, es, Am.OnClients{}}])}, [Am.AShow{n}])
    case Am.Relay{}:
      (Am.D{1n+n, List.append(&2, Am.Q, qs, [Am.Q{n, id, es, Am.OnParent{}}])}, [Am.ARelay{n}])
    case Am.Ends{f}:
      (Am.D{1n+n, qs}, [Am.AWake{n, f}])

def sp_answer(+n: Nat, +qs: List<&2, Am.Q>, +yes: Bool, r: Am.QF) -> Am.D & List<&2, Am.Act>:
  match r:
    case Am.QFound{q, rest}:
      match q:
        case Am.Q{+k, i, +es, w}:
          (Am.D{n, rest}, [Am.ASettle{k}, Am.AWake{k, sp_answered(es, yes)}, Am.ATook{}])
    case Am.QNone{}:
      (Am.D{n, qs}, [Am.AGone{}])

def sp_put(+n: Nat, r: List<&2, Am.Q> & List<&2, Am.Act>) -> Am.D & List<&2, Am.Act>:
  (qs, as) = r
  (Am.D{n, qs}, as)

def sp_detach(+n: Nat, +qs: List<&2, Am.Q>, h: Am.Here, +p: Bool) -> Am.D & List<&2, Am.Act>:
  match h:
    case Am.Clients{}:
      (Am.D{n, qs}, Nil{})
    case Am.Nobody{}:
      sp_put(n, sp_reroute(qs, Am.Nobody{}, p))
    case Am.GatewayOnly{}:
      sp_put(n, sp_reroute(qs, Am.GatewayOnly{}, p))

def sp_cancel(+n: Nat, +qs: List<&2, Am.Q>, r: Am.QF) -> Am.D & List<&2, Am.Act>:
  match r:
    case Am.QFound{q, rest}:
      match q:
        case Am.Q{+k, i, es, w}:
          match w:
            case Am.OnClients{}:
              (Am.D{n, rest}, [Am.ASettle{k}])
            case Am.OnParent{}:
              (Am.D{n, rest}, Nil{})
    case Am.QNone{}:
      (Am.D{n, qs}, Nil{})

def sp_back(+n: Nat, +qs: List<&2, Am.Q>, +f: Am.Fate, r: Am.QF) -> Am.D & List<&2, Am.Act>:
  match r:
    case Am.QFound{q, rest}:
      match q:
        case Am.Q{+k, i, es, w}:
          match w:
            case Am.OnParent{}:
              (Am.D{n, rest}, [Am.AWake{k, f}])
            case Am.OnClients{}:
              (Am.D{n, qs}, Nil{})
    case Am.QNone{}:
      (Am.D{n, qs}, Nil{})

# D1-D5: the desk after one event, and what Rust does
def sp_dstep(d: Am.D, e: Am.Ev) -> Am.D & List<&2, Am.Act>:
  match d:
    case Am.D{+n, +qs}:
      match e:
        case Am.EAsk{id, +es, +h, +p}:
          sp_ask(n, id, es, qs, sp_next(es, h, p))
        case Am.EAnswer{+id, yes}:
          sp_answer(n, qs, yes, sp_find(qs, id))
        case Am.EDetach{h, p}:
          sp_detach(n, qs, h, p)
        case Am.ECancel{+key}:
          sp_cancel(n, qs, sp_take(qs, key))
        case Am.EBack{+key, f}:
          sp_back(n, qs, f, sp_take(qs, key))

# Terms of the safety laws (D6)
# -----------------------------

def ds_desk(r: Am.D & List<&2, Am.Act>) -> Am.D:
  (d, as) = r
  d

def ds_acts(r: Am.D & List<&2, Am.Act>) -> List<&2, Am.Act>:
  (d, as) = r
  as

def ds_next(d: Am.D) -> Nat:
  match d:
    case Am.D{n, qs}:
      n

def ds_qs(d: Am.D) -> List<&2, Am.Q>:
  match d:
    case Am.D{n, qs}:
      qs

def ds_any_clients(qs: List<&2, Am.Q>) -> Bool:
  match qs:
    case Nil{}:
      False{}
    case q <> t:
      match q:
        case Am.Q{k, i, es, w}:
          Bool.or(sp_clients(w), ds_any_clients(t))

def ds_any_relay(as: List<&2, Am.Act>) -> Bool:
  match as:
    case Nil{}:
      False{}
    case a <> t:
      match a:
        case Am.ARelay{k}:
          True{}
        case Am.AShow{k}:
          ds_any_relay(t)
        case Am.ASettle{k}:
          ds_any_relay(t)
        case Am.AWake{k, f}:
          ds_any_relay(t)
        case Am.ATook{}:
          ds_any_relay(t)
        case Am.AGone{}:
          ds_any_relay(t)

# Terms of the wake-once law (D8)
# -------------------------------

def dw_hit(b: Bool, c: Nat) -> Nat:
  match b:
    case True{}:
      1n+c
    case False{}:
      c

# how many times k is in xs
def dw_count(xs: List<&2, Nat>, +k: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      dw_hit(Nat.is_eq(x, k), dw_count(t, k))

# the keys the acts wake, in order
def dw_woke(as: List<&2, Am.Act>) -> List<&2, Nat>:
  match as:
    case Nil{}:
      Nil{}
    case a <> t:
      match a:
        case Am.AWake{k, f}:
          k <> dw_woke(t)
        case Am.AShow{k}:
          dw_woke(t)
        case Am.ASettle{k}:
          dw_woke(t)
        case Am.ARelay{k}:
          dw_woke(t)
        case Am.ATook{}:
          dw_woke(t)
        case Am.AGone{}:
          dw_woke(t)

# every key the desk's replies wake, fed the events es from the desk d, in
# order
def dw_run(es: List<&2, Am.Ev>, +d: Am.D) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      List.append(&2, Nat, dw_woke(ds_acts(Am.dstep(d, e))), dw_run(t, ds_desk(Am.dstep(d, e))))

# The chain (D7)
# --------------
# A question of the asking session, through the desks of its chain: each
# session's clients do what its Desk says (away: no client; left: shown,
# then the interactive clients detach; says: shown, then the first answer;
# phone: the gateway alone; phone-left: shown, the interactive clients
# detach, the gateway stays). A relay asks the parent's desk, and its
# fate comes back to the session's desk.

# who answers the session when the question reaches it
def ch_here(d: Am.Desk) -> Am.Here:
  match d:
    case Am.Away{}:
      Am.Nobody{}
    case Am.Left{}:
      Am.Clients{}
    case Am.Says{y}:
      Am.Clients{}
    case Am.Phone{}:
      Am.GatewayOnly{}
    case Am.PhoneLeft{}:
      Am.Clients{}

# what the clients do once the question is shown
def ch_then(d: Am.Desk, +p: Bool) -> Am.Ev:
  match d:
    case Am.Away{}:
      Am.EDetach{Am.Nobody{}, p}
    case Am.Left{}:
      Am.EDetach{Am.Nobody{}, p}
    case Am.Says{y}:
      Am.EAnswer{"q", y}
    case Am.Phone{}:
      Am.EDetach{Am.GatewayOnly{}, p}
    case Am.PhoneLeft{}:
      Am.EDetach{Am.GatewayOnly{}, p}

# the fate the acts wake key 0 with, if any; whether they show or relay it
def ch_woke(as: List<&2, Am.Act>) -> Maybe<&2, Am.Fate>:
  match as:
    case Nil{}:
      None{}
    case a <> t:
      match a:
        case Am.AWake{k, f}:
          Some{f}
        case Am.AShow{k}:
          ch_woke(t)
        case Am.ASettle{k}:
          ch_woke(t)
        case Am.ARelay{k}:
          ch_woke(t)
        case Am.ATook{}:
          ch_woke(t)
        case Am.AGone{}:
          ch_woke(t)

def ch_shows(as: List<&2, Am.Act>) -> Bool:
  match as:
    case Nil{}:
      False{}
    case a <> t:
      match a:
        case Am.AShow{k}:
          True{}
        case Am.ASettle{k}:
          ch_shows(t)
        case Am.ARelay{k}:
          ch_shows(t)
        case Am.AWake{k, f}:
          ch_shows(t)
        case Am.ATook{}:
          ch_shows(t)
        case Am.AGone{}:
          ch_shows(t)

def ch_up(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      (1n+x) <> ch_up(t)

def ch_fate(m: Maybe<&2, Am.Fate>) -> Am.Fate:
  match m:
    case None{}:
      Am.Unheard{}
    case Some{f}:
      f

# the sessions that showed the question (0: this one) and its fate, from
# the parent's (shown, fate), after this session's desk relayed it
def ch_relayed(+shown0: List<&2, Nat>, r: List<&2, Nat> & Am.Fate, +d1: Am.D) -> List<&2, Nat> & Am.Fate:
  (up, f) = r
  (List.append(&2, Nat, shown0, ch_up(up)), ch_fate(ch_woke(ds_acts(Am.dstep(d1, Am.EBack{0n, f})))))

# what a reply did with the question: woke it (with its fate), relayed
# it, showed it, or nothing of these
type Ck is Data:
  CkWoke{f: Am.Fate}
  CkRelay{}
  CkShow{}
  CkNone{}

def ch_kind(as: List<&2, Am.Act>) -> Ck:
  match as:
    case Nil{}:
      CkNone{}
    case a <> t:
      match a:
        case Am.AWake{k, f}:
          CkWoke{f}
        case Am.ARelay{k}:
          CkRelay{}
        case Am.AShow{k}:
          CkShow{}
        case Am.ASettle{k}:
          ch_kind(t)
        case Am.ATook{}:
          ch_kind(t)
        case Am.AGone{}:
          ch_kind(t)

# after the clients of a session that showed the question acted (k), the
# parent's (shown, fate) up, the desk d2 after the clients' event
def ch_after(k: Ck, up: List<&2, Nat> & Am.Fate, +d2: Am.D) -> List<&2, Nat> & Am.Fate:
  match k:
    case CkWoke{f}:
      ([0n], f)
    case CkRelay{}:
      ch_relayed([0n], up, d2)
    case CkShow{}:
      ([0n], Am.Unheard{})
    case CkNone{}:
      ([0n], Am.Unheard{})

def ch_at.k(k: Ck, +d: Am.Desk, +p: Bool, +d1: Am.D, up: List<&2, Nat> & Am.Fate) -> List<&2, Nat> & Am.Fate:
  match k:
    case CkWoke{f}:
      (Nil{}, f)
    case CkRelay{}:
      ch_relayed(Nil{}, up, d1)
    case CkShow{}:
      ch_after(ch_kind(ds_acts(Am.dstep(d1, ch_then(d, p)))), up, ds_desk(Am.dstep(d1, ch_then(d, p))))
    case CkNone{}:
      (Nil{}, Am.Unheard{})

# the session with Desk d (a parent when p): its desk's step on the
# question (r1), and the parent's (shown, fate) up
def ch_at(+d: Am.Desk, +p: Bool, r1: Am.D & List<&2, Am.Act>, up: List<&2, Nat> & Am.Fate) -> List<&2, Nat> & Am.Fate:
  (d1, as1) = r1
  ch_at.k(ch_kind(as1), d, p, d1, up)

# the question of the step with the effects es at the first session of
# ds, through the desks of the chain: the sessions that showed it, and its
# fate
def ch_run(ds: List<&2, Am.Desk>, +es: List<&2, Nat>) -> List<&2, Nat> & Am.Fate:
  match ds:
    case Nil{}:
      (Nil{}, Am.Unheard{})
    case +d <> +rest:
      ch_at(d, Bool.not(List.is_empty(&2, Am.Desk, rest)), Am.dstep(Am.D{0n, Nil{}}, Am.EAsk{"q", es, ch_here(d), Bool.not(List.is_empty(&2, Am.Desk, rest))}), ch_run(rest, es))

# Laws
# ----

# LAW approvals_desk_step_spec (D1-D5): every event, from every desk,
# moves the desk and answers the acts exactly as the spec's table
# EXCLUDES: an answer applied to another question than the oldest one its
#   frame names, or to a relayed one; a second answer taken (the first
#   answer wins); a detach that strands a question on clients that left,
#   or moves one waiting on the parent; a cancel or a parent's answer for
#   one key that removes or wakes another; a relayed question woken by a
#   client; keys reused
law approvals_desk_step_spec:
  for +d: Am.D
  for +e: Am.Ev
  {Am.dstep(d, e) == sp_dstep(d, e) : Am.D & List<&2, Am.Act>}

# LAW approvals_desk_never_stranded (D6): from every desk, a detach that
# leaves no interactive client leaves no question waiting on the clients
# EXCLUDES: a lost wake-up: a step that waits on clients that all left
law approvals_desk_never_stranded:
  for +d: Am.D
  for +p: Bool
  {[ds_any_clients(ds_qs(ds_desk(Am.dstep(d, Am.EDetach{Am.Nobody{}, p})))), ds_any_clients(ds_qs(ds_desk(Am.dstep(d, Am.EDetach{Am.GatewayOnly{}, p}))))] == [False{}, False{}] : List<&2, Bool>}

# LAW approvals_desk_gateway_never_waits (D6): from every desk, a question
# that reaches a session whose only client is the phone gateway is woken at
# once by the gateway rule: no frame, no relay, and the desk keeps its
# other questions
# EXCLUDES: a phone-only session that waits or hands the question up
law approvals_desk_gateway_never_waits:
  for +d: Am.D
  for +id: String
  for +es: List<&2, Nat>
  for +p: Bool
  {Am.dstep(d, Am.EAsk{id, es, Am.GatewayOnly{}, p}) == (Am.D{1n+ds_next(d), ds_qs(d)}, [Am.AWake{ds_next(d), sp_rule(es)}]) : Am.D & List<&2, Am.Act>}

# LAW approvals_desk_root_never_relays (D6): from every desk, a root
# session (no parent) never relays, on a question or on a detach
# EXCLUDES: a relay to a parent that does not exist (a question lost)
law approvals_desk_root_never_relays:
  for +d: Am.D
  for +id: String
  for +es: List<&2, Nat>
  for +h: Am.Here
  {[ds_any_relay(ds_acts(Am.dstep(d, Am.EAsk{id, es, h, False{}}))), ds_any_relay(ds_acts(Am.dstep(d, Am.EDetach{h, False{}})))] == [False{}, False{}] : List<&2, Bool>}

# LAW approvals_desk_is_route (D7): the desks of a chain of sessions route
# a question exactly as `route` does: the sessions that show it, in order,
# and the fate of the step
# EXCLUDES: a relay past clients that answer, a frame on a session that
#   should not show it, a fate other than the route's (the transcript the
#   Rust bridge compared)
law approvals_desk_is_route:
  for +ds: List<&2, Am.Desk>
  for +es: List<&2, Nat>
  {ch_run(ds, es) == (Am.Out.shown(Am.route(ds)), Am.fate(es, Am.Out.end(Am.route(ds)))) : List<&2, Nat> & Am.Fate}

# LAW approvals_desk_example (D1-D6): anchor: a question shown and answered
# yes, a second answer refused, a relayed one woken by its parent's denial,
# a shown one that its clients leave at a root (woken unanswered)
law approvals_desk_example:
  {ds_acts(Am.dstep(Am.D{2n, [Am.Q{0n, "a", [1n], Am.OnClients{}}, Am.Q{1n, "b", [1n], Am.OnParent{}}]}, Am.EAnswer{"a", True{}})) == [Am.ASettle{0n}, Am.AWake{0n, Am.Runs{}}, Am.ATook{}] : List<&2, Am.Act>} & {ds_acts(Am.dstep(Am.D{2n, [Am.Q{1n, "b", [1n], Am.OnParent{}}]}, Am.EAnswer{"a", True{}})) == [Am.AGone{}] : List<&2, Am.Act>} & {ds_acts(Am.dstep(Am.D{2n, [Am.Q{1n, "b", [1n], Am.OnParent{}}]}, Am.EBack{1n, Am.Denied{}})) == [Am.AWake{1n, Am.Denied{}}] : List<&2, Am.Act>} & {ds_acts(Am.dstep(Am.D{1n, [Am.Q{0n, "a", [1n], Am.OnClients{}}]}, Am.EDetach{Am.Nobody{}, False{}})) == [Am.ASettle{0n}, Am.AWake{0n, Am.Unheard{}}] : List<&2, Am.Act>}

# LAW approvals_desk_wakes_once (D8): over every sequence of events, fed
# from the empty desk as Rust opens it, every key is woken at most once
# EXCLUDES: a step woken twice (a second answer, a detach or a parent's
#   answer that wakes a question already woken), a key given to two
#   questions, an ended question kept open
law approvals_desk_wakes_once:
  for +es: List<&2, Am.Ev>
  for +k: Nat
  {Nat.is_le(dw_count(dw_run(es, Am.D{0n, Nil{}}), k), 1n) == True{} : Bool}

# LAW approvals_desk_fates_example (D1-D3): anchor: the fates the desk
# wakes steps with: a phone-only session refuses a protected-path write
# (effects 1, 5) and a secret read (0, 6) at once and runs a plain write;
# a protected-path write its clients approve runs; a secret read they deny
# is denied; a protected-path write the interactive clients leave to the
# phone gateway is refused, and one they leave at a root is unanswered
# EXCLUDES: a gateway rule that runs a guarded step or refuses a plain
#   one, an approval read as the gateway rule, a denial read as a yes, a
#   left question that runs
law approvals_desk_fates_example:
  {ds_acts(Am.dstep(Am.D{0n, Nil{}}, Am.EAsk{"w", [1n, 5n], Am.GatewayOnly{}, True{}})) == [Am.AWake{0n, Am.GatewayRefused{}}] : List<&2, Am.Act>} &
  {ds_acts(Am.dstep(Am.D{0n, Nil{}}, Am.EAsk{"s", [0n, 6n], Am.GatewayOnly{}, False{}})) == [Am.AWake{0n, Am.GatewayRefused{}}] : List<&2, Am.Act>} &
  {ds_acts(Am.dstep(Am.D{3n, Nil{}}, Am.EAsk{"x", [1n], Am.GatewayOnly{}, False{}})) == [Am.AWake{3n, Am.Runs{}}] : List<&2, Am.Act>} &
  {ds_acts(Am.dstep(Am.D{1n, [Am.Q{0n, "w", [1n, 5n], Am.OnClients{}}]}, Am.EAnswer{"w", True{}})) == [Am.ASettle{0n}, Am.AWake{0n, Am.Runs{}}, Am.ATook{}] : List<&2, Am.Act>} &
  {ds_acts(Am.dstep(Am.D{1n, [Am.Q{0n, "s", [0n, 6n], Am.OnClients{}}]}, Am.EAnswer{"s", False{}})) == [Am.ASettle{0n}, Am.AWake{0n, Am.Denied{}}, Am.ATook{}] : List<&2, Am.Act>} &
  {ds_acts(Am.dstep(Am.D{1n, [Am.Q{0n, "w", [1n, 5n], Am.OnClients{}}]}, Am.EDetach{Am.GatewayOnly{}, True{}})) == [Am.ASettle{0n}, Am.AWake{0n, Am.GatewayRefused{}}] : List<&2, Am.Act>} &
  {ds_acts(Am.dstep(Am.D{1n, [Am.Q{0n, "w", [1n, 5n], Am.OnClients{}}]}, Am.EDetach{Am.Nobody{}, False{}})) == [Am.ASettle{0n}, Am.AWake{0n, Am.Unheard{}}] : List<&2, Am.Act>}

# LAW approvals_desk_terms_exact: the terms of the desk laws mean what they
# say: a question waiting on the clients is seen, one on the parent is not;
# a relay among acts is seen, other acts are not; the woken keys are the
# wakes' keys in order; a count counts; a run collects every reply's wakes
# EXCLUDES: a vacuous term (one constant answer) that would make
#   approvals_desk_never_stranded, approvals_desk_root_never_relays or
#   approvals_desk_wakes_once say nothing
law approvals_desk_terms_exact:
  {[ds_any_clients([Am.Q{0n, "a", Nil{}, Am.OnParent{}}, Am.Q{1n, "b", Nil{}, Am.OnClients{}}]), ds_any_clients([Am.Q{0n, "a", Nil{}, Am.OnParent{}}]), ds_any_relay([Am.ASettle{0n}, Am.ARelay{0n}]), ds_any_relay([Am.AShow{0n}, Am.ASettle{0n}, Am.AWake{0n, Am.Runs{}}, Am.ATook{}, Am.AGone{}])] == [True{}, False{}, True{}, False{}] : List<&2, Bool>} &
  {dw_woke([Am.AShow{0n}, Am.AWake{1n, Am.Runs{}}, Am.ASettle{2n}, Am.ARelay{4n}, Am.AWake{3n, Am.Denied{}}, Am.ATook{}, Am.AGone{}]) == [1n, 3n] : List<&2, Nat>} &
  {[dw_count([1n, 3n, 1n], 1n), dw_count([1n, 3n, 1n], 2n)] == [2n, 0n] : List<&2, Nat>} &
  {dw_run([Am.EAsk{"a", [1n], Am.GatewayOnly{}, False{}}, Am.EAsk{"b", [1n], Am.Clients{}, False{}}, Am.EAnswer{"b", False{}}], Am.D{0n, Nil{}}) == [0n, 1n] : List<&2, Nat>}

# LAW approvals_fate_spec (D1, D2): what becomes of a step, for every
# effects and every end of its question: the clients' yes runs it and their
# no denies it, whatever its effects and whichever session answered; no
# answer is unanswered; the gateway rule refuses a protected-path write or a
# secret and runs any other step
# EXCLUDES: a no that runs a step (for some effects), an unanswered
#   question that runs, an answer read through the gateway rule, a fate
#   that depends on the session that answered
law approvals_fate_spec:
  for +es: List<&2, Nat>
  for +e: Am.End
  {Am.fate(es, e) == sp_fate(es, e) : Am.Fate}
