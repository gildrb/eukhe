# eukhe: the laws of area approvals

import Base
import ../bend/approvals.bend as Am
import ../bend/ffi_approvals.bend as FAm
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- approvals ----

# LAWS (G5): a child's question reaches its root's user, a session that
# runs only from the phone gateway never waits, and the default auto set
# runs every step but the never-auto ones. Each law is an open claim about
# the model in bend/approvals.bend; PROOF.bend proves them (as Approvals.<law>)
# with the lemmas of proof/approvals/.

# (G5) A child's question reaches its root's user
# ------------------------------------------------
# docs/tools.md G5, the model in bend/approvals.bend. A chain lists the
# sessions from the one that asks (a subagent, or a root) up to its root.
# The bridge test in crates/eukhe-daemon/src/shell_approval/bridge.rs
# runs the real approvals of a chain of sessions (clients attached or
# not, answering, denying or leaving, the phone gateway attached alone or
# beside them) on the scenarios of bridge/bridge_approvals.bend, and both
# must print what the model prints.

# LAW child_answered_by_root: when no session below the root has clients that answer, a
# subagent's question reaches the root's clients, and their answer is the
# verdict
law child_answered_by_root:
  for +below: List<&2, Am.Desk>
  for quiet: {Am.quiet(below) == True{} : Bool}
  for +yes: Bool
  {Am.Out.end(Am.route(List.append(&2, Am.Desk, below, [Am.Says{yes}]))) == Am.Answered{List.length(&2, Am.Desk, below), yes} : Am.End}

# LAW nearest_answer_wins: the first session up the chain whose clients answer gives the
# verdict, whatever the sessions above it
law nearest_answer_wins:
  for +below: List<&2, Am.Desk>
  for quiet: {Am.quiet(below) == True{} : Bool}
  for +yes: Bool
  for +above: List<&2, Am.Desk>
  {Am.Out.end(Am.route(List.append(&2, Am.Desk, below, Am.Says{yes} <> above))) == Am.Answered{List.length(&2, Am.Desk, below), yes} : Am.End}

# LAW unanswered_only_when_quiet: a question is unanswered (a denial) only when no session of the
# whole chain has clients that answer
law unanswered_only_when_quiet:
  for +ds: List<&2, Am.Desk>
  for none: {Am.Out.end(Am.route(ds)) == Am.Unanswered{} : Am.End}
  {Am.quiet(ds) == True{} : Bool}

# LAW quiet_is_unanswered: and then it is unanswered: no session invents an answer
law quiet_is_unanswered:
  for +ds: List<&2, Am.Desk>
  for quiet: {Am.quiet(ds) == True{} : Bool}
  {Am.Out.end(Am.route(ds)) == Am.Unanswered{} : Am.End}

# (G5) A session that runs only from the phone gateway never waits
# -----------------------------------------------------------------
# The phone gateway shows no question. A step is guarded when it writes a
# protected path (effect 5: eukhe's own config and credentials, a .git or
# .eukhe dir, a PATH dir) or reads or writes a secret (effect 6).

# LAW gateway_never_waits: a step of a session whose only clients are the phone gateway never
# waits: no client gets a frame, the question does not go up the chain,
# and the session's gateway rule answers at once
law gateway_never_waits:
  for +above: List<&2, Am.Desk>
  {Am.route(Am.Phone{} <> above) == Am.Out{Nil{}, Am.Ruled{0n}} : Am.Out}

# LAW left_to_the_gateway: a question the interactive clients leave unanswered while the
# phone gateway stays falls to the gateway rule, not up the chain
law left_to_the_gateway:
  for +above: List<&2, Am.Desk>
  {Am.route(Am.PhoneLeft{} <> above) == Am.Out{[0n], Am.Ruled{0n}} : Am.Out}

# LAW gateway_rules_a_subagent: a subagent's question that reaches a session whose only clients
# are the phone gateway (no session below it has clients that answer)
# fares as that session's own step: the same rule answers it
law gateway_rules_a_subagent:
  for +below: List<&2, Am.Desk>
  for quiet: {Am.quiet(below) == True{} : Bool}
  for +es: List<&2, Nat>
  for +above: List<&2, Am.Desk>
  {Am.fate(es, Am.Out.end(Am.route(List.append(&2, Am.Desk, below, Am.Phone{} <> above)))) == Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))) : Am.Fate}

# ---- approvals entry ----

# LAWS (G5, compiled core): each session's decision on a question runs as
# the compiled model (bend/ffi_approvals.bend over bend/approvals.bend;
# Rust: crates/eukhe-bend/src/rules/approvals.rs, called by
# crates/eukhe-daemon/src/shell_approval.rs at each session the question
# reaches). Each law is an open claim about FAm.ffi, the function the core
# runs, stated with spec spellers built only from the wire primitives of
# bend/wire.bend; the replies are the route of `Am.route` one session at a
# time:
#
# R1: a session with an interactive client shows the question; one with
#     only the phone gateway ends it by the gateway rule (the fate of
#     `route([Phone])`); one with no client relays it to its parent, or,
#     with no parent, ends it unanswered (the fate of `route([])`); the
#     clients' answer y fares as `route([Says{y}])`; the default auto set
#     is `Am.default_auto`.
# R2: every other input answers exactly the error form "approvals:
#     malformed request".
# Every input is free: any effects, any session, parent or not, any
# answer, any text.

# Spec spellers
# -------------

def spell_ns(xs: List<&2, Nat>, rest: String) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)

def spell_here(h: Am.Here) -> Nat:
  match h:
    case Am.Nobody{}:
      0n
    case Am.GatewayOnly{}:
      1n
    case Am.Clients{}:
      2n

# the request q as Rust writes it, then rest
def spell_req(q: FAm.Req, rest: String) -> String:
  match q:
    case FAm.QNext{h, es, p}:
      Wr.put_nat(0n, Wr.put_nat(spell_here(h), spell_ns(es, Wr.put_bool(p, rest))))
    case FAm.QAnswered{es, y}:
      Wr.put_nat(1n, spell_ns(es, Wr.put_bool(y, rest)))
    case FAm.QDefault{}:
      Wr.put_nat(2n, rest)

# a list of Nats fits the wire: its length and each item
def ns_fit(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

# every number of a request fits the wire
def req_fits(q: FAm.Req) -> Bool:
  match q:
    case FAm.QNext{h, es, p}:
      ns_fit(es)
    case FAm.QAnswered{es, y}:
      ns_fit(es)
    case FAm.QDefault{}:
      True{}

# a fate: runs 0, denied 1, unanswered 2, refused by the gateway rule 3
def spell_fate(f: Am.Fate, rest: String) -> String:
  match f:
    case Am.Runs{}:
      Wr.put_nat(0n, rest)
    case Am.Denied{}:
      Wr.put_nat(1n, rest)
    case Am.Unheard{}:
      Wr.put_nat(2n, rest)
    case Am.GatewayRefused{}:
      Wr.put_nat(3n, rest)

# what a session that is h does with the question of a step with the
# effects es: show it (0), relay it to the parent (1), or end it (2, the
# fate), as `Am.route` decides for that session
def spell_next(+es: List<&2, Nat>, h: Am.Here, p: Bool) -> String:
  match h:
    case Am.Nobody{}:
      match p:
        case True{}:
          Wr.put_nat(1n, "")
        case False{}:
          Wr.put_nat(2n, spell_fate(Am.fate(es, Am.Out.end(Am.route(Nil{}))), ""))
    case Am.GatewayOnly{}:
      Wr.put_nat(2n, spell_fate(Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))), ""))
    case Am.Clients{}:
      Wr.put_nat(0n, "")

# the model's decision on q, spelled
def spell_answer(q: FAm.Req) -> String:
  match q:
    case FAm.QNext{h, es, p}:
      spell_next(es, h, p)
    case FAm.QAnswered{+es, y}:
      spell_fate(Am.fate(es, Am.Out.end(Am.route([Am.Says{y}]))), "")
    case FAm.QDefault{}:
      spell_ns(Am.default_auto(), "")

# the error form of every input that is not exactly one request
def malformed() -> String:
  SCon{'E', SCon{' ', "approvals: malformed request"}}

# Reader: the requests, read with the wire primitives
# ---------------------------------------------------

def read_ns(s: String) -> Wr.Dec<List<&2, Nat>>:
  Wr.get_list(~Nat, ~Wr.get_nat, s)

def read_next.parent(h: Am.Here, es: List<&2, Nat>, r: Wr.Dec<Bool>) -> Wr.Dec<FAm.Req>:
  match r:
    case Wr.Got{p, s}:
      Wr.Got{FAm.QNext{h, es, p}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_next.effs(h: Am.Here, r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FAm.Req>:
  match r:
    case Wr.Got{es, s}:
      read_next.parent(h, es, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_next.here(t: Nat, s: String) -> Wr.Dec<FAm.Req>:
  match t:
    case 0n:
      read_next.effs(Am.Nobody{}, read_ns(s))
    case 1n:
      read_next.effs(Am.GatewayOnly{}, read_ns(s))
    case 2n:
      read_next.effs(Am.Clients{}, read_ns(s))
    case 3n+u:
      Wr.Bad{}

def read_next(r: Wr.Dec<Nat>) -> Wr.Dec<FAm.Req>:
  match r:
    case Wr.Got{t, s}:
      read_next.here(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_answered.yes(es: List<&2, Nat>, r: Wr.Dec<Bool>) -> Wr.Dec<FAm.Req>:
  match r:
    case Wr.Got{y, s}:
      Wr.Got{FAm.QAnswered{es, y}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_answered(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FAm.Req>:
  match r:
    case Wr.Got{es, s}:
      read_answered.yes(es, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_req.tag(t: Nat, s: String) -> Wr.Dec<FAm.Req>:
  match t:
    case 0n:
      read_next(Wr.get_nat(s))
    case 1n:
      read_answered(read_ns(s))
    case 2n:
      Wr.Got{FAm.QDefault{}, s}
    case 3n+u:
      Wr.Bad{}

def read_req.go(r: Wr.Dec<Nat>) -> Wr.Dec<FAm.Req>:
  match r:
    case Wr.Got{t, s}:
      read_req.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the request s starts with, and what follows it
def read_req(s: String) -> Wr.Dec<FAm.Req>:
  read_req.go(Wr.get_nat(s))

def spec.end(whole: Bool, q: FAm.Req) -> String:
  match whole:
    case True{}:
      spell_answer(q)
    case False{}:
      malformed()

def spec.run(r: Wr.Dec<FAm.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      spec.end(Wr.end(s), q)
    case Wr.Bad{}:
      malformed()

# the reply to s: the model's decision on the request s is exactly, else
# the error form
def spec(s: String) -> String:
  spec.run(read_req(s))

# LAW approvals_ffi_exact: on every input the entry answers the model's decision on the request the input is exactly (what a session does with a question, as the route decides for it; what the clients' answer makes of the step; the default auto set), and exactly the error form "approvals: malformed request" on any other input
# EXCLUDES: a session that waits with only the phone gateway, a question
#   relayed past clients that answer or with no parent, a gateway rule
#   that runs a guarded step, a denial read as a yes, another default auto
#   set, a default for malformed input, input left over ignored
law approvals_ffi_exact:
  for +s: String
  {FAm.ffi(s) == spec(s) : String}

# LAW approvals_ffi_answers: every request Rust writes (every number within the wire) gets the model's decision
# EXCLUDES: a request Rust writes refused or misread
law approvals_ffi_answers:
  for +q: FAm.Req
  for fits: {req_fits(q) == True{} : Bool}
  {FAm.ffi(spell_req(q, "")) == spell_answer(q) : String}

# LAW approvals_ffi_left_over: a request Rust writes followed by more input gets exactly the error form
# EXCLUDES: a second request or trailing bytes read past or ignored
law approvals_ffi_left_over:
  for +q: FAm.Req
  for +more: String
  for fits: {req_fits(q) == True{} : Bool}
  for some: {String.is_empty(more) == False{} : Bool}
  {FAm.ffi(spell_req(q, more)) == malformed() : String}

# LAW approvals_ffi_example: anchor: the strings Rust sends: a session with clients shows a write; one with no client relays it to its parent, or ends it unanswered at a root; the gateway alone runs a write and refuses a secret read; a denial and a yes of the clients; the default auto set; a session code 3 is refused
# EXCLUDES: another spelling of a request or a reply
law approvals_ffi_example:
  {FAm.ffi("0,2,1,1,F") == "0," : String} &
  {FAm.ffi("0,0,1,1,T") == "1," : String} &
  {FAm.ffi("0,0,1,1,F") == "2,2," : String} &
  {FAm.ffi("0,1,1,1,T") == "2,0," : String} &
  {FAm.ffi("0,1,2,0,6,F") == "2,3," : String} &
  {FAm.ffi("1,1,1,F") == "1," : String} &
  {FAm.ffi("1,1,1,T") == "0," : String} &
  {FAm.ffi("2,") == "6,0,1,2,3,4,5," : String} &
  {FAm.ffi("0,3,0,F") == malformed() : String}
