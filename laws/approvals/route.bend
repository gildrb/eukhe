# eukhe: the laws of area approvals, section route: where a question of
# the approval gate goes along a chain of sessions (bend/approvals.bend)

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../base.bend as LawsBase

# ---- approvals ----

# LAWS (G5): a child's question reaches its root's user, a session that
# runs only from the phone gateway never waits, and the default auto set
# runs every step. Each law is an open claim about
# the model in bend/approvals.bend; PROOF.bend proves them (as Approvals.<law>)
# with the lemmas of proof/approvals/.

# (G5) A child's question reaches its root's user
# ------------------------------------------------
# the model in bend/approvals.bend. A chain lists the
# sessions from the one that asks (a subagent, or a root) up to its root.
# The desks of a chain of sessions, as the compiled core runs them
# (laws/approvals/desk.bend, approvals_desk_is_route), route a question
# exactly as this model does.

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
# .eukhe dir, a PATH dir); the rule refuses it when the auto set does not
# already run it.

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

# LAW approvals_within_runs_unasked: a step whose effects are within the
# session's auto set runs unasked: no session of any chain is asked
# EXCLUDES: a gate that asks about (or routes) a step the auto set allows
law approvals_within_runs_unasked:
  for +auto: List<&2, Nat>
  for +es: List<&2, Nat>
  for +ds: List<&2, Am.Desk>
  for within: {Tl.within(es, auto) == True{} : Bool}
  {Am.gate(auto, es, ds) == Am.Unasked{} : Am.Gated}

# LAW approvals_outside_is_routed: a step whose effects are not all within
# the session's auto set is never unasked: its question goes its route
# EXCLUDES: a gate that runs unasked a step the session's auto set does
#   not allow (a fixed or remembered auto set, an auto set read for
#   another session)
law approvals_outside_is_routed:
  for +auto: List<&2, Nat>
  for +es: List<&2, Nat>
  for +ds: List<&2, Am.Desk>
  for outside: {Tl.within(es, auto) == False{} : Bool}
  {Am.gate(auto, es, ds) == Am.Routed{Am.route(ds), Am.fate(es, Am.Out.end(Am.route(ds)))} : Am.Gated}

# LAW nearest_rule_wins: when no session below has clients that answer,
# the first session whose only client is the phone gateway (or whose
# interactive clients leave it to the gateway) rules, and the end names
# that session
# EXCLUDES: a ruling credited to another session of the chain
law nearest_rule_wins:
  for +below: List<&2, Am.Desk>
  for quiet: {Am.quiet(below) == True{} : Bool}
  for +above: List<&2, Am.Desk>
  {Am.Out.end(Am.route(List.append(&2, Am.Desk, below, Am.Phone{} <> above))) == Am.Ruled{List.length(&2, Am.Desk, below)} : Am.End} & {Am.Out.end(Am.route(List.append(&2, Am.Desk, below, Am.PhoneLeft{} <> above))) == Am.Ruled{List.length(&2, Am.Desk, below)} : Am.End}
