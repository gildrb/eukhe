# eukhe: the laws of area approvals

import Base
import ../bend/approvals.bend as Am

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
