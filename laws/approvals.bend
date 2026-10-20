# LAWS (G5): a child's question reaches its root's user, a session that
# runs only from the phone gateway never waits, and the default auto set
# runs every step but the never-auto ones. Each law is an open claim about
# the model in bend/approvals.bend; PROOF.bend proves them (as Ap.<law>)
# with the lemmas of bend/proof_approvals.bend.

import Base
import ../bend/tools.bend as Tl
import ../bend/approvals.bend as Am

# (G5) A child's question reaches its root's user
# ------------------------------------------------
# docs/tools.md G5, the model in bend/approvals.bend. A chain lists the
# sessions from the one that asks (a subagent, or a root) up to its root.
# The bridge test in crates/eukhe-daemon/src/shell_approval/bridge.rs
# runs the real approvals of a chain of sessions (clients attached or
# not, answering, denying or leaving, the phone gateway attached alone or
# beside them) on the scenarios of bend/bridge_approvals.bend, and both
# must print what the model prints.

# LAW: when no session below the root has clients that answer, a
# subagent's question reaches the root's clients, and their answer is the
# verdict
law child_answered_by_root:
  for +below: List<&2, Am.Desk>
  for quiet: {Am.quiet(below) == True{} : Bool}
  for +yes: Bool
  {Am.Out.end(Am.route(List.append(&2, Am.Desk, below, [Am.Says{yes}]))) == Am.Answered{List.length(&2, Am.Desk, below), yes} : Am.End}

# LAW: the first session up the chain whose clients answer gives the
# verdict, whatever the sessions above it
law nearest_answer_wins:
  for +below: List<&2, Am.Desk>
  for quiet: {Am.quiet(below) == True{} : Bool}
  for +yes: Bool
  for +above: List<&2, Am.Desk>
  {Am.Out.end(Am.route(List.append(&2, Am.Desk, below, Am.Says{yes} <> above))) == Am.Answered{List.length(&2, Am.Desk, below), yes} : Am.End}

# LAW: a question is unanswered (a denial) only when no session of the
# whole chain has clients that answer
law unanswered_only_when_quiet:
  for +ds: List<&2, Am.Desk>
  for none: {Am.Out.end(Am.route(ds)) == Am.Unanswered{} : Am.End}
  {Am.quiet(ds) == True{} : Bool}

# LAW: and then it is unanswered: no session invents an answer
law quiet_is_unanswered:
  for +ds: List<&2, Am.Desk>
  for quiet: {Am.quiet(ds) == True{} : Bool}
  {Am.Out.end(Am.route(ds)) == Am.Unanswered{} : Am.End}

# (G5) A session that runs only from the phone gateway never waits
# -----------------------------------------------------------------
# The phone gateway shows no question. A step is guarded when it writes a
# protected path (effect 5: eukhe's own config and credentials, a .git or
# .eukhe dir, a PATH dir) or reads or writes a secret (effect 6).

# LAW: a step of a session whose only clients are the phone gateway never
# waits: no client gets a frame, the question does not go up the chain,
# and the session's gateway rule answers at once
law gateway_never_waits:
  for +above: List<&2, Am.Desk>
  {Am.route(Am.Phone{} <> above) == Am.Out{Nil{}, Am.Ruled{0n}} : Am.Out}

# LAW: the gateway rule refuses a step that writes a protected path
law gateway_refuses_protected:
  for +es: List<&2, Nat>
  for protected: {Tl.elem(es, 5n) == True{} : Bool}
  for +above: List<&2, Am.Desk>
  {Am.fate(es, Am.Out.end(Am.route(Am.Phone{} <> above))) == Am.GatewayRefused{} : Am.Fate}

# LAW: the gateway rule refuses a step that reads or writes a secret
law gateway_refuses_secret:
  for +es: List<&2, Nat>
  for secret: {Tl.elem(es, 6n) == True{} : Bool}
  for +above: List<&2, Am.Desk>
  {Am.fate(es, Am.Out.end(Am.route(Am.Phone{} <> above))) == Am.GatewayRefused{} : Am.Fate}

# LAW: the gateway rule runs every other step unasked (a write, a run of
# a program, the network, a write outside the workspace)
law gateway_runs_the_rest:
  for +es: List<&2, Nat>
  for not_protected: {Tl.elem(es, 5n) == False{} : Bool}
  for not_secret: {Tl.elem(es, 6n) == False{} : Bool}
  for +above: List<&2, Am.Desk>
  {Am.fate(es, Am.Out.end(Am.route(Am.Phone{} <> above))) == Am.Runs{} : Am.Fate}

# LAW: a question the interactive clients leave unanswered while the
# phone gateway stays falls to the gateway rule, not up the chain
law left_to_the_gateway:
  for +above: List<&2, Am.Desk>
  {Am.route(Am.PhoneLeft{} <> above) == Am.Out{[0n], Am.Ruled{0n}} : Am.Out}

# LAW: a subagent's question that reaches a session whose only clients
# are the phone gateway (no session below it has clients that answer)
# fares as that session's own step: the same rule answers it
law gateway_rules_a_subagent:
  for +below: List<&2, Am.Desk>
  for quiet: {Am.quiet(below) == True{} : Bool}
  for +es: List<&2, Nat>
  for +above: List<&2, Am.Desk>
  {Am.fate(es, Am.Out.end(Am.route(List.append(&2, Am.Desk, below, Am.Phone{} <> above)))) == Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))) : Am.Fate}

# (G5) The default auto set; the never-auto effects
# --------------------------------------------------
# A step runs unasked when its effects are within the auto set
# (`shell.autoEffects`, bend/tools.bend `within`). The bridge test
# crates/eukhe-core/src/durable/shell/tests.rs
# `the_default_auto_set_is_its_model` reads the real auto set of a
# session with no settings and compares, with bend/bridge_approvals.bend,
# the effects it holds and `gate` on every step of one to seven effects.

# LAW: the auto set of a session whose user sets none holds exactly the
# grantable effects: read, write, exec and net
law default_auto_is_grantable:
  for +c: Nat
  {Tl.elem(Am.default_auto(), c) == Tl.grantable(c) : Bool}

# LAW: a step with an effect that no auto set may hold (4: a write
# outside the workspace, 5: a protected write, 6: a secret) never runs
# unasked through the auto set, in any session: its question goes its
# route
law never_auto_is_routed:
  for +auto: List<&2, Nat>
  for +es: List<&2, Nat>
  for +c: Nat
  for has: {Tl.elem(es, c) == True{} : Bool}
  for held: {Nat.is_le(4n, c) == True{} : Bool}
  for +ds: List<&2, Am.Desk>
  {Am.gate(auto, es, ds) == Am.routed(es, Am.route(ds)) : Am.Gated}

# LAW: so in a session whose client answers (the TUI, the dashboard), such
# a step asks that client, and its answer decides
law never_auto_asks_the_client:
  for +auto: List<&2, Nat>
  for +es: List<&2, Nat>
  for +c: Nat
  for has: {Tl.elem(es, c) == True{} : Bool}
  for held: {Nat.is_le(4n, c) == True{} : Bool}
  for +yes: Bool
  for +above: List<&2, Am.Desk>
  {Am.gate(auto, es, Am.Says{yes} <> above) == Am.Routed{Am.Out{[0n], Am.Answered{0n, yes}}, Am.yes.fate(yes)} : Am.Gated}

# LAW: in a session whose only clients are the phone gateway, a write
# outside the workspace that is not protected and touches no secret runs,
# and only by the gateway rule, never through the auto set
law outside_runs_only_by_the_gateway:
  for +auto: List<&2, Nat>
  for +es: List<&2, Nat>
  for outside: {Tl.elem(es, 4n) == True{} : Bool}
  for not_protected: {Tl.elem(es, 5n) == False{} : Bool}
  for not_secret: {Tl.elem(es, 6n) == False{} : Bool}
  for +above: List<&2, Am.Desk>
  {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.Runs{}} : Am.Gated}

# LAW: and there a protected write or a secret is refused at once,
# whatever the auto set
law guarded_refused_from_the_phone:
  for +auto: List<&2, Nat>
  for +es: List<&2, Nat>
  for guarded: {Bool.or(Tl.elem(es, 5n), Tl.elem(es, 6n)) == True{} : Bool}
  for +above: List<&2, Am.Desk>
  {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.GatewayRefused{}} : Am.Gated}
