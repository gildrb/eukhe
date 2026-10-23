# eukhe: the laws of area tools

import Base
import ../bend/approvals.bend as Am
import ../bend/ffi_tools.bend as FTl
import ../bend/path_policy.bend as Pp
import ../bend/tools.bend as Tl
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S7) The tool surface
# ---------------------
# docs/tools.md S7, the model in bend/tools.bend. Every input is free:
# any tools that join and quit, any schemas, any paths, any scripts, any
# auto set, any answers of the user.

# LAW: no event changes the roster: tools that join go behind `dyn`
law roster_fixed:
  for es: List<&2, Tl.Ev>
  for +s: Tl.Sess
  {Tl.Sess.roster(Tl.run(es, s)) == Tl.Sess.roster(s) : List<&2, Nat>}

# LAW: every request of a session sends the roster it started with
law roster_sent_fixed:
  for es: List<&2, Tl.Ev>
  for +r: List<&2, Nat>
  for d: List<&2, Nat>
  {Tl.all_eq(Tl.Sess.sent(Tl.run(es, Tl.Sess{r, d, Nil{}})), r) == True{} : Bool}

# LAW: a tool that joins is reachable through `dyn`
law dyn_reaches_joined:
  for +s: Tl.Sess
  for +t: Nat
  {Tl.dyn_call(Tl.step(s, Tl.Join{t}), t) == True{} : Bool}

# LAW: a tool that quits is not reachable through `dyn`
law dyn_drops_quit:
  for +s: Tl.Sess
  for +t: Nat
  {Tl.dyn_call(Tl.step(s, Tl.Quit{t}), t) == False{} : Bool}

# LAW: every schema the harness sends has the intent parameter
law schema_has_intent:
  for s: Tl.Schema
  {Tl.elem(Tl.Schema.params(Tl.build(s)), Tl.intent()) == True{} : Bool}

# LAW: every schema the harness sends has a version of at least 1
law schema_versioned:
  for s: Tl.Schema
  {Nat.is_le(1n, Tl.Schema.version(Tl.build(s))) == True{} : Bool}

# LAW: the harness keeps every parameter a tool declares
law schema_keeps_params:
  for +s: Tl.Schema
  for +x: Nat
  for has: {Tl.elem(Tl.Schema.params(s), x) == True{} : Bool}
  {Tl.elem(Tl.Schema.params(Tl.build(s)), x) == True{} : Bool}

# LAW: building a built schema changes nothing
law schema_build_idempotent:
  for +s: Tl.Schema
  {Tl.build(Tl.build(s)) == Tl.build(s) : Tl.Schema}

# LAW: a path that goes above its root is rejected, never clamped
law path_rejects_escape:
  for +segs: List<&2, Tl.Seg>
  for out: {Tl.stays(segs, 0n) == False{} : Bool}
  {Tl.resolve(segs) == None{} : Maybe<&2, List<&2, Nat>>}

# LAW: a path that stays under its root resolves
law path_resolves_inside:
  for +segs: List<&2, Tl.Seg>
  for inside: {Tl.stays(segs, 0n) == True{} : Bool}
  {Maybe.is_some(&2, List<&2, Nat>, Tl.resolve(segs)) == True{} : Bool}

# LAW (compiled core) the path entry (bend/ffi_tools.bend) reads back
# the segments of a path as Rust writes it, and leaves what follows untouched
# EXCLUDES: a request field misread, dropped, reordered or shifted; a
#   decoder that eats the input after the request
law tools_ffi_request_round_trip:
  for +gs: List<&2, Tl.Seg>
  for +rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FTl.codes(gs))), LawsBase.wire_nats_fit(FTl.codes(gs))) == True{} : Bool}
  {FTl.get_req(FTl.put_req(gs, rest)) == Wr.Got{gs, rest} : Wr.Dec<List<&2, Tl.Seg>>}

# LAW (compiled core) the path entry answers a whole request with the
# model's resolution (the names, or none above the root)
# EXCLUDES: an entry that answers another rule, a default, or a reply for
#   a request it misread
law tools_ffi_answers:
  for +gs: List<&2, Tl.Seg>
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FTl.codes(gs))), LawsBase.wire_nats_fit(FTl.codes(gs))) == True{} : Bool}
  {FTl.ffi(FTl.put_req(gs, "")) == FTl.put_names(Tl.resolve(gs), "") : String}

# LAW (compiled core) the path entry answers a malformed request with
# the error form, never a default
# EXCLUDES: a decision made on input that is no request
law tools_ffi_rejects_malformed:
  for +s: String
  for bad: {FTl.get_req(s) == Wr.Bad{} : Wr.Dec<List<&2, Tl.Seg>>}
  {LawsBase.wire_opens_err(FTl.ffi(s)) == True{} : Bool}

# LAW (compiled core) and a request followed by more input with the error
# form
# EXCLUDES: an entry that ignores input left over (a second request, a
#   truncated one)
law tools_ffi_rejects_left_over:
  for +s: String
  for +q: List<&2, Tl.Seg>
  for +r: String
  for got: {FTl.get_req(s) == Wr.Got{q, r} : Wr.Dec<List<&2, Tl.Seg>>}
  for more: {String.is_empty(r) == False{} : Bool}
  {LawsBase.wire_opens_err(FTl.ffi(s)) == True{} : Bool}

# LAW: the steps that ran are the script's first steps, in order
law gate_prefix:
  for +ss: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for ans: List<&2, Bool>
  {Tl.prefix(Tl.Ran.steps(Tl.exec(ss, auto, ans)), ss) == True{} : Bool}

# LAW: no more gated steps run than the user approved
law gate_needs_yes:
  for +ss: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for +ans: List<&2, Bool>
  {Nat.is_le(Tl.gated(Tl.Ran.steps(Tl.exec(ss, auto, ans)), auto), Tl.yeses(ans)) == True{} : Bool}

# LAW: a denial stops the script at the denied step: the steps before it
# ran, it and every later step did not
law gate_deny_stops:
  for +pre: List<&2, Tl.Step>
  for +s: Tl.Step
  for +post: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for ans: List<&2, Bool>
  for free: {Tl.gated(pre, auto) == 0n : Nat}
  for held: {Tl.auto.at(auto, s) == False{} : Bool}
  {Tl.exec(List.append(&2, Tl.Step, pre, s <> post), auto, False{} <> ans) == Tl.Ran{pre, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}

# LAW: a script that finished ran every step
law gate_finish_runs_all:
  for +ss: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for +ans: List<&2, Bool>
  for fin: {Tl.End.finished(Tl.Ran.end(Tl.exec(ss, auto, ans))) == True{} : Bool}
  {Tl.Ran.steps(Tl.exec(ss, auto, ans)) == ss : List<&2, Tl.Step>}

# ---- path_policy ----

# LAWS (G1): the path policy. Each law is an open claim about the model
# in bend/path_policy.bend; PROOF.bend proves them (as Tools.<law>) with the
# lemmas of proof/path_policy/.

# (G1) Path policy
# ----------------
# docs/tools.md S7: one policy for the `bash` tool and the document
# tools (crates/eukhe-types/src/path_policy.rs). A path is a list of
# segments from `/`; the symlinks are free (any location, any target,
# from `/` or from the link's directory, loops included); the policy is
# free (any roots, protected rules and secret entries). An access is
# judged on the real path; its effects run unasked only when the auto
# set (`shell.autoEffects`, any value) allows each of them. The user's
# answer is free: yes, no, or none (no client answered).

# LAW: with writes in the auto set, a write Inside runs without a
# question
law gate_inside_write_runs:
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  for w: {Tl.elem(auto, 1n) == True{} : Bool}
  {Pp.runs(Pp.Inside{}, Pp.Wr{}, auto, ans) == True{} : Bool}

# ---- shell_classification ----

# shell_classification: the laws of section G2 (PROOF.bend proves them
# as Tools.<law>).

# (G2) Shell classification
# -------------------------
# docs/tools.md S7, the gate model of bend/tools.bend part 4. A step has a
# set of effects (codes: 0 read, 1 write, 2 exec, 3 net, 4 outside, 5
# protected, 6 secret): every effect of every part of it (its command,
# each redirection, each path it names; every command an external script
# holds). A part names a path that is or holds a secret, or not; only such
# a part gives the secret effect. Every input is free: any parts, any
# effects, any auto set (codes 4 to 6 in it too), any answers of the user.

# LAW: a step made of parts has every effect of every part
law step_holds_every_part:
  for +pre: List<&2, List<&2, Nat>>
  for +p: List<&2, Nat>
  for +post: List<&2, List<&2, Nat>>
  for +c: Nat
  for has: {Tl.elem(p, c) == True{} : Bool}
  {Tl.elem(Tl.join(List.append(&2, List<&2, Nat>, pre, p <> post)), c) == True{} : Bool}

# LAW: a step has the secret effect (6) only when one of its parts names
# a path that is or holds a secret (an operand, an option value, a
# redirection target, the working directory of a command that reads it
# because it names no path): a step whose parts name none has no secret
# effect, whatever else they hold
law secret_needs_a_secret_path:
  for +ps: List<&2, Tl.Part>
  for has: {Tl.elem(Tl.join(Tl.parts.effs(ps)), 6n) == True{} : Bool}
  {Tl.parts.secret(ps) == True{} : Bool}

# LAW: a part that names a path that is or holds a secret gives its step
# the secret effect (6)
law secret_path_gives_secret:
  for +pre: List<&2, Tl.Part>
  for +p: Tl.Part
  for +post: List<&2, Tl.Part>
  for named: {Tl.Part.secret(p) == True{} : Bool}
  {Tl.elem(Tl.join(Tl.parts.effs(List.append(&2, Tl.Part, pre, p <> post))), 6n) == True{} : Bool}

# LAW: a step with one effect that is not in the auto set, or that no auto
# set may hold, does not run without a question
law auto_needs_every_effect:
  for +s: Tl.Step
  for +auto: List<&2, Nat>
  for +c: Nat
  for has: {Tl.elem(Tl.Step.effs(s), c) == True{} : Bool}
  for out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}
  {Tl.auto.at(auto, s) == False{} : Bool}

# LAW: a write outside the workspace (4), a write to a protected place (5)
# and a read of a secret (6) never run without a question, whatever the
# auto set holds
law auto_never_sensitive:
  for +s: Tl.Step
  for +auto: List<&2, Nat>
  for +c: Nat
  for has: {Tl.elem(Tl.Step.effs(s), c) == True{} : Bool}
  for held: {Nat.is_le(4n, c) == True{} : Bool}
  {Tl.auto.at(auto, s) == False{} : Bool}

# LAW: a step made of parts runs without a question only when every effect
# of every part is within the auto set
law composed_needs_every_part:
  for +i: Nat
  for +pre: List<&2, List<&2, Nat>>
  for +p: List<&2, Nat>
  for +post: List<&2, List<&2, Nat>>
  for +auto: List<&2, Nat>
  for +c: Nat
  for has: {Tl.elem(p, c) == True{} : Bool}
  for out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}
  {Tl.auto.at(auto, Tl.Step{i, Tl.join(List.append(&2, List<&2, Nat>, pre, p <> post))}) == False{} : Bool}

# LAW: a step whose effects are within the auto set runs without a
# question: it uses no answer of the user
law auto_runs_within:
  for +s: Tl.Step
  for +post: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for ans: List<&2, Bool>
  for w: {Tl.within(Tl.Step.effs(s), auto) == True{} : Bool}
  {Tl.exec(s <> post, auto, ans) == Tl.ran.add(s, Tl.exec(post, auto, ans)) : Tl.Ran}

# LAW: a step whose effects are not within the auto set runs only with
# the user's yes: with no answer it does not run, and the script stops
law held_needs_a_yes:
  for +s: Tl.Step
  for +post: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for w: {Tl.within(Tl.Step.effs(s), auto) == False{} : Bool}
  {Tl.exec(s <> post, auto, Nil{}) == Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}

# (G5) A session that runs only from the phone gateway never waits
# -----------------------------------------------------------------
# The phone gateway shows no question. A step is guarded when it writes a
# protected path (effect 5: eukhe's own config and credentials, a .git or
# .eukhe dir, a PATH dir) or reads or writes a secret (effect 6).

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

# (G5) The default auto set; the never-auto effects
# --------------------------------------------------
# A step runs unasked when its effects are within the auto set
# (`shell.autoEffects`, bend/tools.bend `within`). The bridge test
# crates/eukhe-core/src/durable/shell/tests.rs
# `the_default_auto_set_is_its_model` reads the real auto set of a
# session with no settings and compares, with bridge/bridge_approvals.bend,
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
