# laws/shell_classification: the laws of section G2 (imported by LAWS.bend
# as Sg; PROOF.bend proves them as Sg.<law>).

import Base
import ../bend/tools.bend as Tl

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
