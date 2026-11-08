# eukhe: the laws of area path_policy: the gate

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ./policy.bend as PathPolicy

# ---- path_policy gate ----

# LAWS (G1): the gate of the path policy (docs/tools.md S7): which access to
# a judged path runs unasked, and which only on the user's yes. Each law is
# an open claim about the model in bend/path_policy.bend; PROOF.bend proves
# them (as PathPolicyGate.<law>) with the lemmas of proof/path_policy/.

# LAW gate_write_auto_never_secret (changed 2026-10-23 by the user: no prompts, like omp): a write
# without the user's yes never lands on a secret, whatever the auto set
# holds
law gate_write_auto_never_secret:
  for c: Pp.Cls
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  for ran: {Pp.runs(c, Pp.Wr{}, auto, ans) == True{} : Bool}
  for no: {Pp.Ans.yes(ans) == False{} : Bool}
  {Pp.Cls.secret(c) == False{} : Bool}

# LAW gate_secret_read_needs_yes: a read of a secret (a read or a list of one, a search of a
# directory that holds one) runs only on the user's yes, whatever the auto
# set holds
law gate_secret_read_needs_yes:
  for c: Pp.Cls
  for a: Pp.Acc
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  for s: {Pp.secret_read(c, a) == True{} : Bool}
  for ran: {Pp.runs(c, a, auto, ans) == True{} : Bool}
  {Pp.Ans.yes(ans) == True{} : Bool}

# LAW gate_yes_runs: the user's yes runs any access
law gate_yes_runs:
  for c: Pp.Cls
  for a: Pp.Acc
  for +auto: List<&2, Nat>
  {Pp.runs(c, a, auto, Pp.Yes{}) == True{} : Bool}

# (G1) The gate, against an independent spec
# ------------------------------------------
# gate_secret_read_needs_yes takes the model's own Pp.secret_read as its
# premise, and the gate laws read the model's own effects, auto test and
# answer (Pp.effs, Pp.runs, Pp.Ans.yes, Pp.Cls.secret): a model whose
# secret_read misses a plain read of a secret, and whose effects of that
# read lack the secret effect, lets it run with no yes and passes them all
# (an adversary found this gap). The laws below pin those terms whole with
# the spec helpers here, which never call the model. Effects (docs/tools.md
# S7 item 8): 0 read, 1 write, 4 outside, 5 protected, 6 secret; an effect
# below 6 may be in the auto set, secret never.

def pp_cls_secret(c: Pp.Cls) -> Bool:
  match c:
    case Pp.Inside{}:
      False{}
    case Pp.Outside{}:
      False{}
    case Pp.Protected{}:
      False{}
    case Pp.Secret{}:
      True{}

def pp_cls_guarded(c: Pp.Cls) -> Bool:
  match c:
    case Pp.Inside{}:
      False{}
    case Pp.Outside{}:
      False{}
    case Pp.Protected{}:
      True{}
    case Pp.Secret{}:
      True{}

# the user said yes (no, or no client answered: not yes)
def pp_yes(a: Pp.Ans) -> Bool:
  match a:
    case Pp.Yes{}:
      True{}
    case Pp.No{}:
      False{}
    case Pp.Gone{}:
      False{}

# the access reads a secret: a read or a list of a Secret path, a search
# of a Secret directory or of one that holds a secret; a write reads none
def pp_secret_read(c: Pp.Cls, a: Pp.Acc) -> Bool:
  match a:
    case Pp.Rd{}:
      pp_cls_secret(c)
    case Pp.Ls{}:
      pp_cls_secret(c)
    case Pp.Sr{h}:
      Bool.or(h, pp_cls_secret(c))
    case Pp.Wr{}:
      False{}

# a read's effects: read, and secret when it reads a secret
def pp_read_effs(sec: Bool) -> List<&2, Nat>:
  match sec:
    case True{}:
      [0n, 6n]
    case False{}:
      [0n]

# a write's effects: write, then outside, protected or secret by the class
def pp_write_effs(c: Pp.Cls) -> List<&2, Nat>:
  match c:
    case Pp.Inside{}:
      [1n]
    case Pp.Outside{}:
      [1n, 4n]
    case Pp.Protected{}:
      [1n, 5n]
    case Pp.Secret{}:
      [1n, 6n]

def pp_effs(c: Pp.Cls, a: Pp.Acc) -> List<&2, Nat>:
  match a:
    case Pp.Rd{}:
      pp_read_effs(pp_cls_secret(c))
    case Pp.Ls{}:
      pp_read_effs(pp_cls_secret(c))
    case Pp.Sr{h}:
      pp_read_effs(Bool.or(h, pp_cls_secret(c)))
    case Pp.Wr{}:
      pp_write_effs(c)

# every effect of es is below 6 and in the auto set
def pp_auto_holds(+auto: List<&2, Nat>, es: List<&2, Nat>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Bool.and(Nat.is_lt(e, 6n), PathPolicy.pp_has_name(auto, e)), pp_auto_holds(auto, rest))

# LAW gate_secret_read_exact: an access is a read of a secret exactly as pp_secret_read says, for
# every class and access
# EXCLUDES: a secret_read that misses a read, a list or a search of a
#   secret (gate_secret_read_needs_yes then says nothing of it)
law gate_secret_read_exact:
  for c: Pp.Cls
  for a: Pp.Acc
  {Pp.secret_read(c, a) == pp_secret_read(c, a) : Bool}

# LAW gate_effs_exact: the effects of every access to a path of every class are exactly pp_effs
# EXCLUDES: a read of a secret without the secret effect, a write
#   outside the workspace or to a protected path without its effect, an
#   effect renumbered
law gate_effs_exact:
  for c: Pp.Cls
  for a: Pp.Acc
  {Pp.effs(c, a) == pp_effs(c, a) : List<&2, Nat>}

# LAW gate_runs_exact: an access runs exactly when each of its pp_effs is below 6 and in the auto
# set, or the user said yes; whatever the class, the access, the auto set
# and the answer
# EXCLUDES: an auto test that grants the secret effect, ignores an effect or
#   the auto set, asks for an access the auto set allows, or runs on a no or
#   on no answer
law gate_runs_exact:
  for c: Pp.Cls
  for a: Pp.Acc
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  {Pp.runs(c, a, auto, ans) == Bool.or(pp_auto_holds(auto, pp_effs(c, a)), pp_yes(ans)) : Bool}

# LAW gate_terms_exact: the tests the gate and store laws state their claims with are the spec's:
# a class is secret or guarded, an answer is a yes, and a history of writes
# holds a yes exactly when pp_no_yes is false
# EXCLUDES: a vacuous gate_write_auto_never_secret (no class is secret),
#   path_ancestor_guarded (every class guarded), gate_secret_read_needs_yes
#   (every answer a yes) or secrets_need_yes (every history holds a yes)
law gate_terms_exact:
  for c: Pp.Cls
  for ans: Pp.Ans
  for es: List<&2, Pp.Put>
  {[Pp.Cls.secret(c), Pp.Cls.guarded(c), Pp.Ans.yes(ans), Pp.any_yes(es)] == [pp_cls_secret(c), pp_cls_guarded(c), pp_yes(ans), Bool.not(PathPolicy.pp_no_yes(es))] : List<&2, Bool>}

# LAW gate_secret_read_example: anchor: the adversary's input: under the root /3 with the secret
# /3/5, a read of /3/5 with every grantable effect in the auto set and a
# no, a list of it with the auto set [read] and no answer, and a search of
# /3 (it holds the secret) do not run; a read of /3/7 runs unasked, a read
# of /3/5 with a yes runs
# EXCLUDES: a read of a secret that runs with no yes, a gate that never
#   runs a plain read unasked
law gate_secret_read_example:
  {[Pp.runs(Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}, Tl.Name{5n}]), Pp.Rd{}, [0n, 1n, 2n, 3n, 4n, 5n], Pp.No{}), Pp.runs(Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}, Tl.Name{5n}]), Pp.Ls{}, [0n], Pp.Gone{}), Pp.runs(Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}]), Pp.Sr{True{}}, [0n], Pp.No{}), Pp.runs(Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}, Tl.Name{7n}]), Pp.Rd{}, [0n], Pp.No{}), Pp.runs(Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}, Tl.Name{5n}]), Pp.Rd{}, [0n], Pp.Yes{})] == [False{}, False{}, False{}, True{}, True{}] : List<&2, Bool>}

# (G1) The store, against an independent spec
# --------------------------------------------
# The store laws of policy.bend (secrets_need_yes, secrets_kept_without_yes,
# secrets_kept_example) constrain only the cells at or under a secret
# entry: a store whose write asks the gate about secrets only, so that a
# write to a protected or outside path, or any write with an empty auto
# set, lands on the user's no or with no answer, passed every law (an
# adversary found this gap). The law below pins the whole store after any
# writes with the spec helpers here and the spec resolution and class of
# policy.bend.

# v at the location at in place of the cell c when hit; else c, then later
def pp_set_pick(hit: Bool, +at: List<&2, Nat>, +v: Nat, c: Pp.Cell, rest: List<&2, Pp.Cell>, later: List<&2, Pp.Cell>) -> List<&2, Pp.Cell>:
  match hit:
    case True{}:
      Pp.Cell{at, v} <> rest
    case False{}:
      c <> later

# v written at the location at: the first cell there takes it, every other
# cell stays; with no cell there, a new cell at the end
def pp_set(cs: List<&2, Pp.Cell>, +at: List<&2, Nat>, +v: Nat) -> List<&2, Pp.Cell>:
  match cs:
    case Nil{}:
      [Pp.Cell{at, v}]
    case c <> +rest:
      match c:
        case Pp.Cell{+a, w}:
          pp_set_pick(PathPolicy.pp_same(a, at), at, v, Pp.Cell{a, w}, rest, pp_set(rest, at, v))

# v written at at when go, else cs as it was
def pp_land(go: Bool, cs: List<&2, Pp.Cell>, +at: List<&2, Nat>, +v: Nat) -> List<&2, Pp.Cell>:
  match go:
    case True{}:
      pp_set(cs, at, v)
    case False{}:
      cs

# a write of v to the real path r: it lands there when each effect of a
# write to r's spec class is below 6 and in the auto set, or the user said
# yes
def pp_step_at(r: Pp.Res, +ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +auto: List<&2, Nat>, cs: List<&2, Pp.Cell>, +v: Nat, ans: Pp.Ans) -> List<&2, Pp.Cell>:
  match r:
    case Pp.Res{+at, l}:
      pp_land(Bool.or(pp_auto_holds(auto, pp_write_effs(PathPolicy.pp_class(ro, ru, se, at, l))), pp_yes(ans)), cs, at, v)

# one write, judged on the spec real path of its segments
def pp_step(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>, cs: List<&2, Pp.Cell>, e: Pp.Put) -> List<&2, Pp.Cell>:
  match e:
    case Pp.Put{segs, v, ans}:
      pp_step_at(PathPolicy.pp_real(ls, segs), ro, ru, se, auto, cs, v, ans)

# the writes es, in order
def pp_run(es: List<&2, Pp.Put>, +ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>, cs: List<&2, Pp.Cell>) -> List<&2, Pp.Cell>:
  match es:
    case Nil{}:
      cs
    case e <> rest:
      pp_run(rest, ro, ru, se, ls, auto, pp_step(ro, ru, se, ls, auto, cs, e))

# LAW store_run_exact: any agent writes through any paths and links, under any policy, auto set
# and answers, leave the store pp_run says: each write is judged on its
# spec real path by its spec class, and lands there (the first cell there
# takes it, else a new cell at the end) exactly when each effect of a
# write to that class is below 6 and in the auto set, or the user said yes
# EXCLUDES: a write the gate refuses that lands anyway (on a protected or
#   outside path, or with an empty auto set, after a no or no answer), a
#   write the gate runs that is dropped, or lands elsewhere or twice
law store_run_exact:
  for es: List<&2, Pp.Put>
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +ls: List<&2, Pp.Link>
  for +auto: List<&2, Nat>
  for +cs: List<&2, Pp.Cell>
  {Pp.run(es, Pp.Pol{ro, ru, se}, ls, auto, cs) == pp_run(es, ro, ru, se, ls, auto, cs) : List<&2, Pp.Cell>}

# LAW store_run_example: anchor: the adversary's input: under the root /3, a write of 1 to /3/9
# (Protected by a Tree /3/9 rule) with the auto set [read, write] and a no
# leaves its 0; a write of 2 to the Inside /3/7 with an empty auto set and
# no answer leaves its 0, with [write] and a no it lands; a write of 5 to
# the Outside /4 lands as a new last cell with [write, outside], and not
# with [write] alone
# EXCLUDES: a store that asks the gate about secrets only
law store_run_example:
  {[Pp.run([Pp.Put{[Tl.Name{3n}, Tl.Name{9n}], 1n, Pp.No{}}], Pp.Pol{[[3n]], [Pp.Tree{[9n, 3n]}], Nil{}}, Nil{}, [0n, 1n], [Pp.Cell{[9n, 3n], 0n}]), Pp.run([Pp.Put{[Tl.Name{3n}, Tl.Name{7n}], 2n, Pp.Gone{}}], Pp.Pol{[[3n]], Nil{}, Nil{}}, Nil{}, Nil{}, [Pp.Cell{[7n, 3n], 0n}]), Pp.run([Pp.Put{[Tl.Name{3n}, Tl.Name{7n}], 2n, Pp.No{}}], Pp.Pol{[[3n]], Nil{}, Nil{}}, Nil{}, [1n], [Pp.Cell{[7n, 3n], 0n}]), Pp.run([Pp.Put{[Tl.Name{4n}], 5n, Pp.No{}}], Pp.Pol{[[3n]], Nil{}, Nil{}}, Nil{}, [1n, 4n], [Pp.Cell{[7n, 3n], 0n}]), Pp.run([Pp.Put{[Tl.Name{4n}], 5n, Pp.No{}}], Pp.Pol{[[3n]], Nil{}, Nil{}}, Nil{}, [1n], [Pp.Cell{[7n, 3n], 0n}])] == [[Pp.Cell{[9n, 3n], 0n}], [Pp.Cell{[7n, 3n], 0n}], [Pp.Cell{[7n, 3n], 2n}], [Pp.Cell{[7n, 3n], 0n}, Pp.Cell{[4n], 5n}], [Pp.Cell{[7n, 3n], 0n}]] : List<&2, List<&2, Pp.Cell>>}
