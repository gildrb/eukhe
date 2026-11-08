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
