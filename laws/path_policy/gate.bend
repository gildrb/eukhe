# eukhe: the laws of area path_policy: the gate

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ./policy.bend as PathPolicy

# ---- path_policy gate ----

# LAWS (G1): the gate of the path policy: which access to
# a judged path runs unasked, and which only on the user's yes. Each law is
# an open claim about the model in bend/path_policy.bend; PROOF.bend proves
# them (as PathPolicyGate.<law>) with the lemmas of proof/path_policy/.

# (changed 2026-10-27 by the user: secrets never ask again) a secret
# access gates like any access: the auto set decides, the user's yes runs
# it regardless. The store laws that needed a yes for a secret
# (gate_write_auto_never_secret, gate_secret_read_needs_yes,
# secrets_need_yes, secrets_kept_without_yes) are gone with the gate they
# pinned.

# LAW gate_yes_runs: the user's yes runs any access
law gate_yes_runs:
  for c: Pp.Cls
  for a: Pp.Acc
  for +auto: List<&2, Nat>
  {Pp.runs(c, a, auto, Pp.Yes{}) == True{} : Bool}

# (G1) The gate, against the effects table
# ----------------------------------------
# The gate laws read the model's own effects and answer test: a model
# whose secret_read misses a plain read of a secret, and whose effects of
# that read lack the secret effect, lets it run with no yes and passes
# them (an adversary found this gap). gate_effs_exact pins the effects
# with the spec helpers here, which never call the model; the laws after
# it tie the gate's verdict to those effects over constructors and Base's
# own list membership (List.contains with Nat.is_eq), never the model's
# auto test (G1.6: an access runs without a question only when the auto
# set holds each of its effects). Effects: 0 read, 1 write, 4 outside, 5
# protected, 6 secret; an auto set may hold every effect (codes below 7),
# the secret one included (changed 2026-10-27 by the user: secrets never
# ask again).

# the class is Secret
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

# LAW gate_effs_exact: the effects of every access to a path of every class are exactly pp_effs
# EXCLUDES: a read of a secret without the secret effect, a write
#   outside the workspace or to a protected path without its effect, an
#   effect renumbered
law gate_effs_exact:
  for c: Pp.Cls
  for a: Pp.Acc
  {Pp.effs(c, a) == pp_effs(c, a) : List<&2, Nat>}

# LAW gate_unasked_only_granted: an access that runs without the user's yes (on a no, or with no
# answer) has each of its effects below 7 (a known effect code, the secret
# effect 6 included) and in the auto set, whatever the class, the access
# and the auto set
# EXCLUDES: an auto test that grants a code past 6, skips an effect,
#   ignores the auto set, or runs on a no or on no answer
law gate_unasked_only_granted:
  for c: Pp.Cls
  for a: Pp.Acc
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  for +xs: List<&2, Nat>
  for +e: Nat
  for +ys: List<&2, Nat>
  for no: {ans != Pp.Yes{} : Pp.Ans}
  for eff: {Pp.effs(c, a) == List.append(&2, Nat, xs, e <> ys) : List<&2, Nat>}
  for ran: {Pp.runs(c, a, auto, ans) == True{} : Bool}
  {Bool.and(Nat.is_lt(e, 7n), List.contains(~Nat, ~Nat.is_eq, auto, e)) == True{} : Bool}

# LAW gate_refusal_names_an_effect: an access that does not run on a no or with no answer has an
# effect that is not below 7 or not in the auto set (so, with
# gate_unasked_only_granted: without a yes, an access runs exactly when
# each of its effects is below 7 and in the auto set)
# EXCLUDES: a gate that asks for, or refuses, an access whose every effect
#   the auto set holds (a dropped or misread auto set, a refusal of every
#   access)
law gate_refusal_names_an_effect:
  for c: Pp.Cls
  for a: Pp.Acc
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  for no: {ans != Pp.Yes{} : Pp.Ans}
  for refused: {Pp.runs(c, a, auto, ans) == False{} : Bool}
  exs xs: List<&2, Nat>
  exs e: Nat
  exs ys: List<&2, Nat>
  {Pp.effs(c, a) == List.append(&2, Nat, xs, e <> ys) : List<&2, Nat>} & {Bool.and(Nat.is_lt(e, 7n), List.contains(~Nat, ~Nat.is_eq, auto, e)) == False{} : Bool}

# LAW gate_secret_read_example: anchor: the adversary's input: under the root /3 with the secret
# /3/5, a read of /3/5 with every effect but secret in the auto set and a
# no, a list of it with the auto set [read] and no answer, and a search of
# /3 (it holds the secret) do not run; a read of /3/7 runs unasked, a read
# of /3/5 with a yes runs
# EXCLUDES: a read of a secret that runs with no yes while the auto set
#   lacks the secret effect, a gate that never runs a plain read unasked
law gate_secret_read_example:
  {[Pp.runs(Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}, Tl.Name{5n}]), Pp.Rd{}, [0n, 1n, 2n, 3n, 4n, 5n], Pp.No{}), Pp.runs(Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}, Tl.Name{5n}]), Pp.Ls{}, [0n], Pp.Gone{}), Pp.runs(Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}]), Pp.Sr{True{}}, [0n], Pp.No{}), Pp.runs(Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}, Tl.Name{7n}]), Pp.Rd{}, [0n], Pp.No{}), Pp.runs(Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}, Tl.Name{5n}]), Pp.Rd{}, [0n], Pp.Yes{})] == [False{}, False{}, False{}, True{}, True{}] : List<&2, Bool>}

# (G1) The store, by the gate
# ---------------------------
# The store laws of policy.bend (secrets_kept_example) constrain only the
# cells at or under a secret entry: a store whose write asks the gate
# about secrets only, so that a
# write to a protected or outside path, or any write with an empty auto
# set, lands on the user's no or with no answer, passed every law (an
# adversary found this gap). The laws below tie one write to the gate's
# verdict on its real path (G1.6, G1.7: the gate judges the real path, the
# write occurs there), read through pp_cell (the content of the first
# cell at a location), and a history of writes to its writes one by one.

# LAW store_write_lands: a write the gate runs on the class of its path (judged on the real path)
# lands at its real path: the content there is the written value
# EXCLUDES: a write the gate runs that is dropped, lands at the written
#   path instead of the real one, or leaves an older cell first
law store_write_lands:
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +auto: List<&2, Nat>
  for +cs: List<&2, Pp.Cell>
  for +segs: List<&2, Tl.Seg>
  for +v: Nat
  for +ans: Pp.Ans
  for ran: {Pp.runs(Pp.class(pol, ls, segs), Pp.Wr{}, auto, ans) == True{} : Bool}
  {PathPolicy.pp_cell(Pp.run([Pp.Put{segs, v, ans}], pol, ls, auto, cs), Pp.Res.at(Pp.real(ls, segs))) == Some{v} : Maybe<&2, Nat>}

# LAW store_refused_write_keeps: a write the gate refuses on the class of its path leaves the
# store exactly as it was
# EXCLUDES: a refused write that lands anyway (on a protected or outside
#   path, or with an empty auto set, after a no or with no answer: the
#   store that asks the gate about secrets only)
law store_refused_write_keeps:
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +auto: List<&2, Nat>
  for +cs: List<&2, Pp.Cell>
  for +segs: List<&2, Tl.Seg>
  for +v: Nat
  for +ans: Pp.Ans
  for refused: {Pp.runs(Pp.class(pol, ls, segs), Pp.Wr{}, auto, ans) == False{} : Bool}
  {Pp.run([Pp.Put{segs, v, ans}], pol, ls, auto, cs) == cs : List<&2, Pp.Cell>}

# LAW store_write_only_its_path: a write, run or refused, leaves the content at every location
# but its real path as it was
# EXCLUDES: a write that also lands elsewhere (at the written path, a
#   neighbor, every cell)
law store_write_only_its_path:
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +auto: List<&2, Nat>
  for +cs: List<&2, Pp.Cell>
  for +segs: List<&2, Tl.Seg>
  for +v: Nat
  for +ans: Pp.Ans
  for +x: List<&2, Nat>
  for other: {x != Pp.Res.at(Pp.real(ls, segs)) : List<&2, Nat>}
  {PathPolicy.pp_cell(Pp.run([Pp.Put{segs, v, ans}], pol, ls, auto, cs), x) == PathPolicy.pp_cell(cs, x) : Maybe<&2, Nat>}

# LAW store_write_adds_at_most_one: a write adds at most one cell to the store
# EXCLUDES: a write that lands twice, or appends a cell for a location the
#   store already holds and more
law store_write_adds_at_most_one:
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +auto: List<&2, Nat>
  for +cs: List<&2, Pp.Cell>
  for +segs: List<&2, Tl.Seg>
  for +v: Nat
  for +ans: Pp.Ans
  {Nat.is_le(List.length(&2, Pp.Cell, Pp.run([Pp.Put{segs, v, ans}], pol, ls, auto, cs)), 1n+List.length(&2, Pp.Cell, cs)) == True{} : Bool}

# LAW store_run_in_pieces: writes run as two histories one after the other leave the store the
# whole history leaves (each write is judged and lands on its own, in order)
# EXCLUDES: a store that drops, reorders or merges the writes after the
#   first, or judges a write by the ones before it
law store_run_in_pieces:
  for es: List<&2, Pp.Put>
  for +fs: List<&2, Pp.Put>
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +auto: List<&2, Nat>
  for +cs: List<&2, Pp.Cell>
  {Pp.run(List.append(&2, Pp.Put, es, fs), pol, ls, auto, cs) == Pp.run(fs, pol, ls, auto, Pp.run(es, pol, ls, auto, cs)) : List<&2, Pp.Cell>}

# LAW store_run_example: anchor: the adversary's input: under the root /3, a write of 1 to /3/9
# (Protected by a Tree /3/9 rule) with the auto set [read, write] and a no
# leaves its 0; a write of 2 to the Inside /3/7 with an empty auto set and
# no answer leaves its 0, with [write] and a no it lands; a write of 5 to
# the Outside /4 lands as a new last cell with [write, outside], and not
# with [write] alone
# EXCLUDES: a store that asks the gate about secrets only
law store_run_example:
  {[Pp.run([Pp.Put{[Tl.Name{3n}, Tl.Name{9n}], 1n, Pp.No{}}], Pp.Pol{[[3n]], [Pp.Tree{[9n, 3n]}], Nil{}}, Nil{}, [0n, 1n], [Pp.Cell{[9n, 3n], 0n}]), Pp.run([Pp.Put{[Tl.Name{3n}, Tl.Name{7n}], 2n, Pp.Gone{}}], Pp.Pol{[[3n]], Nil{}, Nil{}}, Nil{}, Nil{}, [Pp.Cell{[7n, 3n], 0n}]), Pp.run([Pp.Put{[Tl.Name{3n}, Tl.Name{7n}], 2n, Pp.No{}}], Pp.Pol{[[3n]], Nil{}, Nil{}}, Nil{}, [1n], [Pp.Cell{[7n, 3n], 0n}]), Pp.run([Pp.Put{[Tl.Name{4n}], 5n, Pp.No{}}], Pp.Pol{[[3n]], Nil{}, Nil{}}, Nil{}, [1n, 4n], [Pp.Cell{[7n, 3n], 0n}]), Pp.run([Pp.Put{[Tl.Name{4n}], 5n, Pp.No{}}], Pp.Pol{[[3n]], Nil{}, Nil{}}, Nil{}, [1n], [Pp.Cell{[7n, 3n], 0n}])] == [[Pp.Cell{[9n, 3n], 0n}], [Pp.Cell{[7n, 3n], 0n}], [Pp.Cell{[7n, 3n], 2n}], [Pp.Cell{[7n, 3n], 0n}, Pp.Cell{[4n], 5n}], [Pp.Cell{[7n, 3n], 0n}]] : List<&2, List<&2, Pp.Cell>>}
