# eukhe: the laws of area tree_commit

import Base
import ../bend/tree_commit.bend as Tc
import ../bend/ffi_tree_commit.bend as FTc
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# LAWS (R1): the order in which the state tree records one commit's
# changes (bend/tree_commit.bend, the port of eukhe-durable
# tree/state.rs `StateTree::apply_commit`). Each law is an open claim
# about Tc.order; PROOF.bend proves them (as TreeCommit.<law>) with the
# lemmas of proof/tree_commit/.
#
# The host gives the commit's changes in order, its keys interned to
# commit-local Nats: a Put whose parent is the root or a node of the tree
# now (Here), a Put whose parent is a key absent from the tree now
# (Under: its key and the parent's key), a Del (Gone). Keys are free:
# every law holds for every assignment of keys, repeated keys included.
#
# R1: the Puts go in rounds over the Puts still waiting, in commit order:
#     a Put applies when its parent is present: Here, or the key of a Put
#     applied before it (in the same round or an earlier one); a round
#     that applies nothing ends the rounds; every Put still waiting then
#     has an unknown parent, in commit order.
# R2: then every Del, in commit order.
# R3: every Put is answered once: applied or an unknown parent, never
#     lost, never twice.
# A Put that applies makes its key present (the host's assumption: the
# state tree's parents are conversations and tasks, never deleted, and a
# Put of a new key is never refused); whether a Del finds its node is the
# host's (the tree as it is when the Del comes).

# Terms
# -----

# change i of cs (none past the end: a Del)
def at(cs: List<&2, Tc.Ch>, i: Nat) -> Tc.Ch:
  match cs:
    case Nil{}:
      Tc.Gone{}
    case c <> t:
      match i:
        case 0n:
          c
        case 1n+j:
          at(t, j)

# the indices of the Puts of cs, the first at index i, in order
def put_indices(cs: List<&2, Tc.Ch>, +i: Nat) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      []
    case c <> t:
      match c:
        case Tc.Here{k}:
          i <> put_indices(t, 1n+i)
        case Tc.Under{k, u}:
          i <> put_indices(t, 1n+i)
        case Tc.Gone{}:
          put_indices(t, 1n+i)

# R2: the Dels of cs, the first at index i, in order
def dels_spec(cs: List<&2, Tc.Ch>, +i: Nat) -> List<&2, Tc.Res>:
  match cs:
    case Nil{}:
      []
    case c <> t:
      match c:
        case Tc.Here{k}:
          dels_spec(t, 1n+i)
        case Tc.Under{k, u}:
          dels_spec(t, 1n+i)
        case Tc.Gone{}:
          Tc.Retire{i} <> dels_spec(t, 1n+i)

def member(xs: List<&2, Nat>, +u: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(Nat.is_eq(x, u), member(t, u))

# the parent of change c is present, the keys ready being present
def parent_in(ready: List<&2, Nat>, c: Tc.Ch) -> Bool:
  match c:
    case Tc.Here{k}:
      True{}
    case Tc.Under{k, u}:
      member(ready, u)
    case Tc.Gone{}:
      False{}

def key_of(c: Tc.Ch) -> Nat:
  match c:
    case Tc.Here{k}:
      k
    case Tc.Under{k, u}:
      k
    case Tc.Gone{}:
      0n

def add_if(b: Bool, k: Nat, ready: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      k <> ready
    case False{}:
      ready

# a round: the Puts it applied and those still waiting (indices, in
# order), and the keys present after it
type Pass is Data:
  Pass{applied: List<&2, Nat>, waiting: List<&2, Nat>, ready: List<&2, Nat>}

def pass.cons(b: Bool, i: Nat, r: Pass) -> Pass:
  match b:
    case True{}:
      match r:
        case Pass{a, w, rd}:
          Pass{i <> a, w, rd}
    case False{}:
      match r:
        case Pass{a, w, rd}:
          Pass{a, i <> w, rd}

# R1: one round over the waiting Puts ps (indices into cs), in order
def pass(ps: List<&2, Nat>, +cs: List<&2, Tc.Ch>, +ready: List<&2, Nat>) -> Pass:
  match ps:
    case Nil{}:
      Pass{[], [], ready}
    case +i <> t:
      +c = at(cs, i)
      +b = parent_in(ready, c)
      pass.cons(b, i, pass(t, cs, add_if(b, key_of(c), ready)))

def applies(ps: List<&2, Nat>) -> List<&2, Tc.Res>:
  match ps:
    case Nil{}:
      []
    case i <> t:
      Tc.Apply{i} <> applies(t)

def unknowns(ps: List<&2, Nat>) -> List<&2, Tc.Res>:
  match ps:
    case Nil{}:
      []
    case i <> t:
      Tc.Orphan{i} <> unknowns(t)

def rounds.pick(a: List<&2, Nat>, w: List<&2, Nat>, rest: List<&2, Tc.Res>) -> List<&2, Tc.Res>:
  match a:
    case Nil{}:
      unknowns(w)
    case i <> t:
      List.append(&2, Tc.Res, applies(i <> t), rest)

def Pass.applied(r: Pass) -> List<&2, Nat>:
  match r:
    case Pass{a, w, rd}:
      a

def Pass.waiting(r: Pass) -> List<&2, Nat>:
  match r:
    case Pass{a, w, rd}:
      w

def Pass.ready(r: Pass) -> List<&2, Nat>:
  match r:
    case Pass{a, w, rd}:
      rd

# R1: at most f rounds over the waiting Puts ps, the keys ready present
def rounds_spec(f: Nat, +cs: List<&2, Tc.Ch>, ready: List<&2, Nat>, ps: List<&2, Nat>) -> List<&2, Tc.Res>:
  match f:
    case 0n:
      unknowns(ps)
    case 1n+g:
      +r = pass(ps, cs, ready)
      rounds.pick(Pass.applied(r), Pass.waiting(r), rounds_spec(g, cs, Pass.ready(r), Pass.waiting(r)))

# R1-R2: the results of cs: as many rounds as there are changes (each
# round but the last applies a Put), then the Dels
def order_spec(+cs: List<&2, Tc.Ch>) -> List<&2, Tc.Res>:
  List.append(&2, Tc.Res, rounds_spec(List.length(&2, Tc.Ch, cs), cs, [], put_indices(cs, 0n)), dels_spec(cs, 0n))

def answers.one(hit: Bool, n: Nat) -> Nat:
  match hit:
    case True{}:
      1n+n
    case False{}:
      n

# how many results answer the Put of change i (applied or unknown parent)
def answers(+i: Nat, rs: List<&2, Tc.Res>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case r <> t:
      match r:
        case Tc.Apply{j}:
          answers.one(Nat.is_eq(j, i), answers(i, t))
        case Tc.Orphan{j}:
          answers.one(Nat.is_eq(j, i), answers(i, t))
        case Tc.Retire{j}:
          answers(i, t)

# how many times i is in xs
def count(+i: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      answers.one(Nat.is_eq(x, i), count(i, t))

def justified.go(ok: Bool, rest: Bool) -> Bool:
  match ok:
    case True{}:
      rest
    case False{}:
      False{}

# R1: walking the results rs in order, the keys ready present: every
# applied Put's parent is present when it applies (Here, or the key of a
# Put applied before it), and its key is present after
def justified(rs: List<&2, Tc.Res>, +cs: List<&2, Tc.Ch>, +ready: List<&2, Nat>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      match r:
        case Tc.Apply{+i}:
          +c = at(cs, i)
          justified.go(parent_in(ready, c), justified(t, cs, key_of(c) <> ready))
        case Tc.Orphan{i}:
          justified(t, cs, ready)
        case Tc.Retire{i}:
          justified(t, cs, ready)

# R2: the results after the leading Puts' results
def after_puts(rs: List<&2, Tc.Res>) -> List<&2, Tc.Res>:
  match rs:
    case Nil{}:
      []
    case r <> t:
      match r:
        case Tc.Apply{i}:
          after_puts(t)
        case Tc.Orphan{i}:
          after_puts(t)
        case Tc.Retire{i}:
          Tc.Retire{i} <> t

# Laws
# ----

# LAW tree_commit_order_exact: the results of every commit come in the order of R1-R2: the Puts in rounds over the waiting ones in commit order, each applied as soon as its parent is present, the unknown parents after the last round that applies one, then the Dels
# EXCLUDES: a Put applied before its parent, a Put applied in a later
#   round than it can, the rounds walked in another order, an unknown
#   parent reported while another Put could still give it, Dels before
#   Puts or out of order, a result for another change
law tree_commit_order_exact:
  for +cs: List<&2, Tc.Ch>
  {Tc.order(cs) == order_spec(cs) : List<&2, Tc.Res>}

# LAW tree_commit_once: every Put is answered exactly once (applied or an unknown parent), and nothing else is
# EXCLUDES: a Put lost, a Put applied twice, a Put both applied and
#   reported, a Del answered as a Put
law tree_commit_once:
  for +cs: List<&2, Tc.Ch>
  for +i: Nat
  {answers(i, Tc.order(cs)) == count(i, put_indices(cs, 0n)) : Nat}

# LAW tree_commit_parent_first: every Put applies only once its parent is present: under the root or a node of the tree, or under the key of a Put applied before it in the commit
# EXCLUDES: a Put applied under a parent the tree does not have yet
law tree_commit_parent_first:
  for +cs: List<&2, Tc.Ch>
  {justified(Tc.order(cs), cs, []) == True{} : Bool}

# LAW tree_commit_dels_last: after the Puts' results come exactly the Dels, in commit order
# EXCLUDES: a Del before a Put (a document retired before its content
#   lands), a Del lost, repeated or reordered
law tree_commit_dels_last:
  for +cs: List<&2, Tc.Ch>
  {after_puts(Tc.order(cs)) == dels_spec(cs, 0n) : List<&2, Tc.Res>}

# LAW tree_commit_example: anchor: a commit whose entry comes before its conversation (the state tests' first commit), an unknown parent and a Del, a chain given children first, a Del before a Put
# EXCLUDES: a spec that is wrong on the shipped cases
law tree_commit_example:
  {Tc.order([Tc.Under{0n, 1n}, Tc.Here{1n}, Tc.Here{2n}]) == [Tc.Apply{1n}, Tc.Apply{2n}, Tc.Apply{0n}] : List<&2, Tc.Res>} &
  {Tc.order([Tc.Under{0n, 1n}, Tc.Gone{}]) == [Tc.Orphan{0n}, Tc.Retire{1n}] : List<&2, Tc.Res>} &
  {Tc.order([Tc.Under{0n, 1n}, Tc.Under{1n, 2n}, Tc.Here{2n}]) == [Tc.Apply{2n}, Tc.Apply{1n}, Tc.Apply{0n}] : List<&2, Tc.Res>} &
  {Tc.order([Tc.Gone{}, Tc.Here{0n}, Tc.Under{1n, 0n}]) == [Tc.Apply{1n}, Tc.Apply{2n}, Tc.Retire{0n}] : List<&2, Tc.Res>}

# LAWS (R4): the entry of the compiled Bend core (bend/ffi_tree_commit.bend,
# called by crates/eukhe-durable tree/state.rs through
# `eukhe_bend::rules::tree_commit`). Each law is an open claim about
# FTc.ffi, stated with spec spellers built only from the wire primitives
# of bend/wire.bend (their round trips: laws/wire.bend).
#
# R4: the request is the list of changes: tag 0 Here and its key, 1 Under,
#     its key and its parent's key, 2 a Del; the reply is the list of
#     results: tag 0 apply, 1 unknown parent, 2 the Del, each with its
#     change's index. Every input that is not exactly one request whose
#     count and keys fit the wire answers the error form "tree_commit:
#     malformed request"; never a default.

# Spec spellers
# -------------

def spell_ch(c: Tc.Ch, rest: String) -> String:
  match c:
    case Tc.Here{k}:
      Wr.put_nat(0n, Wr.put_nat(k, rest))
    case Tc.Under{k, u}:
      Wr.put_nat(1n, Wr.put_nat(k, Wr.put_nat(u, rest)))
    case Tc.Gone{}:
      Wr.put_nat(2n, rest)

def spell_chs(cs: List<&2, Tc.Ch>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      spell_ch(c, spell_chs(t, rest))

# the request: the count, then each change
def spell_req(+cs: List<&2, Tc.Ch>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Tc.Ch, cs), spell_chs(cs, rest))

def spell_res(r: Tc.Res, rest: String) -> String:
  match r:
    case Tc.Apply{i}:
      Wr.put_nat(0n, Wr.put_nat(i, rest))
    case Tc.Orphan{i}:
      Wr.put_nat(1n, Wr.put_nat(i, rest))
    case Tc.Retire{i}:
      Wr.put_nat(2n, Wr.put_nat(i, rest))

def spell_ress(rs: List<&2, Tc.Res>, rest: String) -> String:
  match rs:
    case Nil{}:
      rest
    case r <> t:
      spell_res(r, spell_ress(t, rest))

# the reply Rust reads: the spelled results of the model
def spell_reply(+rs: List<&2, Tc.Res>) -> String:
  Wr.put_nat(List.length(&2, Tc.Res, rs), spell_ress(rs, ""))

# every key of a change fits the wire
def ch_fits(c: Tc.Ch) -> Bool:
  match c:
    case Tc.Here{+k}:
      LawsBase.wire_fits(k)
    case Tc.Under{+k, +u}:
      Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(u))
    case Tc.Gone{}:
      True{}

def chs_fit(cs: List<&2, Tc.Ch>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> t:
      Bool.and(ch_fits(c), chs_fit(t))

# the request's count and every key fit the wire
def req_fits(+cs: List<&2, Tc.Ch>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Tc.Ch, cs)), chs_fit(cs))

# Laws
# ----

# LAW tree_commit_ffi_answers: a spelled request whose count and keys fit the wire answers the spelled results of the model
# EXCLUDES: a change misread (a tag off by one, the key and the parent
#   swapped), a result spelled with another tag, results lost or reordered
law tree_commit_ffi_answers:
  for +cs: List<&2, Tc.Ch>
  for h: {req_fits(cs) == True{} : Bool}
  {FTc.ffi(spell_req(cs, "")) == spell_reply(Tc.order(cs)) : String}

# LAW tree_commit_ffi_reads: the entry's decoder reads a spelled request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law tree_commit_ffi_reads:
  for +cs: List<&2, Tc.Ch>
  for +rest: String
  for h: {req_fits(cs) == True{} : Bool}
  {FTc.get_req(spell_req(cs, rest)) == Wr.Got{cs, rest} : Wr.Dec<List<&2, Tc.Ch>>}

# LAW tree_commit_ffi_exact: every input the entry does not answer with the error form is a spelled request that fits the wire
# EXCLUDES: an order made for input that is no request (an unknown tag, a
#   missing key, a Nat of 15 or more digits, input left over)
law tree_commit_ffi_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FTc.ffi(s)) == False{} : Bool}
  exs cs: List<&2, Tc.Ch>
  {s == spell_req(cs, "") : String} & {req_fits(cs) == True{} : Bool}

# LAW tree_commit_ffi_refuses: every error the entry answers is exactly "tree_commit: malformed request"
# EXCLUDES: an error text that varies with the input, a second error form
law tree_commit_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FTc.ffi(s)) == True{} : Bool}
  {FTc.ffi(s) == Wr.err("tree_commit: malformed request") : String}

# LAW tree_commit_ffi_example: anchor: the bytes Rust sends and reads: an entry before its conversation, an unknown parent and a Del, an empty commit, an unknown tag, input left over
# EXCLUDES: another spelling of a change or a result
law tree_commit_ffi_example:
  {[FTc.ffi("3,1,0,1,0,1,0,2,"), FTc.ffi("2,1,0,1,2,"), FTc.ffi("0,"), FTc.ffi("1,3,"), FTc.ffi("1,2,x")] == ["3,0,1,0,2,0,0,", "2,1,0,2,1,", "0,", Wr.err("tree_commit: malformed request"), Wr.err("tree_commit: malformed request")] : List<&2, String>}
