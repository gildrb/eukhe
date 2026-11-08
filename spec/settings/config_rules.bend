# config (spec): independent restatements of the helpers of the config
# model (bend/config.bend) the laws of area config (laws/config.bend) read:
# lookups, membership, the leaf premises, slots, the trust filter and the
# named entries. Each says what the helper answers without calling it. A
# spec: the shipped code never calls it.

import Base
import ../../bend/config.bend as Cf

# Documents
# ---------

def cr_first(here: Bool, v: Nat, later: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match here:
    case True{}:
      Some{v}
    case False{}:
      later

# the value of the first entry of d whose key is j; none when no entry has it
def cr_lookup(d: List<&2, Cf.Entry>, +j: Nat) -> Maybe<&2, Nat>:
  match d:
    case Nil{}:
      None{}
    case e <> t:
      match e:
        case Cf.Entry{k, v}:
          cr_first(Nat.is_eq(k, j), v, cr_lookup(t, j))

# the value of key j in what a writer wrote; none when it refused
def cr_kept(w: Cf.Write, +j: Nat) -> Maybe<&2, Nat>:
  match w:
    case Cf.Refused{}:
      None{}
    case Cf.Wrote{d}:
      cr_lookup(d, j)

# the key an edit names
def cr_edit_key(e: Cf.Edit) -> Nat:
  match e:
    case Cf.Set{k, v}:
      k
    case Cf.Del{k}:
      k

# n is one of ns
def cr_listed(ns: List<&2, Nat>, +n: Nat) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(Nat.is_eq(x, n), cr_listed(t, n))

# Leaves
# ------

def cr_path(l: Cf.Leaf) -> Nat:
  match l:
    case Cf.Leaf{p, o}:
      p

# l is one of ls (a proof names which)
def cr_in(+l: Cf.Leaf, ls: List<&2, Cf.Leaf>) -> Type:
  match ls:
    case Nil{}:
      Empty
    case +x <> t:
      Or({l == x : Cf.Leaf}, cr_in(l, t))

# some leaf of ls has path n
def cr_path_in(ls: List<&2, Cf.Leaf>, +n: Nat) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case l <> t:
      Bool.or(Nat.is_eq(cr_path(l), n), cr_path_in(t, n))

# no two leaves of ls have one path
def cr_distinct(ls: List<&2, Cf.Leaf>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case +l <> +t:
      Bool.and(Bool.not(cr_path_in(t, cr_path(l))), cr_distinct(t))

# Limits
# ------

def cr_slot.pick(here: Bool, v: Cf.Val, later: Maybe<&2, Cf.Val>) -> Maybe<&2, Cf.Val>:
  match here:
    case True{}:
      Some{v}
    case False{}:
      later

# the value of the first slot of provider p
def cr_slot(es: List<&2, Cf.Slot>, +p: Nat) -> Maybe<&2, Cf.Val>:
  match es:
    case Nil{}:
      None{}
    case x <> t:
      match x:
        case Cf.Slot{q, v}:
          cr_slot.pick(Nat.is_eq(q, p), v, cr_slot(t, p))

def cr_bad(m: Maybe<&2, Cf.Val>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      match v:
        case Cf.Num{n}:
          False{}
        case Cf.Malformed{}:
          True{}

# provider p's limit is malformed as written: its first slot is malformed,
# or the value is not a map
def cr_malformed_at(s: Cf.InFlight, +p: Nat) -> Bool:
  match s:
    case Cf.Unset{}:
      False{}
    case Cf.Entries{es}:
      cr_bad(cr_slot(es, p))
    case Cf.NotMap{}:
      True{}

# Trust
# -----

def cr_pref(c: Cf.Class) -> Bool:
  match c:
    case Cf.Pref{}:
      True{}
    case Cf.Limit{}:
      False{}
    case Cf.Prompt{}:
      False{}
    case Cf.Credential{}:
      False{}
    case Cf.Code{}:
      False{}

# a trusted project keeps every item, an untrusted one its preferences
def cr_admits(t: Cf.Trust, c: Cf.Class) -> Bool:
  match t:
    case Cf.Trusted{}:
      True{}
    case Cf.Untrusted{}:
      cr_pref(c)

def cr_put(ok: Bool, k: Nat, v: Nat, rest: List<&2, Cf.Entry>) -> List<&2, Cf.Entry>:
  match ok:
    case True{}:
      Cf.Entry{k, v} <> rest
    case False{}:
      rest

# the items trust t keeps, in order, as entries, before g
def cr_effective(+t: Cf.Trust, g: List<&2, Cf.Entry>, items: List<&2, Cf.Item>) -> List<&2, Cf.Entry>:
  match items:
    case Nil{}:
      g
    case i <> rest:
      match i:
        case Cf.Item{k, c, v}:
          cr_put(cr_admits(t, c), k, v, cr_effective(t, g, rest))

# no item of items is a preference of key k
def cr_only_guarded(items: List<&2, Cf.Item>, +k: Nat) -> Bool:
  match items:
    case Nil{}:
      True{}
    case i <> rest:
      match i:
        case Cf.Item{j, c, v}:
          Bool.and(Bool.not(Bool.and(cr_pref(c), Nat.is_eq(j, k))), cr_only_guarded(rest, k))

# Named entries
# -------------

# some entry of es is named n
def cr_has(es: List<&2, Cf.Named>, +n: Nat) -> Bool:
  match es:
    case Nil{}:
      False{}
    case x <> t:
      match x:
        case Cf.Named{m, fs}:
          Bool.or(Nat.is_eq(m, n), cr_has(t, n))
