# eukhe: lemmas of LAW tree_replay_spec: the model's lookups, checks and
# exact changes are the spec's (spec/durable/tree.bend): get, has, ok,
# same, unset, sorted, rooted and sound on every list; set on a sorted one.

import Base
import ../../../bend/tree.bend as Tr
import ../../../spec/durable/tree.bend as TS
import ../base/tree/has.bend as LATreeHas

# Lookups
# -------

def ts.get_at(b: Bool, +e: Tr.Ent, +rest: List<&2, Tr.Ent>, +x: Nat, ih: {Tr.get(rest, x) == TS.get(rest, x) : Maybe<&2, Tr.Ent>}) -> {Tr.get.go(e <> rest, x, b) == TS.get.pick(b, e, TS.get(rest, x)) : Maybe<&2, Tr.Ent>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the model's lookup is the spec's, on every list
def ts.get(t: List<&2, Tr.Ent>, +x: Nat) -> {Tr.get(t, x) == TS.get(t, x) : Maybe<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +e <> +rest:
      match e:
        case Tr.Ent{+k, +p, +v}:
          ts.get_at(Nat.is_eq(k, x), Tr.Ent{k, p, v}, rest, x, ts.get(rest, x))

def ts.has(+t: List<&2, Tr.Ent>, +x: Nat) -> {Tr.has(t, x) == TS.has(t, x) : Bool}:
  %ts.get(t, x) : {Maybe.is_some(&2, Tr.Ent, Tr.get(t, x)) == Maybe.is_some(&2, Tr.Ent, _) : Bool}
  {==}

def ts.ok(+t: List<&2, Tr.Ent>, +k: Nat, +p: Nat) -> {Tr.ok(t, k, p) == TS.hangs(t, k, p) : Bool}:
  %ts.has(t, p) : {Tr.ok(t, k, p) == Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), _)) : Bool}
  {==}

def ts.same(m: Maybe<&2, Tr.Ent>, +e: Tr.Ent) -> {Tr.same(m, Some{e}) == TS.same(m, e) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      match x e:
        case Tr.Ent{a, b, c} Tr.Ent{d, f, g}:
          {==}

# Unset
# -----

def ts.unset_at(b: Bool, +e: Tr.Ent, +rest: List<&2, Tr.Ent>, +x: Nat, ih: {Tr.unset(rest, x) == TS.without(rest, x) : List<&2, Tr.Ent>}) -> {Tr.unset.go(e <> rest, x, b) == TS.keep.if(Bool.not(b), e, TS.without(rest, x)) : List<&2, Tr.Ent>}:
  match b:
    case True{}:
      ih
    case False{}:
      %ih : {e <> Tr.unset(rest, x) == e <> _ : List<&2, Tr.Ent>}
      {==}

# the model's unset is the spec's, on every list
def ts.unset(t: List<&2, Tr.Ent>, +x: Nat) -> {Tr.unset(t, x) == TS.without(t, x) : List<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +e <> +rest:
      match e:
        case Tr.Ent{+k, +p, +v}:
          ts.unset_at(Nat.is_eq(k, x), Tr.Ent{k, p, v}, rest, x, ts.unset(rest, x))

# Validity
# --------

def ts.above(+k: Nat, t: List<&2, Tr.Ent>) -> {Tr.above(k, t) == TS.first_above(k, t) : Bool}:
  match t:
    case Nil{}:
      {==}
    case h <> r:
      match h:
        case Tr.Ent{a, b, c}:
          {==}

# the model's order is the spec's, on every list
def ts.sorted(t: List<&2, Tr.Ent>) -> {Tr.sorted(t) == TS.ordered(t) : Bool}:
  match t:
    case Nil{}:
      {==}
    case +e <> +rest:
      match e:
        case Tr.Ent{+k, p, v}:
          %ts.above(k, rest) : {Bool.and(Tr.above(k, rest), Tr.sorted(rest)) == Bool.and(_, TS.ordered(rest)) : Bool}
          %ts.sorted(rest) : {Bool.and(Tr.above(k, rest), Tr.sorted(rest)) == Bool.and(Tr.above(k, rest), _) : Bool}
          {==}

def ts.rooted(s: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>) -> {Tr.rooted.go(s, all) == TS.hung(s, all) : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      match e:
        case Tr.Ent{+k, +p, v}:
          %ts.ok(all, k, p) : {Bool.and(Tr.ok(all, k, p), Tr.rooted.go(rest, all)) == Bool.and(_, TS.hung(rest, all)) : Bool}
          %ts.rooted(rest, all) : {Bool.and(Tr.ok(all, k, p), Tr.rooted.go(rest, all)) == Bool.and(Tr.ok(all, k, p), _) : Bool}
          {==}

# the model's validity is the spec's, on every list
def ts.sound(+t: List<&2, Tr.Ent>) -> {Tr.sound(t) == TS.valid(t) : Bool}:
  %ts.sorted(t) : {Tr.sound(t) == Bool.and(_, TS.hung(t, t)) : Bool}
  %ts.rooted(t, t) : {Tr.sound(t) == Bool.and(Tr.sorted(t), _) : Bool}
  {==}
