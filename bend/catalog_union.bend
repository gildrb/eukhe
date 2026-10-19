# catalog_union: the model of the built-in model catalog
# (crates/eukhe-models/src/effective.rs `effective_catalog`, served by
# chain.rs `ModelCatalog::models`). The catalog has two sources: the
# bundled snapshot (models.bundled.json, pinned) and the compiled catalog
# (the pi-ai tables in eukhe-ai). The built-in catalog is their union.
#
# An entry has a key (the model's provider and id), an api, the data the
# bundle always states (route and data fields: baseUrl, name, reasoning,
# input, cost, contextWindow, maxTokens; one value here), and one optional
# field (thinkingLevelMap, compat, featured or headers: each follows the
# same rule, so one stands for all).
#
# The rule. The union has the bundled entries in bundled order, then the
# compiled entries whose key the bundle lacks, in compiled order. A
# bundled entry whose key the compiled catalog has keeps its api and data
# and the optional field it states; it takes the compiled optional field
# when it states none and both use the same api.
#
# A recursive scan takes the test of its first entry as a parameter (Bend
# matches only parameters); `*.at` computes that test.
#
# laws/catalog_union.bend states the laws; bend/proof_catalog_union.bend
# proves them; bend/bridge_catalog_union.bend runs this model against the
# Rust code.

import Base

# One entry of a source
type Ent is Data:
  Ent{key: Nat, api: Nat, data: Nat, opt: Maybe<&2, Nat>}

# Which source a catalog is
type Src is Data:
  Bundled{}
  Compiled{}

# A source and its entries, as read
type Cat is Data:
  Cat{src: Src, ents: List<&2, Ent>}

def Ent.key(e: Ent) -> Nat:
  match e:
    case Ent{k, a, d, o}:
      k

def Ent.api(e: Ent) -> Nat:
  match e:
    case Ent{k, a, d, o}:
      a

def Ent.data(e: Ent) -> Nat:
  match e:
    case Ent{k, a, d, o}:
      d

def Ent.opt(e: Ent) -> Maybe<&2, Nat>:
  match e:
    case Ent{k, a, d, o}:
      o

# Lookup
# ------

# the first entry of xs has key k
def key.at(+xs: List<&2, Ent>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case e <> rest:
      Nat.is_eq(Ent.key(e), k)

# the first entry with key k; hit is key.at(xs, k)
def find.go(xs: List<&2, Ent>, +k: Nat, hit: Bool) -> Maybe<&2, Ent>:
  match xs:
    case Nil{}:
      None{}
    case e <> +rest:
      match hit:
        case True{}:
          Some{e}
        case False{}:
          find.go(rest, k, key.at(rest, k))

def find(+xs: List<&2, Ent>, +k: Nat) -> Maybe<&2, Ent>:
  find.go(xs, k, key.at(xs, k))

def has(+xs: List<&2, Ent>, +k: Nat) -> Bool:
  Maybe.is_some(&2, Ent, find(xs, k))

# the number of entries with key k; hit is key.at(xs, k)
def count.go(xs: List<&2, Ent>, +k: Nat, hit: Bool) -> Nat:
  match xs:
    case Nil{}:
      0n
    case e <> +rest:
      match hit:
        case True{}:
          1n+count.go(rest, k, key.at(rest, k))
        case False{}:
          count.go(rest, k, key.at(rest, k))

def count(+xs: List<&2, Ent>, +k: Nat) -> Nat:
  count.go(xs, k, key.at(xs, k))

# A model in both sources
# ----------------------

# the optional field: the bundled one when it states one, else the
# compiled one when both use the same api (same), else none
def fill(o: Maybe<&2, Nat>, c: Maybe<&2, Nat>, same: Bool) -> Maybe<&2, Nat>:
  match o:
    case Some{v}:
      Some{v}
    case None{}:
      match same:
        case True{}:
          c
        case False{}:
          None{}

# bundled entry b with its compiled twin c
def merge(b: Ent, c: Ent) -> Ent:
  match b c:
    case Ent{bk, +ba, bd, bo} Ent{ck, +ca, cd, co}:
      Ent{bk, ba, bd, fill(bo, co, Nat.is_eq(ba, ca))}

# bundled entry b with its compiled twin, if any
def with(+b: Ent, m: Maybe<&2, Ent>) -> Ent:
  match m:
    case None{}:
      b
    case Some{c}:
      merge(b, c)

# The union
# ---------

# every bundled entry, with its compiled twin
def bundled(bs: List<&2, Ent>, +cs: List<&2, Ent>) -> List<&2, Ent>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> rest:
      with(b, find(cs, Ent.key(b))) <> bundled(rest, cs)

# the bundle has the key of the first entry of cs
def seen.at(+cs: List<&2, Ent>, +bs: List<&2, Ent>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> rest:
      has(bs, Ent.key(c))

# the compiled entries whose key the bundle lacks; seen is seen.at(cs, bs)
def extra.go(cs: List<&2, Ent>, +bs: List<&2, Ent>, seen: Bool) -> List<&2, Ent>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> +rest:
      match seen:
        case True{}:
          extra.go(rest, bs, seen.at(rest, bs))
        case False{}:
          c <> extra.go(rest, bs, seen.at(rest, bs))

def extra(+cs: List<&2, Ent>, +bs: List<&2, Ent>) -> List<&2, Ent>:
  extra.go(cs, bs, seen.at(cs, bs))

# the built-in catalog of the bundle bs and the compiled catalog cs
def union(+bs: List<&2, Ent>, +cs: List<&2, Ent>) -> List<&2, Ent>:
  List.append(&2, Ent, bundled(bs, cs), extra(cs, bs))

def Cat.ents(c: Cat) -> List<&2, Ent>:
  match c:
    case Cat{s, xs}:
      xs

# the built-in catalog when the first source read is s with entries xs
# and the second is b
def read.go(s: Src, +xs: List<&2, Ent>, +b: Cat) -> List<&2, Ent>:
  match s:
    case Bundled{}:
      union(xs, Cat.ents(b))
    case Compiled{}:
      union(Cat.ents(b), xs)

# the built-in catalog of two sources, in the order they were read
def read(a: Cat, +b: Cat) -> List<&2, Ent>:
  match a:
    case Cat{s, xs}:
      read.go(s, xs, b)
