# catalog_union: the model of the built-in model catalog
# (crates/eukhe-models/src/effective.rs `effective_catalog`, served by
# chain.rs `ModelCatalog::models`). The catalog has two sources: the
# bundled snapshot (models.bundled.json, pinned) and the compiled catalog
# (the pi-ai tables in eukhe-ai). The built-in catalog is their union.
#
# An entry has a key (the model's provider and id), an api, the data the
# bundle always states (route and data fields: baseUrl, name, reasoning,
# input, cost, contextWindow, maxTokens; one value here), and the four
# optional fields (thinkingLevelMap, compat, featured, headers), each
# none or a value.
#
# The rule. The union has the bundled entries in bundled order, then the
# compiled entries whose key the bundle lacks, in compiled order. A
# bundled entry whose key the compiled catalog has keeps its api and data
# and each optional field it states; it takes each compiled optional
# field it states none of when both use the same api.
#
# A recursive scan takes the test of its first entry as a parameter (Bend
# matches only parameters); `*.at` computes that test.
#
# `union` is the rule as the laws read it (a scan per entry); `fast` is
# the same list by tables keyed by the entries' keys (a binary trie of
# native steps), O(n log n): the law union_fast pins it to `union`.
#
# laws/catalog_union.bend states the laws; proof/catalog_union/
# proves them; bend/ffi_catalog_union.bend is the entry the Rust code
# calls (crates/eukhe-models/src/effective.rs).

import Base

# One entry of a source
type Ent is Data:
  Ent{key: Nat, api: Nat, data: Nat, tlm: Maybe<&2, Nat>, compat: Maybe<&2, Nat>, featured: Maybe<&2, Nat>, headers: Maybe<&2, Nat>}

# An optional field
type Fld is Data:
  Tlm{}
  Compat{}
  Featured{}
  Headers{}

# Which source a catalog is
type Src is Data:
  Bundled{}
  Compiled{}

# A source and its entries, as read
type Cat is Data:
  Cat{src: Src, ents: List<&2, Ent>}

def Ent.key(e: Ent) -> Nat:
  match e:
    case Ent{k, a, d, t, c, f, h}:
      k

def Ent.api(e: Ent) -> Nat:
  match e:
    case Ent{k, a, d, t, c, f, h}:
      a

def Ent.data(e: Ent) -> Nat:
  match e:
    case Ent{k, a, d, t, c, f, h}:
      d

# the optional field f of e
def Ent.opt(e: Ent, f: Fld) -> Maybe<&2, Nat>:
  match e:
    case Ent{k, a, d, t, c, ft, h}:
      match f:
        case Tlm{}:
          t
        case Compat{}:
          c
        case Featured{}:
          ft
        case Headers{}:
          h

# An entry as one optional field shows it: key, api, data and the field
type Slot is Data:
  Slot{key: Nat, api: Nat, data: Nat, opt: Maybe<&2, Nat>}

def Ent.slot(+e: Ent, f: Fld) -> Slot:
  Slot{Ent.key(e), Ent.api(e), Ent.data(e), Ent.opt(e, f)}

def slot(m: Maybe<&2, Ent>, f: Fld) -> Maybe<&2, Slot>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Some{Ent.slot(e, f)}

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

# an optional field: the bundled one when it states one, else the
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
    case Ent{bk, +ba, bd, bt, bc, bf, bh} Ent{ck, +ca, cd, ct, cc, cf, ch}:
      +same = Nat.is_eq(ba, ca)
      Ent{bk, ba, bd, fill(bt, ct, same), fill(bc, cc, same), fill(bf, cf, same), fill(bh, ch, same)}

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

# The fast union
# --------------
# A table holds at most one entry per key in a binary trie: the root
# holds key 0; key k > 0 lives under the left child (k - 1 even) or the
# right child (k - 1 odd) at key (k - 1) / 2. Each step is native
# arithmetic, so a lookup takes about log2(k) steps. A put takes a fuel
# above the key (a step at least halves it).

type Tab is Data:
  TNil{}
  TNode{v: Maybe<&2, Ent>, l: Tab, r: Tab}

# k is the root's key
def key.z(k: Nat) -> Bool:
  Nat.is_eq(k, 0n)

# key k > 0 goes right
def key.odd(k: Nat) -> Bool:
  Nat.is_eq(Nat.mod(Nat.sub(k, 1n), 2n), 1n)

# the key of k > 0 in its child
def key.half(k: Nat) -> Nat:
  Nat.div(Nat.sub(k, 1n), 2n)

# the entry at key k; z is key.z(k), odd is key.odd(k)
def look(t: Tab, +k: Nat, z: Bool, odd: Bool) -> Maybe<&2, Ent>:
  match t:
    case TNil{}:
      None{}
    case TNode{v, l, r}:
      match z:
        case True{}:
          v
        case False{}:
          match odd:
            case True{}:
              +h = key.half(k)
              look(r, h, key.z(h), key.odd(h))
            case False{}:
              +h = key.half(k)
              look(l, h, key.z(h), key.odd(h))

def find.t(t: Tab, +k: Nat) -> Maybe<&2, Ent>:
  look(t, k, key.z(k), key.odd(k))

# the slot keeps its entry: the first put at a key wins
def keep(v: Maybe<&2, Ent>, e: Ent) -> Maybe<&2, Ent>:
  match v:
    case None{}:
      Some{e}
    case Some{x}:
      Some{x}

# t with e at key k unless k holds one; z is key.z(k), odd is key.odd(k)
def put(fuel: Nat, t: Tab, +k: Nat, z: Bool, odd: Bool, e: Ent) -> Tab:
  match fuel:
    case 0n:
      t
    case 1n+f:
      match t:
        case TNil{}:
          match z:
            case True{}:
              TNode{Some{e}, TNil{}, TNil{}}
            case False{}:
              match odd:
                case True{}:
                  +h = key.half(k)
                  TNode{None{}, TNil{}, put(f, TNil{}, h, key.z(h), key.odd(h), e)}
                case False{}:
                  +h = key.half(k)
                  TNode{None{}, put(f, TNil{}, h, key.z(h), key.odd(h), e), TNil{}}
        case TNode{v, l, r}:
          match z:
            case True{}:
              TNode{keep(v, e), l, r}
            case False{}:
              match odd:
                case True{}:
                  +h = key.half(k)
                  TNode{v, l, put(f, r, h, key.z(h), key.odd(h), e)}
                case False{}:
                  +h = key.half(k)
                  TNode{v, put(f, l, h, key.z(h), key.odd(h), e), r}

# the table of xs after t: each key's first entry
def tab(xs: List<&2, Ent>, t: Tab) -> Tab:
  match xs:
    case Nil{}:
      t
    case +e <> rest:
      +k = Ent.key(e)
      tab(rest, put(1n+k, t, k, key.z(k), key.odd(k), e))

# every bundled entry, with its compiled twin from the table ct
def bundled.t(bs: List<&2, Ent>, +ct: Tab) -> List<&2, Ent>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> rest:
      with(b, find.t(ct, Ent.key(b))) <> bundled.t(rest, ct)

# the table bt has the key of the first entry of cs
def seen.t(+cs: List<&2, Ent>, +bt: Tab) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> rest:
      Maybe.is_some(&2, Ent, find.t(bt, Ent.key(c)))

# the compiled entries whose key the table bt lacks; seen is seen.t(cs, bt)
def extra.t(cs: List<&2, Ent>, +bt: Tab, seen: Bool) -> List<&2, Ent>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> +rest:
      match seen:
        case True{}:
          extra.t(rest, bt, seen.t(rest, bt))
        case False{}:
          c <> extra.t(rest, bt, seen.t(rest, bt))

# the built-in catalog of bs and cs, by tables: union(bs, cs)
def fast(+bs: List<&2, Ent>, +cs: List<&2, Ent>) -> List<&2, Ent>:
  +bt = tab(bs, TNil{})
  List.append(&2, Ent, bundled.t(bs, tab(cs, TNil{})), extra.t(cs, bt, seen.t(cs, bt)))
