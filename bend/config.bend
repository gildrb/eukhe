# config: what eukhe does with its config documents (settings.json,
# mcp-connections.json, auth.json) and with the layers over them. The
# Rust code is crates/eukhe-core/src/settings/ (`persist.rs`, `load.rs`,
# `manager.rs`, `trust.rs`, `merge.rs`), mcp/connection_store.rs,
# auth/storage.rs and admission.rs; the laws are laws/config.bend.
#
# A document is a list of entries: a key and a value, both numbers (a
# key stands for a key path, a value for the JSON at it).

import Base

type Entry is Data:
  Entry{k: Nat, v: Nat}

# Lists
# -----

def pick(b: Bool, v: Nat, later: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      later

# the value of the first entry of d with key j
def lookup(d: List<&2, Entry>, +j: Nat) -> Maybe<&2, Nat>:
  match d:
    case Nil{}:
      None{}
    case e <> rest:
      match e:
        case Entry{k, v}:
          pick(Nat.is_eq(k, j), v, lookup(rest, j))

# n is in ns
def listed(ns: List<&2, Nat>, +n: Nat) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(Nat.is_eq(x, n), listed(rest, n))

# Read, modify, write
# -------------------
# A writer reads the document on disk under its lock. The read ends one
# of three ways: no file (`Missing`), a document (`Parsed`), or a file it
# cannot read or parse, or a version it does not know (`Broken`). The
# change is one edit of one key.

type Read is Data:
  Missing{}
  Parsed{d: List<&2, Entry>}
  Broken{}

type Edit is Data:
  Set{k: Nat, v: Nat}
  Del{k: Nat}

type Write is Data:
  Refused{}
  Wrote{d: List<&2, Entry>}

def keep(b: Bool, e: Entry, rest: List<&2, Entry>) -> List<&2, Entry>:
  match b:
    case True{}:
      rest
    case False{}:
      e <> rest

# d without the entries of key k
def del(d: List<&2, Entry>, +k: Nat) -> List<&2, Entry>:
  match d:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Entry{+j, v}:
          keep(Nat.is_eq(j, k), Entry{j, v}, del(rest, k))

# d with key k set to v
def set(d: List<&2, Entry>, +k: Nat, v: Nat) -> List<&2, Entry>:
  Entry{k, v} <> del(d, k)

def apply(d: List<&2, Entry>, e: Edit) -> List<&2, Entry>:
  match e:
    case Set{k, v}:
      set(d, k, v)
    case Del{k}:
      del(d, k)

# the edit e changes key j
def touches(e: Edit, +j: Nat) -> Bool:
  match e:
    case Set{k, v}:
      Nat.is_eq(k, j)
    case Del{k}:
      Nat.is_eq(k, j)

# the writer: it writes only over a document it read
def rmw(r: Read, e: Edit) -> Write:
  match r:
    case Missing{}:
      Wrote{apply(Nil{}, e)}
    case Parsed{d}:
      Wrote{apply(d, e)}
    case Broken{}:
      Refused{}

# the value of key j in what was written; none when nothing was
def kept(w: Write, +j: Nat) -> Maybe<&2, Nat>:
  match w:
    case Refused{}:
      None{}
    case Wrote{d}:
      lookup(d, j)

# A settings setter: it writes the document on disk at write time, never
# the copy it loaded (`loaded`, which may lack a key that failed to load
# or a key another writer added since).
def save(loaded: List<&2, Entry>, disk: Read, +k: Nat, v: Nat) -> Write:
  rmw(disk, Set{k, v})

# Leaves of a settings document
# -----------------------------
# The load of one settings document: each leaf (a value that is not an
# object, or the whole value of a cvar) has a path and an outcome. A good
# leaf applies (it becomes its cvar's set); a value its type does not
# admit, or a key no setting declares, is named by a diagnostic.

type Outcome is Data:
  Good{}
  BadType{}
  Undeclared{}

type Leaf is Data:
  Leaf{path: Nat, o: Outcome}

def Leaf.path(l: Leaf) -> Nat:
  match l:
    case Leaf{p, o}:
      p

# l is in ls
def In(+l: Leaf, ls: List<&2, Leaf>) -> Type:
  match ls:
    case Nil{}:
      Empty
    case +x <> rest:
      Or({l == x : Leaf}, In(l, rest))

# the paths of the leaves that apply
def applied(ls: List<&2, Leaf>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      match l:
        case Leaf{p, o}:
          match o:
            case Good{}:
              p <> applied(rest)
            case BadType{}:
              applied(rest)
            case Undeclared{}:
              applied(rest)

# the paths the diagnostics name
def reported(ls: List<&2, Leaf>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      match l:
        case Leaf{p, o}:
          match o:
            case Good{}:
              reported(rest)
            case BadType{}:
              p <> reported(rest)
            case Undeclared{}:
              p <> reported(rest)

# the paths of the leaves
def paths(ls: List<&2, Leaf>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      Leaf.path(l) <> paths(rest)

# no two leaves share a path
def distinct(ls: List<&2, Leaf>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case +l <> +rest:
      Bool.and(Bool.not(listed(paths(rest), Leaf.path(l))), distinct(rest))

# Admission limits
# ----------------
# `providerMaxInFlight` as written: unset, a map of provider entries, or
# a value that is not a map. An entry is a whole number (`0`: no limit)
# or something else (malformed).

type Val is Data:
  Num{n: Nat}
  Malformed{}

type Slot is Data:
  Slot{p: Nat, v: Val}

type InFlight is Data:
  Unset{}
  Entries{es: List<&2, Slot>}
  NotMap{}

type Lim is Data:
  Unlimited{}
  Cap{n: Nat}

# the limit an entry gives: a malformed one caps at 1
def val_limit(v: Val) -> Lim:
  match v:
    case Num{n}:
      match n:
        case 0n:
          Unlimited{}
        case 1n+q:
          Cap{1n+q}
    case Malformed{}:
      Cap{1n}

def slot.pick(b: Bool, v: Val, later: Maybe<&2, Val>) -> Maybe<&2, Val>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      later

# the entry of provider p
def slot(es: List<&2, Slot>, +p: Nat) -> Maybe<&2, Val>:
  match es:
    case Nil{}:
      None{}
    case s <> rest:
      match s:
        case Slot{q, v}:
          slot.pick(Nat.is_eq(q, p), v, slot(rest, p))

def slot_limit(m: Maybe<&2, Val>) -> Lim:
  match m:
    case None{}:
      Unlimited{}
    case Some{v}:
      val_limit(v)

# the in-flight limit of provider p
def limit(s: InFlight, +p: Nat) -> Lim:
  match s:
    case Unset{}:
      Unlimited{}
    case Entries{es}:
      slot_limit(slot(es, p))
    case NotMap{}:
      Cap{1n}

def malformed_val(m: Maybe<&2, Val>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      match v:
        case Num{n}:
          False{}
        case Malformed{}:
          True{}

# the limit of provider p is malformed as written
def malformed_at(s: InFlight, +p: Nat) -> Bool:
  match s:
    case Unset{}:
      False{}
    case Entries{es}:
      malformed_val(slot(es, p))
    case NotMap{}:
      True{}

# Project trust
# -------------
# A project document's items: a key, what the key is, and a value. An
# untrusted project applies only its preferences; a limit, a system
# prompt file and a credential (or what routes one) are withheld.

type Class is Data:
  Pref{}
  Limit{}
  Prompt{}
  Credential{}

type Item is Data:
  Item{k: Nat, kind: Class, v: Nat}

type Trust is Data:
  Trusted{}
  Untrusted{}

def guard(b: Bool, e: Entry, rest: List<&2, Entry>) -> List<&2, Entry>:
  match b:
    case True{}:
      e <> rest
    case False{}:
      rest

def admits(t: Trust, kind: Class) -> Bool:
  match t:
    case Trusted{}:
      True{}
    case Untrusted{}:
      match kind:
        case Pref{}:
          True{}
        case Limit{}:
          False{}
        case Prompt{}:
          False{}
        case Credential{}:
          False{}

# the values that apply: the project items trust admits over the global
# document g
def effective(+t: Trust, g: List<&2, Entry>, items: List<&2, Item>) -> List<&2, Entry>:
  match items:
    case Nil{}:
      g
    case i <> rest:
      match i:
        case Item{k, kind, v}:
          guard(admits(t, kind), Entry{k, v}, effective(t, g, rest))

# an item of key j and class kind leaves key k to the global document
# when the project is untrusted: it is not a preference of key k
def guarded_at(+j: Nat, kind: Class, +k: Nat) -> Bool:
  match kind:
    case Pref{}:
      Bool.not(Nat.is_eq(j, k))
    case Limit{}:
      True{}
    case Prompt{}:
      True{}
    case Credential{}:
      True{}

# no preference item of the project has key k (every item of key k is a
# limit, a prompt or a credential)
def only_guarded(items: List<&2, Item>, +k: Nat) -> Bool:
  match items:
    case Nil{}:
      True{}
    case i <> rest:
      match i:
        case Item{j, kind, v}:
          Bool.and(guarded_at(j, kind, k), only_guarded(rest, k))

# Named entries
# -------------
# A map of named entries (`mcpServers`): each entry is a unit (its
# fields).

type Named is Data:
  Named{n: Nat, fs: List<&2, Entry>}

def find.pick(b: Bool, fs: List<&2, Entry>, later: Maybe<&2, List<&2, Entry>>) -> Maybe<&2, List<&2, Entry>>:
  match b:
    case True{}:
      Some{fs}
    case False{}:
      later

# the fields of the entry named n
def find(es: List<&2, Named>, +n: Nat) -> Maybe<&2, List<&2, Entry>>:
  match es:
    case Nil{}:
      None{}
    case e <> rest:
      match e:
        case Named{m, fs}:
          find.pick(Nat.is_eq(m, n), fs, find(rest, n))

# the entries of the project p over the global g: a project entry
# replaces the global entry of its name whole
def merge(g: List<&2, Named>, p: List<&2, Named>) -> List<&2, Named>:
  List.append(&2, Named, p, g)

# an entry is named n in es
def has(es: List<&2, Named>, +n: Nat) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Named{m, fs}:
          Bool.or(Nat.is_eq(m, n), has(rest, n))
