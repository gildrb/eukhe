# staging: the models of how a new session storage gets its place, how the
# leftovers of a crash go, and how the sessions directory is listed
# (crates/eukhe-core/src/durable/staging.rs, discovery.rs).
#
# Publish: a storage built in a staging directory moves to its target
# name only when no entry has that name; an entry there stays as it was.
#
# Sweep: the sweep walks every directory under its roots, except a
# storage (it holds main.jsonl), a symlink and a leftover. A node is one
# entry it may meet: `open` says the walk reaches it (every directory
# above it is plain), `held` that a live process holds its lock, `stale`
# that nothing touched it for a day. It removes a staging directory or a
# tombstone, and a lock file whose staging directory is gone, when the
# walk reaches it, no live process holds it, and it is stale.
#
# Listing: a sessions directory holds directories (a storage when it holds
# main.jsonl, is not hidden and its cwd reads) and legacy files
# `<stem>.jsonl` (listed when the header reads). A legacy file is listed
# only while no directory has its stem: an open imports it into
# `<stem>/`, and then that directory is the session.
#
# The bridge (bridge/bridge_staging.bend,
# crates/eukhe-core/src/durable/staging/bridge.rs) runs the real code on
# generated directories and compares.

import Base

# Publish
# -------

# a directory entry: its name and what it holds
type Entry is Data:
  Entry{name: Nat, tag: Nat}

def has(+n: Nat, es: List<&2, Entry>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Entry{m, t}:
          Bool.or(Nat.is_eq(m, n), has(n, rest))

def rename.put(+t: Nat, +m: Nat, g: Nat, rest: List<&2, Entry>, b: Bool) -> List<&2, Entry>:
  match b:
    case True{}:
      Entry{t, g} <> rest
    case False{}:
      Entry{m, g} <> rest

# the entries after the entry s takes the name t
def rename(+s: Nat, +t: Nat, es: List<&2, Entry>) -> List<&2, Entry>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Entry{+m, g}:
          rename.put(t, m, g, rename(s, t, rest), Nat.is_eq(m, s))

# what a publish did: whether it moved, and the entries after it
type Pub is Data:
  Pub{ok: Bool, es: List<&2, Entry>}

def Pub.ok(p: Pub) -> Bool:
  match p:
    case Pub{ok, es}:
      ok

def publish.go(+s: Nat, +t: Nat, taken: Bool, es: List<&2, Entry>) -> Pub:
  match taken:
    case True{}:
      Pub{False{}, es}
    case False{}:
      Pub{True{}, rename(s, t, es)}

def publish(+s: Nat, +t: Nat, +es: List<&2, Entry>) -> Pub:
  publish.go(s, t, has(t, es), es)

# Sweep
# -----

type Sort is Data:
  Leftover{}         # a staging directory or a tombstone
  Lock{dir: Bool}    # a staging lock file; dir: its directory is there
  Store{}            # a storage
  Plain{}            # another directory
  Other{}            # anything else

type Node is Data:
  Node{id: Nat, sort: Sort, held: Bool, stale: Bool, open: Bool}

def Node.held(n: Node) -> Bool:
  match n:
    case Node{i, k, h, s, o}:
      h

def Node.stale(n: Node) -> Bool:
  match n:
    case Node{i, k, h, s, o}:
      s

def Sort.swept(k: Sort) -> Bool:
  match k:
    case Leftover{}:
      True{}
    case Lock{d}:
      Bool.not(d)
    case Store{}:
      False{}
    case Plain{}:
      False{}
    case Other{}:
      False{}

# whether the sweep removes the node
def removes(n: Node) -> Bool:
  match n:
    case Node{i, k, h, s, o}:
      Bool.and(o, Bool.and(Bool.not(h), Bool.and(s, Sort.swept(k))))

def sweep.put(+n: Node, rest: List<&2, Node>, b: Bool) -> List<&2, Node>:
  match b:
    case True{}:
      n <> rest
    case False{}:
      rest

# the nodes the sweep removes, in order
def sweep(ns: List<&2, Node>) -> List<&2, Node>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> rest:
      sweep.put(n, sweep(rest), removes(n))

# Listing
# -------

type Ent is Data:
  Dir{name: Nat, main: Bool, hidden: Bool, cwd: Bool}
  Legacy{stem: Nat, header: Bool}

def mem(+n: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(Nat.is_eq(x, n), mem(n, rest))

# whether a directory has the name n
def dirn(+n: Nat, es: List<&2, Ent>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Dir{m, a, h, c}:
          Bool.or(Nat.is_eq(m, n), dirn(n, rest))
        case Legacy{s, r}:
          dirn(n, rest)

def keep.put(+n: Nat, rest: List<&2, Nat>, b: Bool) -> List<&2, Nat>:
  match b:
    case True{}:
      n <> rest
    case False{}:
      rest

# the storages listed
def durables(es: List<&2, Ent>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Dir{+m, a, h, c}:
          keep.put(m, durables(rest), Bool.and(a, Bool.and(Bool.not(h), c)))
        case Legacy{s, r}:
          durables(rest)

# the legacy files listed, with the whole directory `all`
def legacies(+all: List<&2, Ent>, es: List<&2, Ent>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Dir{m, a, h, c}:
          legacies(all, rest)
        case Legacy{+s, r}:
          keep.put(s, legacies(all, rest), Bool.and(r, Bool.not(dirn(s, all))))

# every listed session, by the name of the storage it opens as
def listing(+es: List<&2, Ent>) -> List<&2, Nat>:
  List.append(&2, Nat, durables(es), legacies(es, es))

# the directory after the legacy file with stem s is imported
def imported(+s: Nat, es: List<&2, Ent>) -> List<&2, Ent>:
  List.append(&2, Ent, es, [Dir{s, True{}, False{}, True{}}])
