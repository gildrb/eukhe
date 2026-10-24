# staging: how a new session storage gets its place, how the leftovers of
# a crash go, and how the sessions directory is listed
# (crates/eukhe-core/src/durable/staging.rs, discovery.rs).
#
# The file holds two things. First the model (Publish, Sweep, Listing):
# names are interned Nats and the facts are bits, the abstraction the first
# laws are about. Then the real rule (from "The real rule" on), which the
# compiled core runs (bend/ffi_staging.bend) on the facts the Rust gathers:
# real names, entry types, lock probes, modification times, cwds. The laws
# of laws/staging.bend tie the real rule to the model.
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


# ===========================================================================
# The real rule
# ===========================================================================
#
# What the compiled core decides, on the facts the Rust gathers (the Rust
# performs every removal, rename and read):
# - publish: the verdict of a rename without replacement (`settle`);
# - sweep: the class of every entry of a directory the walk lists (`meet`:
#   keep, enter, or judge it), and the plan for a judged entry from its
#   lock probe and its modification times (`judge`);
# - listing: bend/listing.bend (it uses the names of this section).

# Publish (real)
# --------------

# what a publish did: the storage moved to the target, or an entry held the
# target (nothing moved)
type Verdict is Data:
  Moved{}
  Taken{}

# the verdict of a publish whose rename without replacement met an entry at
# the target (taken) or not; the kernel decides the race, atomically
def settle(taken: Bool) -> Verdict:
  match taken:
    case True{}:
      Taken{}
    case False{}:
      Moved{}

# Names
# -----

# an entry's name: UTF-8 text, or bytes that are not UTF-8
type Name is Data:
  Utf{s: String}
  Raw{}

# an entry's type, symlinks not followed
type Form is Data:
  KDir{main: Bool}     # a directory; main: it holds main.jsonl, a file
  KFile{}              # a regular file
  KOther{}             # a symlink or anything else

# an entry of a directory listing
type Seen is Data:
  Seen{name: Name, kind: Form}

# the char c has the code x
def ch.is(c: Char, x: U32) -> Bool:
  match c:
    case Chr{y}:
      U32.is_eq(y, x)

# c is one of the chars of cs
def ch.in(+c: Char, cs: String) -> Bool:
  match cs:
    case SNil{}:
      False{}
    case SCon{x, t}:
      Bool.or(Char.is_eq(c, x), ch.in(c, t))

# a and b are the same text
def same(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{y, v}:
      False{}
    case SCon{x, u} SNil{}:
      False{}
    case SCon{x, u} SCon{y, v}:
      Bool.and(Char.is_eq(x, y), same(u, v))

# the name n is the text s
def named(+s: String, n: Name) -> Bool:
  match n:
    case Utf{t}:
      same(t, s)
    case Raw{}:
      False{}

# an entry of es has the name s
def has_name(+s: String, es: List<&2, Seen>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Seen{n, k}:
          Bool.or(named(s, n), has_name(s, rest))

def kept_if(ok: Bool, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      m
    case False{}:
      None{}

# s after the prefix p, when s starts with p
def unprefix(p: String, s: String) -> Maybe<&2, String>:
  match p:
    case SNil{}:
      Some{s}
    case SCon{x, pt}:
      match s:
        case SNil{}:
          None{}
        case SCon{y, st}:
          kept_if(Char.is_eq(x, y), unprefix(pt, st))

def unsuffix.here(b: Bool, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{""}
    case False{}:
      m

def unsuffix.cons(c: Char, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      Some{SCon{c, r}}

# s before the suffix p, when s ends with p
def unsuffix(+p: String, +s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      unsuffix.here(String.is_empty(p), None{})
    case SCon{c, t}:
      unsuffix.here(same(SCon{c, t}, p), unsuffix.cons(c, unsuffix(p, t)))

# Sweep (real)
# ------------

# a text split at a '.': the text before it and the text after it
type Split is Data:
  Split{before: String, after: String}

def cut.cons(c: Char, p: Split) -> Maybe<&2, Split>:
  match p:
    case Split{b, a}:
      Some{Split{SCon{c, b}, a}}

def cut.dot(d: Bool, t: String) -> Maybe<&2, Split>:
  match d:
    case True{}:
      Some{Split{SNil{}, t}}
    case False{}:
      None{}

def cut.put(r: Maybe<&2, Split>, d: Bool, c: Char, t: String) -> Maybe<&2, Split>:
  match r:
    case Some{p}:
      cut.cons(c, p)
    case None{}:
      cut.dot(d, t)

# w split at its last '.'
def cut(w: String) -> Maybe<&2, Split>:
  match w:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      cut.put(cut(t), ch.is(c, 46), c, t)

def hex(c: Char) -> Bool:
  ch.in(c, "0123456789abcdef")

# s is n lowercase hex digits
def hexn(n: Nat, s: String) -> Bool:
  match n:
    case 0n:
      String.is_empty(s)
    case 1n+k:
      match s:
        case SNil{}:
          False{}
        case SCon{c, t}:
          Bool.and(hex(c), hexn(k, t))

# a simple-format uuid: 32 lowercase hex digits
def uuid(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      hexn(32n, s)

# the part after the last '.' of a swept name: a label, '-', a uuid. The
# labels: an import or a fork staging directory, a saved-session tombstone
def tail(+a: String) -> Bool:
  Bool.or(uuid(unprefix("import-", a)), Bool.or(uuid(unprefix("fork-", a)), uuid(unprefix("deleted-", a))))

def swept.parts(p: Split) -> Bool:
  match p:
    case Split{b, a}:
      Bool.and(Bool.not(String.is_empty(b)), tail(a))

def swept.cut(m: Maybe<&2, Split>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{p}:
      swept.parts(p)

# s is a name a staging directory or a tombstone gets:
# `.<target>.<label>-<uuid>`, the target not empty
def swept(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.and(ch.is(c, 46), swept.cut(cut(t)))

# what the sweep does with an entry of a directory it lists
type Met is Data:
  MKeep{}       # keep it, do not enter it
  MDescend{}    # a directory the walk enters
  MLeftover{}   # a staging directory or a tombstone: judge it
  MOrphan{}     # a staging lock file whose directory is gone: judge it

def met.dir(sw: Bool, main: Bool) -> Met:
  match sw:
    case True{}:
      MLeftover{}
    case False{}:
      match main:
        case True{}:
          MKeep{}
        case False{}:
          MDescend{}

def met.lock(sw: Bool, there: Bool) -> Met:
  match sw:
    case True{}:
      match there:
        case True{}:
          MKeep{}
        case False{}:
          MOrphan{}
    case False{}:
      MKeep{}

def met.file(m: Maybe<&2, String>, all: List<&2, Seen>) -> Met:
  match m:
    case None{}:
      MKeep{}
    case Some{+x}:
      met.lock(swept(x), has_name(x, all))

def met.utf(k: Form, +s: String, all: List<&2, Seen>) -> Met:
  match k:
    case KDir{main}:
      met.dir(swept(s), main)
    case KFile{}:
      met.file(unsuffix(".lock", s), all)
    case KOther{}:
      MKeep{}

def met.raw(k: Form) -> Met:
  match k:
    case KDir{main}:
      met.dir(False{}, main)
    case KFile{}:
      MKeep{}
    case KOther{}:
      MKeep{}

# what the sweep does with the entry e of the directory listing all
def met(e: Seen, all: List<&2, Seen>) -> Met:
  match e:
    case Seen{n, k}:
      match n:
        case Utf{s}:
          met.utf(k, s, all)
        case Raw{}:
          met.raw(k)

def meet.go(es: List<&2, Seen>, +all: List<&2, Seen>) -> List<&2, Met>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      met(e, all) <> meet.go(rest, all)

# what the sweep does with each entry of a directory listing, in order
def meet(+es: List<&2, Seen>) -> List<&2, Met>:
  meet.go(es, es)

# a lock probe
type Lock is Data:
  LHeld{}     # a live process holds the lock
  LFree{}     # the sweep holds the lock now: no live process does
  LAbsent{}   # no lock file is there

# what the sweep judges
type Cand is Data:
  CDir{}      # a staging directory or a tombstone (its lock file beside it)
  CLock{}     # a staging lock file whose directory is gone

# a modification time: seconds and nanoseconds after the epoch
type Time is Data:
  Time{secs: Nat, nanos: Nat}

# what the sweep does with a judged entry
type Plan is Data:
  PKeep{}       # keep it
  PRmDir{}      # remove the directory
  PRmDirLock{}  # remove the directory, then its lock file
  PRmFile{}     # remove the lock file

# A day, in seconds: how long a leftover stays untouched before the sweep
# takes it for a crash leftover, when no live process holds its lock. The
# lock is the evidence that a build runs; the age covers the moment
# between the creation of a lock file and its lock, and the leftovers of a
# build that held no lock. A staging directory lives for one import or
# fork: seconds, minutes for the largest sessions; a day is orders of
# magnitude above that, and the margin costs only the disk a leftover
# holds until a later sweep. Tombstones share the bound: a rename keeps
# modification times, so the fresh tombstone of an old session already
# counts as stale, and a sweep may remove it under a running delete
# (concurrent removals tolerate each other).
def day() -> Nat:
  86400n

# t is at least a day before now (a time ahead of now is fresh)
def stale(+now: Time, t: Time) -> Bool:
  match now:
    case Time{+ns, nn}:
      match t:
        case Time{ts, tn}:
          +d = Nat.add(ts, day())
          Bool.or(Nat.is_lt(d, ns), Bool.and(Nat.is_eq(d, ns), Nat.is_le(tn, nn)))

# every time of ts is at least a day before now
def stale_all(+now: Time, ts: List<&2, Time>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case t <> rest:
      Bool.and(stale(now, t), stale_all(now, rest))

def judge.free(c: Cand, l: Lock) -> Plan:
  match c:
    case CDir{}:
      match l:
        case LHeld{}:
          PKeep{}
        case LFree{}:
          PRmDirLock{}
        case LAbsent{}:
          PRmDir{}
    case CLock{}:
      match l:
        case LHeld{}:
          PKeep{}
        case LFree{}:
          PRmFile{}
        case LAbsent{}:
          PKeep{}

def judge.go(old: Bool, c: Cand, l: Lock) -> Plan:
  match old:
    case True{}:
      judge.free(c, l)
    case False{}:
      PKeep{}

# the plan for the judged entry c: its lock probe l, the time now, its own
# modification time and those of its direct entries (none for a lock file)
def judge(c: Cand, l: Lock, +now: Time, own: Time, inner: List<&2, Time>) -> Plan:
  judge.go(stale_all(now, own <> inner), c, l)
