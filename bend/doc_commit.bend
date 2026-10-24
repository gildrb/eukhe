# doc_commit: the models of how the documents tools put files on disk
# (crates/eukhe-docs/src/write.rs, hashline/mod.rs, documents.rs).
#
# Edit: an edit of many files first locks every path and checks every
# file (phase 1): when one file changed since it was staged, the edit
# writes nothing. Then it publishes the files in order and stops at the
# first publish that fails (phase 2). A publish lands; or lands with a
# warning (the rename is done but the directory sync fails, or a move put
# its destination in place but could not remove its source); or fails
# (nothing of that file lands). The reply calls a file applied only when
# it landed.
#
# Write: the write tool replaces a file only when the bytes on disk are a
# version the session saw (it read them, grep showed them, or it wrote
# them); a missing file is created. The session keeps the last 8 versions
# it saw.
#
# Move: an MV never replaces a file: when its destination exists it is
# refused and nothing changes.
#
# Sweep: a replace of a file removes the temporary files of that file
# that no live writer holds; it keeps every other entry.
#
# The writer's choices (the last section) run as the compiled core
# (bend/ffi_doc_commit.bend, called from crates/eukhe-docs write.rs,
# hashline/mod.rs, store.rs): Rust locks, reads, compares bytes, hashes,
# publishes and removes; each choice is a function of what it met, and
# the laws tie each to the models above.

import Base

# Edit
# ----

type Op is Data:
  Update{}   # the file gets new content
  Moving{}   # the file moves to a free name

type Fault is Data:
  Clean{}    # no fault
  Sync{}     # the rename is done; the directory sync fails
  Publish{}  # the publish fails: nothing of the file lands
  Remove{}   # a move: the destination lands; the source removal fails

# one file of an edit: changed says that its bytes changed since the edit
# staged it
type Doc is Data:
  Doc{op: Op, changed: Bool, fault: Fault}

# what one publish did
type Out is Data:
  Landed{warn: Bool}
  Failed{}

def publish.go(x: Fault, k: Op) -> Out:
  match x:
    case Clean{}:
      Landed{False{}}
    case Sync{}:
      Landed{True{}}
    case Publish{}:
      Failed{}
    case Remove{}:
      match k:
        case Update{}:
          Landed{False{}}
        case Moving{}:
          Landed{True{}}

def publish(f: Doc) -> Out:
  match f:
    case Doc{k, c, x}:
      publish.go(x, k)

def Fault.fails(x: Fault) -> Bool:
  match x:
    case Clean{}:
      False{}
    case Sync{}:
      False{}
    case Publish{}:
      True{}
    case Remove{}:
      False{}

# phase 1: whether a file changed since the edit staged it
def conflict(fs: List<&2, Doc>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case f <> rest:
      match f:
        case Doc{k, c, x}:
          Bool.or(c, conflict(rest))

# whether a publish fails
def failing(fs: List<&2, Doc>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case f <> rest:
      match f:
        case Doc{k, c, x}:
          Bool.or(Fault.fails(x), failing(rest))

def landed.put(+n: Nat, rest: List<&2, Nat>, o: Out) -> List<&2, Nat>:
  match o:
    case Landed{w}:
      n <> rest
    case Failed{}:
      Nil{}

# the disk: the files (by index, from n) whose new content lands, in order
def landed.go(fs: List<&2, Doc>, +n: Nat) -> List<&2, Nat>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      landed.put(n, landed.go(rest, 1n+n), publish(f))

def landed.pick(c: Bool, fs: List<&2, Doc>) -> List<&2, Nat>:
  match c:
    case True{}:
      Nil{}
    case False{}:
      landed.go(fs, 0n)

# the files whose new content is on disk after the edit
def landed(+fs: List<&2, Doc>) -> List<&2, Nat>:
  landed.pick(conflict(fs), fs)

def run.put(o: Out, rest: List<&2, Out>) -> List<&2, Out>:
  match o:
    case Landed{w}:
      Landed{w} <> rest
    case Failed{}:
      [Failed{}]

# phase 2: the publishes, in order, up to the first that fails
def run(fs: List<&2, Doc>) -> List<&2, Out>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      run.put(publish(f), run(rest))

# what the reply says of one file
type Report is Data:
  Applied{warn: Bool}
  NotWritten{}

def report.put(o: Out, rest: List<&2, Report>) -> List<&2, Report>:
  match o:
    case Landed{w}:
      Applied{w} <> rest
    case Failed{}:
      NotWritten{} <> rest

# one report a file, from the publishes: a file with no publish was not
# written
def report(fs: List<&2, Doc>, os: List<&2, Out>) -> List<&2, Report>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      match os:
        case Nil{}:
          NotWritten{} <> report(rest, Nil{})
        case o <> more:
          report.put(o, report(rest, more))

type Reply is Data:
  Rejected{}                         # an error: nothing was written
  Answered{files: List<&2, Report>}  # applied, or applied in part

def reply.go(os: List<&2, Out>, fs: List<&2, Doc>) -> Reply:
  match os:
    case Nil{}:
      Answered{report(fs, Nil{})}
    case o <> more:
      match o:
        case Landed{w}:
          Answered{report(fs, Landed{w} <> more)}
        case Failed{}:
          Rejected{}

def reply.pick(c: Bool, +fs: List<&2, Doc>) -> Reply:
  match c:
    case True{}:
      Rejected{}
    case False{}:
      reply.go(run(fs), fs)

# the reply of the edit
def reply(+fs: List<&2, Doc>) -> Reply:
  reply.pick(conflict(fs), fs)

def applied(rs: List<&2, Report>, +n: Nat) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Applied{w}:
          n <> applied(rest, 1n+n)
        case NotWritten{}:
          applied(rest, 1n+n)

# the files (by index) the reply reports applied
def reported(r: Reply) -> List<&2, Nat>:
  match r:
    case Rejected{}:
      Nil{}
    case Answered{rs}:
      applied(rs, 0n)

# the indices of the files, from n
def ids(fs: List<&2, Doc>, +n: Nat) -> List<&2, Nat>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      n <> ids(rest, 1n+n)

# Write
# -----

def mem(+v: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(Nat.is_eq(x, v), mem(v, rest))

def drop.put(+x: Nat, rest: List<&2, Nat>, b: Bool) -> List<&2, Nat>:
  match b:
    case True{}:
      rest
    case False{}:
      x <> rest

def drop(+v: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      drop.put(x, drop(v, rest), Nat.is_eq(x, v))

# the versions seen after the session sees v: newest first, once each,
# the last 8
def saw(+v: Nat, s: List<&2, Nat>) -> List<&2, Nat>:
  List.take(&2, Nat, v <> drop(v, s), 8n)

# whether the disk holds a version the session did not see
def unseen(d: Maybe<&2, Nat>, +s: List<&2, Nat>) -> Bool:
  match d:
    case None{}:
      False{}
    case Some{v}:
      Bool.not(mem(v, s))

# what a write did: whether it wrote, the disk and the seen versions after
type Wt is Data:
  Wt{ok: Bool, disk: Maybe<&2, Nat>, seen: List<&2, Nat>}

def write.go(b: Bool, d: Maybe<&2, Nat>, +s: List<&2, Nat>, +c: Nat) -> Wt:
  match b:
    case True{}:
      Wt{False{}, d, s}
    case False{}:
      Wt{True{}, Some{c}, saw(c, s)}

# the session writes c over the disk d, having seen the versions s
def write(+d: Maybe<&2, Nat>, +s: List<&2, Nat>, +c: Nat) -> Wt:
  write.go(unseen(d, s), d, s, c)

# Move
# ----

# a file: its name and its content
type Entry is Data:
  Entry{name: Nat, body: Nat}

def has(+n: Nat, es: List<&2, Entry>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Entry{m, g}:
          Bool.or(Nat.is_eq(m, n), has(n, rest))

def get.put(b: Bool, g: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{g}
    case False{}:
      rest

# the content of the file named n
def get(+n: Nat, es: List<&2, Entry>) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      None{}
    case e <> rest:
      match e:
        case Entry{m, g}:
          get.put(Nat.is_eq(m, n), g, get(n, rest))

def rename.put(+t: Nat, +m: Nat, g: Nat, rest: List<&2, Entry>, b: Bool) -> List<&2, Entry>:
  match b:
    case True{}:
      Entry{t, g} <> rest
    case False{}:
      Entry{m, g} <> rest

# the files after the file s takes the name t
def rename(+s: Nat, +t: Nat, es: List<&2, Entry>) -> List<&2, Entry>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Entry{+m, g}:
          rename.put(t, m, g, rename(s, t, rest), Nat.is_eq(m, s))

# what a move did: whether it moved, and the files after it
type Mv is Data:
  Mv{ok: Bool, es: List<&2, Entry>}

def Mv.ok(m: Mv) -> Bool:
  match m:
    case Mv{ok, es}:
      ok

def Mv.es(m: Mv) -> List<&2, Entry>:
  match m:
    case Mv{ok, es}:
      es

def move.go(+s: Nat, +t: Nat, taken: Bool, es: List<&2, Entry>) -> Mv:
  match taken:
    case True{}:
      Mv{False{}, es}
    case False{}:
      Mv{True{}, rename(s, t, es)}

# MV s t over the files es
def move(+s: Nat, +t: Nat, +es: List<&2, Entry>) -> Mv:
  move.go(s, t, has(t, es), es)

# Sweep
# -----

type Sort is Data:
  Own{}      # a temporary file of the target
  Foreign{}  # a temporary file of another target
  Plain{}    # another file

def Sort.own(k: Sort) -> Bool:
  match k:
    case Own{}:
      True{}
    case Foreign{}:
      False{}
    case Plain{}:
      False{}

# an entry of the target's directory; held: a live writer holds its lock
type Temp is Data:
  Temp{id: Nat, sort: Sort, held: Bool}

# whether the sweep removes the entry
def removes(n: Temp) -> Bool:
  match n:
    case Temp{i, k, h}:
      Bool.and(Sort.own(k), Bool.not(h))

def sweep.put(+n: Temp, rest: List<&2, Temp>, b: Bool) -> List<&2, Temp>:
  match b:
    case True{}:
      n <> rest
    case False{}:
      rest

# the entries the sweep removes, in order
def sweep(ns: List<&2, Temp>) -> List<&2, Temp>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> rest:
      sweep.put(n, sweep(rest), removes(n))

# The writer's choices
# --------------------
# What the real writer decides from what it met. Content digests are
# texts Rust computes (the hash stays Rust); two digests name the same
# bytes exactly when they are the same text.

# a and b are the same text, char by char
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

# Phase 1: the check of an edit
# -----------------------------

# what the check of one file met: its bytes changed since the edit staged
# it; a move whose destination exists
type Met is Data:
  Met{changed: Bool, taken: Bool}

type Why is Data:
  Changed{}  # the file changed on disk
  Taken{}    # the move's destination exists

type Check is Data:
  Go{}                    # publish every file
  Stop{at: Nat, why: Why} # write nothing: file `at` is why

def check.met(changed: Bool, taken: Bool, +n: Nat, rest: Check) -> Check:
  match changed:
    case True{}:
      Stop{n, Changed{}}
    case False{}:
      match taken:
        case True{}:
          Stop{n, Taken{}}
        case False{}:
          rest

# the check of the files from index n: the first file that changed or
# whose destination exists stops the edit
def check.go(ms: List<&2, Met>, +n: Nat) -> Check:
  match ms:
    case Nil{}:
      Go{}
    case m <> rest:
      match m:
        case Met{c, t}:
          check.met(c, t, n, check.go(rest, 1n+n))

def check(ms: List<&2, Met>) -> Check:
  check.go(ms, 0n)

# Phase 2: one publish
# --------------------

# where a publish put the new bytes
type Placed is Data:
  NotPlaced{}             # the write or the rename failed
  Placed{synced: Bool}    # the target holds them; the directory sync

# what one publish met
type Pub is Data:
  Updated{placed: Placed}               # a file got new content
  Deleted{removed: Bool}                # a file was removed (or not)
  Moved{placed: Placed, removed: Bool}  # the destination placed; the source removed

# the warning a landed publish carries
type Warn is Data:
  NoWarn{}
  SyncWarn{}    # the directory sync failed
  RemoveWarn{}  # a move could not remove its source

type Outcome is Data:
  Lands{warn: Warn}   # the change is on disk: go on
  Fails{}             # nothing of it landed: stop here

def placed.out(p: Placed) -> Outcome:
  match p:
    case NotPlaced{}:
      Fails{}
    case Placed{s}:
      match s:
        case True{}:
          Lands{NoWarn{}}
        case False{}:
          Lands{SyncWarn{}}

def moved.out(p: Placed, removed: Bool) -> Outcome:
  match p:
    case NotPlaced{}:
      Fails{}
    case Placed{s}:
      match removed:
        case False{}:
          Lands{RemoveWarn{}}
        case True{}:
          placed.out(Placed{s})

def removed.out(r: Bool) -> Outcome:
  match r:
    case True{}:
      Lands{NoWarn{}}
    case False{}:
      Fails{}

# what one publish did
def outcome(p: Pub) -> Outcome:
  match p:
    case Updated{x}:
      placed.out(x)
    case Deleted{r}:
      removed.out(r)
    case Moved{x, r}:
      moved.out(x, r)

# The reply of an edit
# --------------------

# what became of one staged file
type Fate is Data:
  Noop{}               # nothing to write
  Wrote{out: Outcome}  # its publish
  Untried{}            # a publish before it failed

type Note is Data:
  Untouched{}          # a no-op
  Written{}            # it landed
  Unwritten{}          # its publish failed (its own reason)
  Skipped{at: Nat}     # not tried: file `at` failed first

type Verdict is Data:
  Failure{}                                       # nothing landed: the first failure is the error
  Summary{files: List<&2, Note>, partial: Bool}   # partial: some file was not written

def lands(o: Outcome) -> Bool:
  match o:
    case Lands{w}:
      True{}
    case Fails{}:
      False{}

def fails(o: Outcome) -> Bool:
  Bool.not(lands(o))

def any.landed(fs: List<&2, Fate>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case f <> rest:
      match f:
        case Noop{}:
          any.landed(rest)
        case Wrote{o}:
          Bool.or(lands(o), any.landed(rest))
        case Untried{}:
          any.landed(rest)

def any.failed(fs: List<&2, Fate>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case f <> rest:
      match f:
        case Noop{}:
          any.failed(rest)
        case Wrote{o}:
          Bool.or(fails(o), any.failed(rest))
        case Untried{}:
          any.failed(rest)

def first.put(o: Outcome, +n: Nat, rest: Nat) -> Nat:
  match o:
    case Lands{w}:
      rest
    case Fails{}:
      n

# the index of the first failed publish from index n (past the end: none)
def first.failed(fs: List<&2, Fate>, +n: Nat) -> Nat:
  match fs:
    case Nil{}:
      n
    case f <> rest:
      match f:
        case Noop{}:
          first.failed(rest, 1n+n)
        case Wrote{o}:
          first.put(o, n, first.failed(rest, 1n+n))
        case Untried{}:
          first.failed(rest, 1n+n)

def report.of(+k: Nat, f: Fate) -> Note:
  match f:
    case Noop{}:
      Untouched{}
    case Wrote{o}:
      match o:
        case Lands{w}:
          Written{}
        case Fails{}:
          Unwritten{}
    case Untried{}:
      Skipped{k}

# one report a file; k: the first failed file
def reports(fs: List<&2, Fate>, +k: Nat) -> List<&2, Note>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      report.of(k, f) <> reports(rest, k)

def unwritten(fs: List<&2, Fate>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case f <> rest:
      match f:
        case Noop{}:
          unwritten(rest)
        case Wrote{o}:
          Bool.or(fails(o), unwritten(rest))
        case Untried{}:
          True{}

def answer.go(rejected: Bool, +fs: List<&2, Fate>) -> Verdict:
  match rejected:
    case True{}:
      Failure{}
    case False{}:
      Summary{reports(fs, first.failed(fs, 0n)), unwritten(fs)}

# the reply of an edit: an error when a publish failed and none landed
def answer(+fs: List<&2, Fate>) -> Verdict:
  answer.go(Bool.and(any.failed(fs), Bool.not(any.landed(fs))), fs)

# The write tool
# --------------

# what the write is based on
type Base is Data:
  OnSeen{seen: List<&2, String>}  # versions the session saw (their digests)
  OnBytes{}                       # exactly the bytes the caller holds

# what the target held when the write locked it
type Disk is Data:
  Absent{}
  Present{digest: String, expected: Bool}  # its digest; expected: the caller's bytes

type Gate is Data:
  Proceed{}   # write
  Unseen{}    # refuse: the session did not see these bytes
  Stale{}     # refuse: the bytes are not the expected ones (or the file is gone)

def member(+d: String, s: List<&2, String>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(same(x, d), member(d, rest))

def gate.seen(b: Bool) -> Gate:
  match b:
    case True{}:
      Proceed{}
    case False{}:
      Unseen{}

def gate.bytes(b: Bool) -> Gate:
  match b:
    case True{}:
      Proceed{}
    case False{}:
      Stale{}

# whether the write tool may replace the target
def gate(b: Base, d: Disk) -> Gate:
  match b:
    case OnSeen{s}:
      match d:
        case Absent{}:
          Proceed{}
        case Present{g, e}:
          gate.seen(member(g, s))
    case OnBytes{}:
      match d:
        case Absent{}:
          Stale{}
        case Present{g, e}:
          gate.bytes(e)

def unsee.put(+x: String, rest: List<&2, String>, b: Bool) -> List<&2, String>:
  match b:
    case True{}:
      rest
    case False{}:
      x <> rest

def unsee(+d: String, s: List<&2, String>) -> List<&2, String>:
  match s:
    case Nil{}:
      Nil{}
    case +x <> rest:
      unsee.put(x, unsee(d, rest), same(x, d))

# the versions seen after the session sees digest d: newest first, once
# each, the last 8 (`saw` of the model, on digests)
def seen(+d: String, s: List<&2, String>) -> List<&2, String>:
  List.take(&2, String, d <> unsee(d, s), 8n)

# The temporary files
# -------------------

# the name prefix of every temporary file of the writer
def temp() -> String:
  ".eukhe-tmp-"

# the name prefix of the temporary files of a target whose file name has
# the digest h
def prefix(h: String) -> String:
  String.append(temp(), String.append(h, "-"))

def starts(p: String, s: String) -> Bool:
  match p:
    case SNil{}:
      True{}
    case SCon{c, q}:
      match s:
        case SNil{}:
          False{}
        case SCon{d, t}:
          Bool.and(Char.is_eq(c, d), starts(q, t))

# an entry of the target's directory: its name (lossy UTF-8), and whether
# a live writer holds its lock
type Ent is Data:
  Ent{name: String, held: Bool}

def sweeps(+p: String, e: Ent) -> Bool:
  match e:
    case Ent{n, h}:
      Bool.and(starts(p, n), Bool.not(h))

def gone.put(+n: Nat, rest: List<&2, Nat>, b: Bool) -> List<&2, Nat>:
  match b:
    case True{}:
      n <> rest
    case False{}:
      rest

def gone.go(+p: String, es: List<&2, Ent>, +n: Nat) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      gone.put(n, gone.go(p, rest, 1n+n), sweeps(p, e))

# the entries (by index) the sweep of the target with digest h removes
def gone(h: String, es: List<&2, Ent>) -> List<&2, Nat>:
  gone.go(prefix(h), es, 0n)
