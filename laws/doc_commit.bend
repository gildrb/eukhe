# eukhe: the laws of area doc_commit

import Base
import ../bend/doc_commit.bend as Cm
import ../bend/ffi_doc_commit.bend as FCm
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- documents ----

# LAWS: the documents tools (crates/eukhe-docs and the documents tools of
# crates/eukhe-core): edits, writes, moves, temporary files, line endings,
# tags, seen lines, grep and glob. Each law is an open claim about a model
# in bend/doc_*.bend; PROOF.bend proves them (as DocCommit.<law>) with the
# lemmas of proof/doc_commit/ and, for lines and their endings,
# proof/doc_lines/.

# (F1, F9) An edit of many files
# ------------------------------
# bend/doc_commit.bend: every input is free: any files, each an update or
# a move, changed since the edit staged it or not, with any fault (none,
# a failed directory sync, a failed publish, a failed source removal).

# LAW edit_reports_what_landed: the reply calls a file applied exactly when its new content is on
# disk: after a conflict, a publish that fails at any file, or a publish
# that lands with a warning
law edit_reports_what_landed:
  for +fs: List<&2, Cm.Doc>
  {Cm.reported(Cm.reply(fs)) == Cm.landed(fs) : List<&2, Nat>}

# LAW edit_all_or_nothing_on_conflict: when one file changed since the edit staged it, no file lands
law edit_all_or_nothing_on_conflict:
  for +pre: List<&2, Cm.Doc>
  for +k: Cm.Op
  for +x: Cm.Fault
  for +post: List<&2, Cm.Doc>
  {Cm.landed(List.append(&2, Cm.Doc, pre, Cm.Doc{k, True{}, x} <> post)) == Nil{} : List<&2, Nat>}

# LAW edit_lands_every_file: an edit with no changed file and no failed publish lands every
# file
law edit_lands_every_file:
  for +fs: List<&2, Cm.Doc>
  for same: {Cm.conflict(fs) == False{} : Bool}
  for sound: {Cm.failing(fs) == False{} : Bool}
  {Cm.landed(fs) == Cm.ids(fs, 0n) : List<&2, Nat>}

# (F2) The write tool
# -------------------
# bend/doc_commit.bend: every input is free: any disk (a version or no
# file), any versions the session saw, any new content.

# LAW write_never_loses_unseen: a write over a version the session did not see is refused and
# changes nothing: a write never loses a change the session did not see
law write_never_loses_unseen:
  for +d: Maybe<&2, Nat>
  for +s: List<&2, Nat>
  for +c: Nat
  for lost: {Cm.unseen(d, s) == True{} : Bool}
  {Cm.write(d, s, c) == Cm.Wt{False{}, d, s} : Cm.Wt}

# LAW write_writes_seen: a write over no file or over a version the session saw writes,
# and the session then knows the new version
law write_writes_seen:
  for +d: Maybe<&2, Nat>
  for +s: List<&2, Nat>
  for +c: Nat
  for kept: {Cm.unseen(d, s) == False{} : Bool}
  {Cm.write(d, s, c) == Cm.Wt{True{}, Some{c}, Cm.saw(c, s)} : Cm.Wt}

# (F5) A move
# -----------
# bend/doc_commit.bend: every input is free: any files with any names
# and contents, any source and destination names.

# LAW move_never_overwrites: a move to a name that a file has is refused and changes nothing:
# an MV never replaces a file
law move_never_overwrites:
  for +s: Nat
  for +t: Nat
  for +es: List<&2, Cm.Entry>
  for taken: {Cm.has(t, es) == True{} : Bool}
  {Cm.move(s, t, es) == Cm.Mv{False{}, es} : Cm.Mv}

# LAW move_moves: a move of a file to a free name moves it: the move is done, the
# source name is gone, and the destination holds the source's content
law move_moves:
  for +s: Nat
  for +t: Nat
  for +es: List<&2, Cm.Entry>
  for free: {Cm.has(t, es) == False{} : Bool}
  for from: {Cm.has(s, es) == True{} : Bool}
  {Cm.Mv.ok(Cm.move(s, t, es)) == True{} : Bool} & {Cm.has(s, Cm.Mv.es(Cm.move(s, t, es))) == False{} : Bool} & {Cm.get(t, Cm.Mv.es(Cm.move(s, t, es))) == Cm.get(s, es) : Maybe<&2, Nat>}

# (F10) Temporary files
# ---------------------
# bend/doc_commit.bend: every input is free: any entries in the target's
# directory (a temporary file of the target, of another target, or
# another file), held by a live writer or not.

# LAW temp_sweep_never_held: a sweep never removes a temporary file that a live writer holds
law temp_sweep_never_held:
  for +pre: List<&2, Cm.Temp>
  for +i: Nat
  for +k: Cm.Sort
  for +post: List<&2, Cm.Temp>
  {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, k, True{}} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}

# LAW temp_sweep_only_own: a sweep never removes a temporary file of another target, or a
# file that is not a temporary file
law temp_sweep_only_own:
  for +pre: List<&2, Cm.Temp>
  for +i: Nat
  for +k: Cm.Sort
  for +h: Bool
  for +post: List<&2, Cm.Temp>
  for other: {Cm.Sort.own(k) == False{} : Bool}
  {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, k, h} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}

# LAW temp_sweep_removes_free: a sweep removes every temporary file of the target that no live
# writer holds
law temp_sweep_removes_free:
  for +pre: List<&2, Cm.Temp>
  for +i: Nat
  for +post: List<&2, Cm.Temp>
  {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, Cm.Own{}, False{}} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.Temp{i, Cm.Own{}, False{}} <> Cm.sweep(post)) : List<&2, Cm.Temp>}

# (F1, F9, F10) The writer's choices
# ----------------------------------
# bend/doc_commit.bend section "The writer's choices", run as the compiled
# core by bend/ffi_doc_commit.bend (crates/eukhe-docs write.rs,
# hashline/mod.rs, store.rs). Every input is free: any files of an edit
# with any check facts, any publish facts, any staged files with any
# outcome, any base and disk of a write, any digests, any directory
# entries with any names, held or not.
#
# R1: an edit writes nothing when a file changed since it was staged or a
#     move's destination exists: the first such file (a change before a
#     taken destination in one file) is the reason; otherwise every file
#     is published.
# R2: a publish lands when its new bytes are in place (with a warning when
#     the directory sync failed, or when a move could not remove its
#     source, the second taking precedence); a delete lands when the file
#     is removed; anything else fails and stops the edit.
# R3: the reply of an edit is an error exactly when a publish failed and
#     none landed; otherwise it lists each staged file (a no-op, written,
#     not written for its own reason, or not tried because the first
#     failed file failed first) and says whether some file was not
#     written.
# R4: the write tool replaces a file based on seen versions only when its
#     bytes are a version the session saw (a missing file is created);
#     based on exact bytes only when the file still holds them.
# R5: after the session sees a version, the seen versions are it, then
#     the earlier ones without it, the last 8.
# R6: the temporary files of a target are named `.eukhe-tmp-<digest>-...`
#     (the digest of its file name); a sweep removes exactly the entries
#     with that prefix that no live writer holds, never another target's
#     temporary files or other files.
# R7: the entry answers each request Rust writes with the choice of R1-R6,
#     reads exactly the request and nothing after it, and answers any
#     other input with the exact error form.

# Spec helpers
# ------------

# R1
def sp_check(ms: List<&2, Cm.Met>, +n: Nat) -> Cm.Check:
  match ms:
    case Nil{}:
      Cm.Go{}
    case m <> rest:
      match m:
        case Cm.Met{c, t}:
          match c:
            case True{}:
              Cm.Stop{n, Cm.Changed{}}
            case False{}:
              match t:
                case True{}:
                  Cm.Stop{n, Cm.Taken{}}
                case False{}:
                  sp_check(rest, 1n+n)

def sp_go(c: Cm.Check) -> Bool:
  match c:
    case Cm.Go{}:
      True{}
    case Cm.Stop{at, why}:
      False{}

# the check facts of the model's files: changed as staged, no move taken
def sp_mets(fs: List<&2, Cm.Doc>) -> List<&2, Cm.Met>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      match f:
        case Cm.Doc{k, c, x}:
          Cm.Met{c, False{}} <> sp_mets(rest)

def sp_placed(p: Cm.Placed) -> Cm.Outcome:
  match p:
    case Cm.NotPlaced{}:
      Cm.Fails{}
    case Cm.Placed{s}:
      match s:
        case True{}:
          Cm.Lands{Cm.NoWarn{}}
        case False{}:
          Cm.Lands{Cm.SyncWarn{}}

# R2
def sp_outcome(p: Cm.Pub) -> Cm.Outcome:
  match p:
    case Cm.Updated{x}:
      sp_placed(x)
    case Cm.Deleted{r}:
      match r:
        case True{}:
          Cm.Lands{Cm.NoWarn{}}
        case False{}:
          Cm.Fails{}
    case Cm.Moved{x, r}:
      match x:
        case Cm.NotPlaced{}:
          Cm.Fails{}
        case Cm.Placed{s}:
          match r:
            case True{}:
              sp_placed(Cm.Placed{s})
            case False{}:
              Cm.Lands{Cm.RemoveWarn{}}

# the publish facts a fault of the model stands for
def sp_pub(k: Cm.Op, x: Cm.Fault) -> Cm.Pub:
  match k:
    case Cm.Update{}:
      match x:
        case Cm.Clean{}:
          Cm.Updated{Cm.Placed{True{}}}
        case Cm.Sync{}:
          Cm.Updated{Cm.Placed{False{}}}
        case Cm.Publish{}:
          Cm.Updated{Cm.NotPlaced{}}
        case Cm.Remove{}:
          Cm.Updated{Cm.Placed{True{}}}
    case Cm.Moving{}:
      match x:
        case Cm.Clean{}:
          Cm.Moved{Cm.Placed{True{}}, True{}}
        case Cm.Sync{}:
          Cm.Moved{Cm.Placed{False{}}, True{}}
        case Cm.Publish{}:
          Cm.Moved{Cm.NotPlaced{}, True{}}
        case Cm.Remove{}:
          Cm.Moved{Cm.Placed{True{}}, False{}}

# what the model's publish says of an outcome
def sp_out(o: Cm.Outcome) -> Cm.Out:
  match o:
    case Cm.Lands{w}:
      match w:
        case Cm.NoWarn{}:
          Cm.Landed{False{}}
        case Cm.SyncWarn{}:
          Cm.Landed{True{}}
        case Cm.RemoveWarn{}:
          Cm.Landed{True{}}
    case Cm.Fails{}:
      Cm.Failed{}

def sp_landed(o: Cm.Outcome) -> Bool:
  match o:
    case Cm.Lands{w}:
      True{}
    case Cm.Fails{}:
      False{}

# the index of the first failed publish among fs from n (n + the length
# when none failed)
def sp_first(fs: List<&2, Cm.Fate>, +n: Nat) -> Nat:
  match fs:
    case Nil{}:
      n
    case f <> rest:
      match f:
        case Cm.Wrote{o}:
          match o:
            case Cm.Fails{}:
              n
            case Cm.Lands{w}:
              sp_first(rest, 1n+n)
        case Cm.Noop{}:
          sp_first(rest, 1n+n)
        case Cm.Untried{}:
          sp_first(rest, 1n+n)

def sp_note(f: Cm.Fate, +k: Nat) -> Cm.Note:
  match f:
    case Cm.Noop{}:
      Cm.Untouched{}
    case Cm.Wrote{o}:
      match o:
        case Cm.Lands{w}:
          Cm.Written{}
        case Cm.Fails{}:
          Cm.Unwritten{}
    case Cm.Untried{}:
      Cm.Skipped{k}

def sp_notes(fs: List<&2, Cm.Fate>, +k: Nat) -> List<&2, Cm.Note>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      sp_note(f, k) <> sp_notes(rest, k)

def sp_counts.add(f: Cm.Fate, landed: Nat, failed: Nat, unwritten: Nat) -> (Nat & Nat) & Nat:
  match f:
    case Cm.Noop{}:
      ((landed, failed), unwritten)
    case Cm.Wrote{o}:
      match o:
        case Cm.Lands{w}:
          ((1n+landed, failed), unwritten)
        case Cm.Fails{}:
          ((landed, 1n+failed), 1n+unwritten)
    case Cm.Untried{}:
      ((landed, failed), 1n+unwritten)

# how many publishes landed, how many failed, how many files were not
# written
def sp_counts.of(f: Cm.Fate, c: (Nat & Nat) & Nat) -> (Nat & Nat) & Nat:
  match c:
    case ((l, x), u):
      sp_counts.add(f, l, x, u)

def sp_counts(fs: List<&2, Cm.Fate>) -> (Nat & Nat) & Nat:
  match fs:
    case Nil{}:
      ((0n, 0n), 0n)
    case f <> rest:
      sp_counts.of(f, sp_counts(rest))

def sp_answer.of(+fs: List<&2, Cm.Fate>, c: (Nat & Nat) & Nat) -> Cm.Verdict:
  match c:
    case ((l, x), u):
      match l:
        case 0n:
          match x:
            case 0n:
              Cm.Summary{sp_notes(fs, sp_first(fs, 0n)), Nat.is_gt(u, 0n)}
            case 1n+y:
              Cm.Failure{}
        case 1n+m:
          Cm.Summary{sp_notes(fs, sp_first(fs, 0n)), Nat.is_gt(u, 0n)}

# R3
def sp_answer(+fs: List<&2, Cm.Fate>) -> Cm.Verdict:
  sp_answer.of(fs, sp_counts(fs))

def sp_written(ns: List<&2, Cm.Note>, +n: Nat) -> List<&2, Nat>:
  match ns:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case Cm.Written{}:
          n <> sp_written(rest, 1n+n)
        case Cm.Untouched{}:
          sp_written(rest, 1n+n)
        case Cm.Unwritten{}:
          sp_written(rest, 1n+n)
        case Cm.Skipped{k}:
          sp_written(rest, 1n+n)

# the files a verdict reports written
def sp_reported(v: Cm.Verdict) -> List<&2, Nat>:
  match v:
    case Cm.Failure{}:
      Nil{}
    case Cm.Summary{ns, p}:
      sp_written(ns, 0n)

def sp_untried(fs: List<&2, Cm.Doc>) -> List<&2, Cm.Fate>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      Cm.Untried{} <> sp_untried(rest)

def sp_fates.pick(+o: Cm.Outcome, go: List<&2, Cm.Fate>, stop: List<&2, Cm.Fate>) -> List<&2, Cm.Fate>:
  match o:
    case Cm.Lands{w}:
      Cm.Wrote{o} <> go
    case Cm.Fails{}:
      Cm.Wrote{o} <> stop

# the fates of the model's files: each published until the first failure,
# the rest untried
def sp_fates(fs: List<&2, Cm.Doc>) -> List<&2, Cm.Fate>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> +rest:
      match f:
        case Cm.Doc{k, c, x}:
          sp_fates.pick(sp_outcome(sp_pub(k, x)), sp_fates(rest), sp_untried(rest))

# R5: membership by text
def sp_in(+d: String, s: List<&2, String>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(LawsBase.text_same(x, d), sp_in(d, rest))

def sp_if(b: Bool, t: Cm.Gate, f: Cm.Gate) -> Cm.Gate:
  match b:
    case True{}:
      t
    case False{}:
      f

# R4
def sp_gate(b: Cm.Base, d: Cm.Disk) -> Cm.Gate:
  match b:
    case Cm.OnSeen{s}:
      match d:
        case Cm.Absent{}:
          Cm.Proceed{}
        case Cm.Present{g, e}:
          sp_if(sp_in(g, s), Cm.Proceed{}, Cm.Unseen{})
    case Cm.OnBytes{}:
      match d:
        case Cm.Absent{}:
          Cm.Stale{}
        case Cm.Present{g, e}:
          sp_if(e, Cm.Proceed{}, Cm.Stale{})

def sp_without.keep(b: Bool, x: String, r: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      r
    case False{}:
      x <> r

def sp_without(+d: String, s: List<&2, String>) -> List<&2, String>:
  match s:
    case Nil{}:
      Nil{}
    case +x <> rest:
      sp_without.keep(LawsBase.text_same(x, d), x, sp_without(d, rest))

def sp_take8(n: Nat, s: List<&2, String>) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      match s:
        case Nil{}:
          Nil{}
        case x <> rest:
          x <> sp_take8(m, rest)

# R5
def sp_seen(+d: String, s: List<&2, String>) -> List<&2, String>:
  sp_take8(8n, d <> sp_without(d, s))

# R6: the name prefix of a target's temporary files
def sp_prefix(h: String) -> String:
  String.append(".eukhe-tmp-", String.append(h, "-"))

# p is a prefix of s, char by char
def sp_starts(p: String, s: String) -> Bool:
  match p:
    case SNil{}:
      True{}
    case SCon{c, q}:
      match s:
        case SNil{}:
          False{}
        case SCon{d, t}:
          Bool.and(Char.is_eq(c, d), sp_starts(q, t))

def sp_gone.keep(b: Bool, +n: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      n <> r
    case False{}:
      r

# R6: the entries a sweep removes
def sp_gone(+p: String, es: List<&2, Cm.Ent>, +n: Nat) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Cm.Ent{name, h}:
          sp_gone.keep(Bool.and(sp_starts(p, name), Bool.not(h)), n, sp_gone(p, rest, 1n+n))

# the model's entries of a directory: a temporary file of the target, of
# another target, or another file, by its name
def sp_sort.of(own: Bool, temp: Bool) -> Cm.Sort:
  match own:
    case True{}:
      Cm.Own{}
    case False{}:
      match temp:
        case True{}:
          Cm.Foreign{}
        case False{}:
          Cm.Plain{}

def sp_sort(+p: String, +name: String) -> Cm.Sort:
  sp_sort.of(sp_starts(p, name), sp_starts(".eukhe-tmp-", name))

def sp_temps(+p: String, es: List<&2, Cm.Ent>, +n: Nat) -> List<&2, Cm.Temp>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Cm.Ent{name, h}:
          Cm.Temp{n, sp_sort(p, name), h} <> sp_temps(p, rest, 1n+n)

def sp_ids(ts: List<&2, Cm.Temp>) -> List<&2, Nat>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      match t:
        case Cm.Temp{i, k, h}:
          i <> sp_ids(rest)

# The spelling of a request and of its reply, from the wire primitives
# (R7).

def sp_w_met(m: Cm.Met, rest: String) -> String:
  match m:
    case Cm.Met{c, t}:
      Wr.put_bool(c, Wr.put_bool(t, rest))

def sp_w_placed(x: Cm.Placed, rest: String) -> String:
  match x:
    case Cm.NotPlaced{}:
      Wr.put_nat(0n, rest)
    case Cm.Placed{s}:
      Wr.put_nat(1n, Wr.put_bool(s, rest))

def sp_w_pub(p: Cm.Pub, rest: String) -> String:
  match p:
    case Cm.Updated{x}:
      Wr.put_nat(0n, sp_w_placed(x, rest))
    case Cm.Deleted{r}:
      Wr.put_nat(1n, Wr.put_bool(r, rest))
    case Cm.Moved{x, r}:
      Wr.put_nat(2n, sp_w_placed(x, Wr.put_bool(r, rest)))

def sp_w_outcome(o: Cm.Outcome, rest: String) -> String:
  match o:
    case Cm.Lands{w}:
      match w:
        case Cm.NoWarn{}:
          Wr.put_nat(0n, Wr.put_nat(0n, rest))
        case Cm.SyncWarn{}:
          Wr.put_nat(0n, Wr.put_nat(1n, rest))
        case Cm.RemoveWarn{}:
          Wr.put_nat(0n, Wr.put_nat(2n, rest))
    case Cm.Fails{}:
      Wr.put_nat(1n, rest)

def sp_w_fate(f: Cm.Fate, rest: String) -> String:
  match f:
    case Cm.Noop{}:
      Wr.put_nat(0n, rest)
    case Cm.Wrote{o}:
      Wr.put_nat(1n, sp_w_outcome(o, rest))
    case Cm.Untried{}:
      Wr.put_nat(2n, rest)

def sp_w_base(b: Cm.Base, rest: String) -> String:
  match b:
    case Cm.OnSeen{xs}:
      Wr.put_nat(0n, Wr.put_list(~String, ~Wr.put_str, xs, rest))
    case Cm.OnBytes{}:
      Wr.put_nat(1n, rest)

def sp_w_disk(d: Cm.Disk, rest: String) -> String:
  match d:
    case Cm.Absent{}:
      Wr.put_nat(0n, rest)
    case Cm.Present{g, e}:
      Wr.put_nat(1n, Wr.put_str(g, Wr.put_bool(e, rest)))

def sp_w_ent(e: Cm.Ent, rest: String) -> String:
  match e:
    case Cm.Ent{n, h}:
      Wr.put_str(n, Wr.put_bool(h, rest))

def sp_w_req(q: FCm.Req, rest: String) -> String:
  match q:
    case FCm.QCheck{ms}:
      Wr.put_nat(0n, Wr.put_list(~Cm.Met, ~sp_w_met, ms, rest))
    case FCm.QPublish{p}:
      Wr.put_nat(1n, sp_w_pub(p, rest))
    case FCm.QAnswer{fs}:
      Wr.put_nat(2n, Wr.put_list(~Cm.Fate, ~sp_w_fate, fs, rest))
    case FCm.QGate{b, d}:
      Wr.put_nat(3n, sp_w_base(b, sp_w_disk(d, rest)))
    case FCm.QSeen{d, xs}:
      Wr.put_nat(4n, Wr.put_str(d, Wr.put_list(~String, ~Wr.put_str, xs, rest)))
    case FCm.QPrefix{h}:
      Wr.put_nat(5n, Wr.put_str(h, rest))
    case FCm.QSweep{h, es}:
      Wr.put_nat(6n, Wr.put_str(h, Wr.put_list(~Cm.Ent, ~sp_w_ent, es, rest)))

def sp_w_check(c: Cm.Check) -> String:
  match c:
    case Cm.Go{}:
      Wr.put_nat(0n, "")
    case Cm.Stop{at, why}:
      match why:
        case Cm.Changed{}:
          Wr.put_nat(1n, Wr.put_nat(at, Wr.put_nat(0n, "")))
        case Cm.Taken{}:
          Wr.put_nat(1n, Wr.put_nat(at, Wr.put_nat(1n, "")))

def sp_w_note(x: Cm.Note, rest: String) -> String:
  match x:
    case Cm.Untouched{}:
      Wr.put_nat(0n, rest)
    case Cm.Written{}:
      Wr.put_nat(1n, rest)
    case Cm.Unwritten{}:
      Wr.put_nat(2n, rest)
    case Cm.Skipped{k}:
      Wr.put_nat(3n, Wr.put_nat(k, rest))

def sp_w_verdict(v: Cm.Verdict) -> String:
  match v:
    case Cm.Failure{}:
      Wr.put_nat(0n, "")
    case Cm.Summary{ns, p}:
      Wr.put_nat(1n, Wr.put_list(~Cm.Note, ~sp_w_note, ns, Wr.put_bool(p, "")))

def sp_w_gate(g: Cm.Gate) -> String:
  match g:
    case Cm.Proceed{}:
      Wr.put_nat(0n, "")
    case Cm.Unseen{}:
      Wr.put_nat(1n, "")
    case Cm.Stale{}:
      Wr.put_nat(2n, "")

# the reply Rust reads: the spelled choice of the spec (R1-R6)
def sp_w_reply(q: FCm.Req) -> String:
  match q:
    case FCm.QCheck{ms}:
      sp_w_check(sp_check(ms, 0n))
    case FCm.QPublish{p}:
      sp_w_outcome(sp_outcome(p), "")
    case FCm.QAnswer{fs}:
      sp_w_verdict(sp_answer(fs))
    case FCm.QGate{b, d}:
      sp_w_gate(sp_gate(b, d))
    case FCm.QSeen{d, xs}:
      Wr.put_list(~String, ~Wr.put_str, sp_seen(d, xs), "")
    case FCm.QPrefix{h}:
      Wr.put_str(sp_prefix(h), "")
    case FCm.QSweep{h, es}:
      Wr.put_list(~Nat, ~Wr.put_nat, sp_gone(sp_prefix(h), es, 0n), "")

def sp_fit_strs(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(LawsBase.wire_fits(String.length(x)), sp_fit_strs(rest))

def sp_fit_ents(es: List<&2, Cm.Ent>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> rest:
      match e:
        case Cm.Ent{n, h}:
          Bool.and(LawsBase.wire_fits(String.length(n)), sp_fit_ents(rest))

def sp_fit_base(b: Cm.Base) -> Bool:
  match b:
    case Cm.OnSeen{+xs}:
      Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), sp_fit_strs(xs))
    case Cm.OnBytes{}:
      True{}

def sp_fit_disk(d: Cm.Disk) -> Bool:
  match d:
    case Cm.Absent{}:
      True{}
    case Cm.Present{g, e}:
      LawsBase.wire_fits(String.length(g))

# every number, length and count of the request fits the wire
def sp_fit_req(q: FCm.Req) -> Bool:
  match q:
    case FCm.QCheck{ms}:
      LawsBase.wire_fits(List.length(&2, Cm.Met, ms))
    case FCm.QPublish{p}:
      True{}
    case FCm.QAnswer{fs}:
      LawsBase.wire_fits(List.length(&2, Cm.Fate, fs))
    case FCm.QGate{b, d}:
      Bool.and(sp_fit_base(b), sp_fit_disk(d))
    case FCm.QSeen{d, +xs}:
      Bool.and(LawsBase.wire_fits(String.length(d)), Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), sp_fit_strs(xs)))
    case FCm.QPrefix{h}:
      LawsBase.wire_fits(String.length(h))
    case FCm.QSweep{h, +es}:
      Bool.and(LawsBase.wire_fits(String.length(h)), Bool.and(LawsBase.wire_fits(List.length(&2, Cm.Ent, es)), sp_fit_ents(es)))

# Laws: the choices
# -----------------

# LAW commit_check_spec (R1): the check of an edit stops at the first file
# that changed or whose move destination exists, and names why
# EXCLUDES: an edit that writes after a conflict, a move over an existing
#   file, a stop that names another file or reason
law commit_check_spec:
  for +ms: List<&2, Cm.Met>
  {Cm.check(ms) == sp_check(ms, 0n) : Cm.Check}

# LAW commit_check_is_conflict (R1, F1): on the model's files the check
# goes on exactly when no file changed (edit_all_or_nothing_on_conflict)
# EXCLUDES: a real check that drifts from the model's phase 1
law commit_check_is_conflict:
  for +fs: List<&2, Cm.Doc>
  {sp_go(Cm.check(sp_mets(fs))) == Bool.not(Cm.conflict(fs)) : Bool}

# LAW commit_outcome_spec (R2): what one publish did
# EXCLUDES: a failed publish reported landed (or the reverse), a lost
#   warning, a move that lost its source reported clean
law commit_outcome_spec:
  for +p: Cm.Pub
  {Cm.outcome(p) == sp_outcome(p) : Cm.Outcome}

# LAW commit_outcome_is_publish (R2, F9): the outcome of the facts a fault
# stands for is the model's publish of that file
# EXCLUDES: a real publish that drifts from the model's `publish`
law commit_outcome_is_publish:
  for +k: Cm.Op
  for +c: Bool
  for +x: Cm.Fault
  {sp_out(Cm.outcome(sp_pub(k, x))) == Cm.publish(Cm.Doc{k, c, x}) : Cm.Out}

# LAW commit_answer_spec (R3): the reply of an edit from its staged files
# EXCLUDES: an error after a file landed (its new tag lost), an answer
#   after nothing landed, a file reported written that failed, an untried
#   file blamed on another file than the first failure, a lost partial flag
law commit_answer_spec:
  for +fs: List<&2, Cm.Fate>
  {Cm.answer(fs) == sp_answer(fs) : Cm.Verdict}

# LAW commit_answer_is_reply (R3, F1): on the model's files with no
# conflict, published until the first failure, the reply reports written
# exactly the files the model's reply reports applied
# EXCLUDES: a real reply that drifts from edit_reports_what_landed
law commit_answer_is_reply:
  for +fs: List<&2, Cm.Doc>
  for clean: {Cm.conflict(fs) == False{} : Bool}
  {sp_reported(Cm.answer(sp_fates(fs))) == Cm.reported(Cm.reply(fs)) : List<&2, Nat>}

# LAW commit_gate_spec (R4): whether the write tool may replace a file
# EXCLUDES: a write over bytes the session never saw, a refused create, a
#   write over bytes other than the expected ones, a digest compared by
#   prefix
law commit_gate_spec:
  for +b: Cm.Base
  for +d: Cm.Disk
  {Cm.gate(b, d) == sp_gate(b, d) : Cm.Gate}

# LAW commit_seen_spec (R5): the seen versions after the session sees one
# EXCLUDES: a duplicate, the newest lost or not first, more than 8 kept, an
#   older version dropped while room is left
law commit_seen_spec:
  for +d: String
  for +s: List<&2, String>
  {Cm.seen(d, s) == sp_seen(d, s) : List<&2, String>}

# LAW commit_prefix_spec (R6): the name prefix of a target's temporary
# files
# EXCLUDES: a prefix that another target's files share, one a sweep of
#   this target does not match
law commit_prefix_spec:
  for +h: String
  {Cm.prefix(h) == sp_prefix(h) : String}

# LAW commit_sweep_spec (R6): a sweep removes exactly the entries named
# with the target's prefix that no live writer holds
# EXCLUDES: a held temporary file removed, another target's temporary file
#   or another file removed, a free one kept
law commit_sweep_spec:
  for +h: String
  for +es: List<&2, Cm.Ent>
  {Cm.gone(h, es) == sp_gone(sp_prefix(h), es, 0n) : List<&2, Nat>}

# LAW commit_sweep_is_model (R6, F10): the sweep removes the entries the
# model's sweep removes, each entry sorted by its name
# EXCLUDES: a real sweep that drifts from temp_sweep_only_own and
#   temp_sweep_never_held
law commit_sweep_is_model:
  for +h: String
  for +es: List<&2, Cm.Ent>
  {Cm.gone(h, es) == sp_ids(Cm.sweep(sp_temps(sp_prefix(h), es, 0n))) : List<&2, Nat>}

# LAW commit_choices_example (R1-R6): anchor: a second file whose
# destination exists stops the edit at it; a move that kept its source
# lands with that warning; an edit whose first publish failed and then
# untried files is an error, one where a publish landed first names the
# failed file; a write over a seen digest goes on, over an unseen one is
# refused; a sweep keeps a held file, another target's and another file
# EXCLUDES: the spec read one way off
law commit_choices_example:
  {Cm.check([Cm.Met{False{}, False{}}, Cm.Met{False{}, True{}}, Cm.Met{True{}, False{}}]) == Cm.Stop{1n, Cm.Taken{}} : Cm.Check} & {Cm.outcome(Cm.Moved{Cm.Placed{False{}}, False{}}) == Cm.Lands{Cm.RemoveWarn{}} : Cm.Outcome} & {[Cm.answer([Cm.Wrote{Cm.Fails{}}, Cm.Untried{}]), Cm.answer([Cm.Noop{}, Cm.Wrote{Cm.Lands{Cm.NoWarn{}}}, Cm.Wrote{Cm.Fails{}}, Cm.Untried{}])] == [Cm.Failure{}, Cm.Summary{[Cm.Untouched{}, Cm.Written{}, Cm.Unwritten{}, Cm.Skipped{2n}], True{}}] : List<&2, Cm.Verdict>} & {[Cm.gate(Cm.OnSeen{["ab", "cd"]}, Cm.Present{"cd", False{}}), Cm.gate(Cm.OnSeen{["ab"]}, Cm.Present{"a", False{}})] == [Cm.Proceed{}, Cm.Unseen{}] : List<&2, Cm.Gate>} & {Cm.gone("beef", [Cm.Ent{".eukhe-tmp-beef-12-0", False{}}, Cm.Ent{".eukhe-tmp-beef-13-0", True{}}, Cm.Ent{"o", False{}}, Cm.Ent{".eukhe-tmp-dead-1-0", False{}}]) == [0n] : List<&2, Nat>}

# Laws: the entry (R7)
# --------------------

# LAW commit_entry_answers (R7): the doc_commit entry answers every
# request Rust spells, every length and count within the wire, with the
# spelled choice of the spec
# EXCLUDES: a field misread, swapped or dropped; a request answered with
#   another request's choice, a default, or a reply spelled otherwise
law commit_entry_answers:
  for +q: FCm.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FCm.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW commit_entry_reads (R7): the entry's decoder reads a spelled request
# back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law commit_entry_reads:
  for +q: FCm.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FCm.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FCm.Req>}

# LAW commit_entry_exact (R7): every input the entry does not answer with
# the error form is a spelled request that fits the wire
# EXCLUDES: a choice made on input that is no request (an unknown tag, a
#   malformed field, input left over)
law commit_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FCm.ffi(s)) == False{} : Bool}
  exs r: FCm.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW commit_entry_refuses (R7): every error the entry answers is exactly
# `E doc_commit: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law commit_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FCm.ffi(s)) == True{} : Bool}
  {FCm.ffi(s) == Wr.err("doc_commit: malformed request") : String}

# LAW commit_entry_example (R7): anchor: the wire strings Rust sends and
# the replies it reads; an unknown tag and input left over
# EXCLUDES: tags in another order, a field order other than Rust's
law commit_entry_example:
  {[FCm.ffi("0,3,FFFTTF"), FCm.ffi("1,2,1,TF"), FCm.ffi("2,4,0,1,0,0,1,1,2,"), FCm.ffi("3,0,2,2,ab2,cd1,2,cdF"), FCm.ffi("3,1,0,"), FCm.ffi("4,1,b3,1,a1,b1,c"), FCm.ffi("5,4,beef"), FCm.ffi("6,4,beef4,20,.eukhe-tmp-beef-12-0F20,.eukhe-tmp-beef-13-0T1,oF19,.eukhe-tmp-dead-1-0F"), FCm.ffi("7,"), FCm.ffi("5,1,ax")] == ["1,1,1,", "0,2,", "1,4,0,1,2,3,2,T", "0,", "2,", "3,1,b1,a1,c", "16,.eukhe-tmp-beef-", "1,0,", Wr.err("doc_commit: malformed request"), Wr.err("doc_commit: malformed request")] : List<&2, String>}

# (F2) The write tool, pinned
# ---------------------------
# The model's unseen and saw, which write_never_loses_unseen and
# write_writes_seen take as given, stated outright (a mutant that sees
# every version, or keeps 9, or drops the newest, passed those laws).

def sp_nmem(+v: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(Nat.is_eq(x, v), sp_nmem(v, rest))

def sp_ndrop.keep(b: Bool, x: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      r
    case False{}:
      x <> r

def sp_ndrop(+v: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      sp_ndrop.keep(Nat.is_eq(x, v), x, sp_ndrop(v, rest))

def sp_unseen(d: Maybe<&2, Nat>, +s: List<&2, Nat>) -> Bool:
  match d:
    case None{}:
      False{}
    case Some{v}:
      Bool.not(sp_nmem(v, s))

# LAW write_unseen_spec (F2): the disk holds an unseen version exactly when
# it holds a version not among the seen ones (no file is never unseen)
# EXCLUDES: a write over a version never seen, a refused create, a seen
#   version refused
law write_unseen_spec:
  for +d: Maybe<&2, Nat>
  for +s: List<&2, Nat>
  {Cm.unseen(d, s) == sp_unseen(d, s) : Bool}

# LAW write_saw_spec (F2): after the session sees v, the seen versions are
# v, then the earlier ones without v, the last 8
# EXCLUDES: the newest lost or not first, a duplicate, more than 8 kept
law write_saw_spec:
  for +v: Nat
  for +s: List<&2, Nat>
  {Cm.saw(v, s) == List.take(&2, Nat, v <> sp_ndrop(v, s), 8n) : List<&2, Nat>}
