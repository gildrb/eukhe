# eukhe: the laws of area staging

import Base
import ../bend/staging.bend as Sg
import ../bend/listing.bend as Ls
import ../bend/ffi_staging.bend as FSg
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# Staging, sweep and listing (bend/staging.bend): every input is free: any
# directory entries with any names, any nodes a sweep may meet (held or
# not, stale or not, reached or not, of any sort), any sessions directory.

# LAW publish_never_overwrites: a publish to a name that an entry has fails and changes nothing:
# a rename never replaces an existing target, not even an empty directory
law publish_never_overwrites:
  for +s: Nat
  for +t: Nat
  for +es: List<&2, Sg.Entry>
  for taken: {Sg.has(t, es) == True{} : Bool}
  {Sg.publish(s, t, es) == Sg.Pub{False{}, es} : Sg.Pub}

# LAW publish_moves: a publish to a free name moves the storage
law publish_moves:
  for +s: Nat
  for +t: Nat
  for +es: List<&2, Sg.Entry>
  for free: {Sg.has(t, es) == False{} : Bool}
  {Sg.Pub.ok(Sg.publish(s, t, es)) == True{} : Bool}

# LAW sweep_never_live: a sweep never removes an entry a live process holds the lock of
law sweep_never_live:
  for +pre: List<&2, Sg.Node>
  for +i: Nat
  for +k: Sg.Sort
  for +s: Bool
  for +o: Bool
  for +post: List<&2, Sg.Node>
  {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, True{}, s, o} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}

# LAW sweep_never_young: a sweep never removes an entry touched within the day
law sweep_never_young:
  for +pre: List<&2, Sg.Node>
  for +i: Nat
  for +k: Sg.Sort
  for +h: Bool
  for +o: Bool
  for +post: List<&2, Sg.Node>
  {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, h, False{}, o} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}

# LAW sweep_stays_out: a sweep never removes an entry it does not reach (inside a storage
# or a leftover, behind a symlink)
law sweep_stays_out:
  for +pre: List<&2, Sg.Node>
  for +i: Nat
  for +k: Sg.Sort
  for +h: Bool
  for +s: Bool
  for +post: List<&2, Sg.Node>
  {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, h, s, False{}} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}

# LAW sweep_reaches_every_depth: a sweep removes every free, stale leftover it reaches, at any depth
law sweep_reaches_every_depth:
  for +pre: List<&2, Sg.Node>
  for +i: Nat
  for +k: Sg.Sort
  for +post: List<&2, Sg.Node>
  for sw: {Sg.Sort.swept(k) == True{} : Bool}
  {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, False{}, True{}, True{}} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.Node{i, k, False{}, True{}, True{}} <> Sg.sweep(post)) : List<&2, Sg.Node>}

# LAW list_one_location: a session never shows twice: no name is listed both as a storage
# and as a legacy file
law list_one_location:
  for +es: List<&2, Sg.Ent>
  for +n: Nat
  {Bool.and(Sg.mem(n, Sg.durables(es)), Sg.mem(n, Sg.legacies(es, es))) == False{} : Bool}

# LAW list_import_lists_storage: after the import of the legacy file with stem s, s is listed as a
# storage (and so, by list_one_location, no more as a legacy file)
law list_import_lists_storage:
  for +es: List<&2, Sg.Ent>
  for +s: Nat
  {Sg.mem(s, Sg.durables(Sg.imported(s, es))) == True{} : Bool}

# LAW list_import_keeps_others: an import changes the listing of no other name
law list_import_keeps_others:
  for +es: List<&2, Sg.Ent>
  for +s: Nat
  for +n: Nat
  for ne: {Nat.is_eq(s, n) == False{} : Bool}
  {Sg.mem(n, Sg.listing(Sg.imported(s, es))) == Sg.mem(n, Sg.listing(es)) : Bool}

# ---- staging: the real rule ----

# LAWS: the real rule of bend/staging.bend (its section "The real rule")
# and the entry of the compiled core that runs it with bend/listing.bend
# (bend/ffi_staging.bend; crates/eukhe-core/src/durable/staging.rs,
# discovery.rs). The Rust gathers the facts (directory listings, lock
# probes, modification times, cwds) and performs what the rule answers.
# Each law is an open claim; PROOF.bend proves them (as Staging.<law>)
# with the lemmas of proof/staging/. The listing's laws: laws/listing.bend.
#
# R1: a publish moves the staged storage only when its rename without
#     replacement met no entry at the target: an entry there stays.
# R2: the sweep never removes an entry a live process holds the lock of,
#     nor one that it, or a direct entry of it, changed within a day.
# R3: the sweep enters every directory but a storage (main.jsonl), a
#     symlink and a leftover; it judges exactly the staging directories
#     and tombstones (`.<target>.<label>-<uuid>`, labels import, fork,
#     deleted, a 32-digit lowercase hex uuid, a target not empty) and the
#     lock files of such names whose directory is gone.
# R4: a judged free stale leftover goes: a directory with its lock file,
#     an orphan lock file; nothing else does.
# R8: the entry answers every request Rust spells with the spelled
#     decision of the real rule; any other input gets the error form.
# Every input is free: any names (UTF-8 or not), entry types, listings,
# lock probes, times, cwds.

# Spec helpers: the names the sweep judges
# ----------------------------------------

# c is one of the chars of cs
def sp_in(+c: Char, cs: String) -> Bool:
  match cs:
    case SNil{}:
      False{}
    case SCon{x, t}:
      Bool.or(Char.is_eq(c, x), sp_in(c, t))

def sp_if(ok: Bool, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      m
    case False{}:
      None{}

# s after the prefix p, when s starts with p
def sp_unprefix(p: String, s: String) -> Maybe<&2, String>:
  match p:
    case SNil{}:
      Some{s}
    case SCon{x, pt}:
      match s:
        case SNil{}:
          None{}
        case SCon{y, st}:
          sp_if(Char.is_eq(x, y), sp_unprefix(pt, st))

# the text before the last '.' of a text, and the text after it
type SpCut is Data:
  SpCut{before: String, after: String}

def sp_cut.cons(c: Char, p: SpCut) -> Maybe<&2, SpCut>:
  match p:
    case SpCut{b, a}:
      Some{SpCut{SCon{c, b}, a}}

def sp_cut.dot(d: Bool, t: String) -> Maybe<&2, SpCut>:
  match d:
    case True{}:
      Some{SpCut{SNil{}, t}}
    case False{}:
      None{}

def sp_cut.put(r: Maybe<&2, SpCut>, d: Bool, c: Char, t: String) -> Maybe<&2, SpCut>:
  match r:
    case Some{p}:
      sp_cut.cons(c, p)
    case None{}:
      sp_cut.dot(d, t)

# w split at its last '.'
def sp_cut(w: String) -> Maybe<&2, SpCut>:
  match w:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      sp_cut.put(sp_cut(t), Char.is_eq(c, '.'), c, t)

# s is n lowercase hex digits
def sp_hexn(n: Nat, s: String) -> Bool:
  match n:
    case 0n:
      String.is_empty(s)
    case 1n+k:
      match s:
        case SNil{}:
          False{}
        case SCon{c, t}:
          Bool.and(sp_in(c, "0123456789abcdef"), sp_hexn(k, t))

def sp_uuid(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      sp_hexn(32n, s)

# the part after the last '.': `import-`, `fork-` or `deleted-`, then a uuid
def sp_tail(+a: String) -> Bool:
  Bool.or(sp_uuid(sp_unprefix("import-", a)), Bool.or(sp_uuid(sp_unprefix("fork-", a)), sp_uuid(sp_unprefix("deleted-", a))))

def sp_swept.cut(m: Maybe<&2, SpCut>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{p}:
      match p:
        case SpCut{b, a}:
          Bool.and(Bool.not(String.is_empty(b)), sp_tail(a))

# s is `.<target>.<label>-<uuid>`, the target not empty
def sp_swept(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.and(Char.is_eq(c, '.'), sp_swept.cut(sp_cut(t)))

# the labels of the names Rust mints (staging.rs `staging_dir`: import and
# fork; the daemon's saved-session delete: deleted)
type SpLab is Data:
  SpImport{}
  SpFork{}
  SpDeleted{}

def sp_label(l: SpLab) -> String:
  match l:
    case SpImport{}:
      "import"
    case SpFork{}:
      "fork"
    case SpDeleted{}:
      "deleted"

# the name Rust mints: `.<target>.<label>-<uuid>`
def sp_mint(t: String, l: SpLab, id: String) -> String:
  SCon{'.', String.append(t, SCon{'.', String.append(sp_label(l), SCon{'-', id})})}

# Spec helpers: the sweep
# -----------------------

def sp_met.dir(sw: Bool, main: Bool) -> Sg.Met:
  match sw:
    case True{}:
      Sg.MLeftover{}
    case False{}:
      match main:
        case True{}:
          Sg.MKeep{}
        case False{}:
          Sg.MDescend{}

def sp_met.lock(sw: Bool, there: Bool) -> Sg.Met:
  match sw:
    case True{}:
      match there:
        case True{}:
          Sg.MKeep{}
        case False{}:
          Sg.MOrphan{}
    case False{}:
      Sg.MKeep{}

def sp_met.file(m: Maybe<&2, String>, all: List<&2, Sg.Seen>) -> Sg.Met:
  match m:
    case None{}:
      Sg.MKeep{}
    case Some{+x}:
      sp_met.lock(sp_swept(x), LawsBase.text_has_name(x, all))

def sp_met.utf(k: Sg.Form, +s: String, all: List<&2, Sg.Seen>) -> Sg.Met:
  match k:
    case Sg.KDir{main}:
      sp_met.dir(sp_swept(s), main)
    case Sg.KFile{}:
      sp_met.file(LawsBase.text_unsuffix(".lock", s), all)
    case Sg.KOther{}:
      Sg.MKeep{}

def sp_met.raw(k: Sg.Form) -> Sg.Met:
  match k:
    case Sg.KDir{main}:
      sp_met.dir(False{}, main)
    case Sg.KFile{}:
      Sg.MKeep{}
    case Sg.KOther{}:
      Sg.MKeep{}

# what the sweep does with the entry e of the listing all (R3): a
# directory with a swept name is judged; any other directory is kept when
# it holds main.jsonl and entered otherwise; a file `<x>.lock`, x a swept
# name, is judged when no entry has the name x; everything else is kept
def sp_met(e: Sg.Seen, all: List<&2, Sg.Seen>) -> Sg.Met:
  match e:
    case Sg.Seen{n, k}:
      match n:
        case Sg.Utf{s}:
          sp_met.utf(k, s, all)
        case Sg.Raw{}:
          sp_met.raw(k)

def sp_meet.go(es: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> List<&2, Sg.Met>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      sp_met(e, all) <> sp_meet.go(rest, all)

def sp_meet(+es: List<&2, Sg.Seen>) -> List<&2, Sg.Met>:
  sp_meet.go(es, es)

# a plain directory: no swept name, no main.jsonl (R3)
def sp_plain.k(k: Sg.Form, sw: Bool) -> Bool:
  match k:
    case Sg.KDir{main}:
      Bool.and(Bool.not(sw), Bool.not(main))
    case Sg.KFile{}:
      False{}
    case Sg.KOther{}:
      False{}

def sp_plain(e: Sg.Seen) -> Bool:
  match e:
    case Sg.Seen{n, k}:
      match n:
        case Sg.Utf{s}:
          sp_plain.k(k, sp_swept(s))
        case Sg.Raw{}:
          sp_plain.k(k, False{})

def sp_plains(es: List<&2, Sg.Seen>) -> List<&2, Bool>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      sp_plain(e) <> sp_plains(rest)

def sp_descend(m: Sg.Met) -> Bool:
  match m:
    case Sg.MKeep{}:
      False{}
    case Sg.MDescend{}:
      True{}
    case Sg.MLeftover{}:
      False{}
    case Sg.MOrphan{}:
      False{}

def sp_descends(ms: List<&2, Sg.Met>) -> List<&2, Bool>:
  match ms:
    case Nil{}:
      Nil{}
    case m <> rest:
      sp_descend(m) <> sp_descends(rest)

# t is at least a day (86400 s) before now, a time ahead of now is fresh
# (R2): the age now - t is at least a day
def sp_old(+now: Sg.Time, t: Sg.Time) -> Bool:
  match now:
    case Sg.Time{+ns, nn}:
      match t:
        case Sg.Time{ts, tn}:
          +d = Nat.add(ts, 86400n)
          Bool.or(Nat.is_lt(d, ns), Bool.and(Nat.is_eq(d, ns), Nat.is_le(tn, nn)))

# every time of ts is at least a day before now
def sp_all_old(+now: Sg.Time, ts: List<&2, Sg.Time>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case t <> rest:
      Bool.and(sp_old(now, t), sp_all_old(now, rest))

def sp_judge.free(c: Sg.Cand, l: Sg.Lock) -> Sg.Plan:
  match c:
    case Sg.CDir{}:
      match l:
        case Sg.LHeld{}:
          Sg.PKeep{}
        case Sg.LFree{}:
          Sg.PRmDirLock{}
        case Sg.LAbsent{}:
          Sg.PRmDir{}
    case Sg.CLock{}:
      match l:
        case Sg.LHeld{}:
          Sg.PKeep{}
        case Sg.LFree{}:
          Sg.PRmFile{}
        case Sg.LAbsent{}:
          Sg.PKeep{}

def sp_judge.go(old: Bool, c: Sg.Cand, l: Sg.Lock) -> Sg.Plan:
  match old:
    case True{}:
      sp_judge.free(c, l)
    case False{}:
      Sg.PKeep{}

# the plan for a judged entry (R2, R4): held or touched within a day: keep;
# else a directory goes with its lock file (when one is there), an orphan
# lock file goes (when it is still there)
def sp_judge(c: Sg.Cand, l: Sg.Lock, +now: Sg.Time, own: Sg.Time, inner: List<&2, Sg.Time>) -> Sg.Plan:
  sp_judge.go(sp_all_old(now, own <> inner), c, l)

# a plan removes something
def sp_removes(p: Sg.Plan) -> Bool:
  match p:
    case Sg.PKeep{}:
      False{}
    case Sg.PRmDir{}:
      True{}
    case Sg.PRmDirLock{}:
      True{}
    case Sg.PRmFile{}:
      True{}

# the model's sort of a judged entry: a leftover, or a lock file whose
# directory is gone
def sp_sort(c: Sg.Cand) -> Sg.Sort:
  match c:
    case Sg.CDir{}:
      Sg.Leftover{}
    case Sg.CLock{}:
      Sg.Lock{False{}}

def sp_held(l: Sg.Lock) -> Bool:
  match l:
    case Sg.LHeld{}:
      True{}
    case Sg.LFree{}:
      False{}
    case Sg.LAbsent{}:
      False{}

# a lock probe the model has a node for: an orphan lock file that is gone
# is no node
def sp_probed(c: Sg.Cand, l: Sg.Lock) -> Bool:
  match c:
    case Sg.CDir{}:
      True{}
    case Sg.CLock{}:
      match l:
        case Sg.LHeld{}:
          True{}
        case Sg.LFree{}:
          True{}
        case Sg.LAbsent{}:
          False{}

def sp_moved(v: Sg.Verdict) -> Bool:
  match v:
    case Sg.Moved{}:
      True{}
    case Sg.Taken{}:
      False{}

# Spec helpers: the wire
# ----------------------
# Spellers of the requests and replies of bend/ffi_staging.bend, composed
# of the wire primitives only (their round trips: laws/wire.bend).

def sp_w_name(n: Sg.Name, rest: String) -> String:
  match n:
    case Sg.Utf{s}:
      Wr.put_nat(0n, Wr.put_str(s, rest))
    case Sg.Raw{}:
      Wr.put_nat(1n, rest)

def sp_w_form(k: Sg.Form, rest: String) -> String:
  match k:
    case Sg.KDir{m}:
      Wr.put_nat(0n, Wr.put_bool(m, rest))
    case Sg.KFile{}:
      Wr.put_nat(1n, rest)
    case Sg.KOther{}:
      Wr.put_nat(2n, rest)

def sp_w_seen(e: Sg.Seen, rest: String) -> String:
  match e:
    case Sg.Seen{n, k}:
      sp_w_name(n, sp_w_form(k, rest))

def sp_w_time(t: Sg.Time, rest: String) -> String:
  match t:
    case Sg.Time{s, n}:
      Wr.put_nat(s, Wr.put_nat(n, rest))

def sp_w_cwd(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{s}:
      Wr.put_nat(1n, Wr.put_str(s, rest))

def sp_w_obs(o: Ls.Obs, rest: String) -> String:
  match o:
    case Ls.Obs{e, c, ts}:
      sp_w_seen(e, sp_w_cwd(c, Wr.put_list(~Sg.Time, ~sp_w_time, ts, rest)))

def sp_w_cand(c: Sg.Cand, rest: String) -> String:
  match c:
    case Sg.CDir{}:
      Wr.put_nat(0n, rest)
    case Sg.CLock{}:
      Wr.put_nat(1n, rest)

def sp_w_lock(l: Sg.Lock, rest: String) -> String:
  match l:
    case Sg.LHeld{}:
      Wr.put_nat(0n, rest)
    case Sg.LFree{}:
      Wr.put_nat(1n, rest)
    case Sg.LAbsent{}:
      Wr.put_nat(2n, rest)

# a request, as Rust writes it
def sp_w_req(r: FSg.Req, rest: String) -> String:
  match r:
    case FSg.Publish{b}:
      Wr.put_nat(0n, Wr.put_bool(b, rest))
    case FSg.Meet{es}:
      Wr.put_nat(1n, Wr.put_list(~Sg.Seen, ~sp_w_seen, es, rest))
    case FSg.Judge{c, l, now, own, inner}:
      Wr.put_nat(2n, sp_w_cand(c, sp_w_lock(l, sp_w_time(now, sp_w_time(own, Wr.put_list(~Sg.Time, ~sp_w_time, inner, rest))))))
    case FSg.Scan{es}:
      Wr.put_nat(3n, Wr.put_list(~Sg.Seen, ~sp_w_seen, es, rest))
    case FSg.Rows{os}:
      Wr.put_nat(4n, Wr.put_list(~Ls.Obs, ~sp_w_obs, os, rest))

def sp_w_verdict(v: Sg.Verdict, rest: String) -> String:
  match v:
    case Sg.Moved{}:
      Wr.put_nat(0n, rest)
    case Sg.Taken{}:
      Wr.put_nat(1n, rest)

def sp_w_met(m: Sg.Met, rest: String) -> String:
  match m:
    case Sg.MKeep{}:
      Wr.put_nat(0n, rest)
    case Sg.MDescend{}:
      Wr.put_nat(1n, rest)
    case Sg.MLeftover{}:
      Wr.put_nat(2n, rest)
    case Sg.MOrphan{}:
      Wr.put_nat(3n, rest)

def sp_w_plan(p: Sg.Plan, rest: String) -> String:
  match p:
    case Sg.PKeep{}:
      Wr.put_nat(0n, rest)
    case Sg.PRmDir{}:
      Wr.put_nat(1n, rest)
    case Sg.PRmDirLock{}:
      Wr.put_nat(2n, rest)
    case Sg.PRmFile{}:
      Wr.put_nat(3n, rest)

def sp_w_pick(p: Ls.Pick, rest: String) -> String:
  match p:
    case Ls.PSkip{}:
      Wr.put_nat(0n, rest)
    case Ls.PStore{s}:
      Wr.put_nat(1n, Wr.put_str(s, rest))
    case Ls.PLegacy{s}:
      Wr.put_nat(2n, Wr.put_str(s, rest))

def sp_w_row(r: Ls.Row, rest: String) -> String:
  match r:
    case Ls.Row{i, p, t}:
      Wr.put_nat(i, sp_w_pick(p, sp_w_time(t, rest)))

# the reply to a request: the real rule's decision, as Rust reads it
def sp_w_reply(r: FSg.Req) -> String:
  match r:
    case FSg.Publish{b}:
      sp_w_verdict(Sg.settle(b), "")
    case FSg.Meet{es}:
      Wr.put_list(~Sg.Met, ~sp_w_met, Sg.meet(es), "")
    case FSg.Judge{c, l, now, own, inner}:
      sp_w_plan(Sg.judge(c, l, now, own, inner), "")
    case FSg.Scan{es}:
      Wr.put_list(~Ls.Pick, ~sp_w_pick, Ls.scan(es), "")
    case FSg.Rows{os}:
      Wr.put_list(~Ls.Row, ~sp_w_row, Ls.rows(os), "")

# what fits the wire: every number, length and count of a request
def sp_fit_str(+s: String) -> Bool:
  LawsBase.wire_fits(String.length(s))

def sp_fit_seen(e: Sg.Seen) -> Bool:
  match e:
    case Sg.Seen{n, k}:
      match n:
        case Sg.Utf{s}:
          sp_fit_str(s)
        case Sg.Raw{}:
          True{}

def sp_fit_seens.all(es: List<&2, Sg.Seen>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(sp_fit_seen(e), sp_fit_seens.all(rest))

def sp_fit_seens(+es: List<&2, Sg.Seen>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Sg.Seen, es)), sp_fit_seens.all(es))

def sp_fit_time(t: Sg.Time) -> Bool:
  match t:
    case Sg.Time{s, n}:
      Bool.and(LawsBase.wire_fits(s), LawsBase.wire_fits(n))

def sp_fit_times.all(ts: List<&2, Sg.Time>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case t <> rest:
      Bool.and(sp_fit_time(t), sp_fit_times.all(rest))

def sp_fit_times(+ts: List<&2, Sg.Time>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Sg.Time, ts)), sp_fit_times.all(ts))

def sp_fit_cwd(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      sp_fit_str(s)

def sp_fit_obs(o: Ls.Obs) -> Bool:
  match o:
    case Ls.Obs{e, c, ts}:
      Bool.and(sp_fit_seen(e), Bool.and(sp_fit_cwd(c), sp_fit_times(ts)))

def sp_fit_obss.all(os: List<&2, Ls.Obs>) -> Bool:
  match os:
    case Nil{}:
      True{}
    case o <> rest:
      Bool.and(sp_fit_obs(o), sp_fit_obss.all(rest))

def sp_fit_obss(+os: List<&2, Ls.Obs>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Ls.Obs, os)), sp_fit_obss.all(os))

def sp_fit_req(r: FSg.Req) -> Bool:
  match r:
    case FSg.Publish{b}:
      True{}
    case FSg.Meet{es}:
      sp_fit_seens(es)
    case FSg.Judge{c, l, now, own, inner}:
      Bool.and(sp_fit_time(now), Bool.and(sp_fit_time(own), sp_fit_times(inner)))
    case FSg.Scan{es}:
      sp_fit_seens(es)
    case FSg.Rows{os}:
      sp_fit_obss(os)

# Laws: publish (R1)
# ------------------

# LAW publish_settles (R1): a publish is taken exactly when its rename without replacement
# met an entry at the target, and moved otherwise
# EXCLUDES: a publish reported moved over an entry it did not replace (or
#   the reverse), a constant verdict
law publish_settles:
  for +b: Bool
  {sp_moved(Sg.settle(b)) == Bool.not(b) : Bool}

# LAW publish_settle_refines (R1): the verdict of a rename that met the entries es of the
# parent is the model's publish: moved exactly when the model moves
# EXCLUDES: a real verdict that differs from the model the laws
#   publish_never_overwrites and publish_moves are about
law publish_settle_refines:
  for +s: Nat
  for +t: Nat
  for +es: List<&2, Sg.Entry>
  {sp_moved(Sg.settle(Sg.has(t, es))) == Sg.Pub.ok(Sg.publish(s, t, es)) : Bool}

# Laws: the sweep (R2, R3, R4)
# ----------------------------

# LAW meet_exact (R3): the sweep's class of every entry of a listing is the spec's, in order
# EXCLUDES: a storage entered, a symlink followed, a leftover entered or
#   kept, a staging name misread (another label, an uppercase or short
#   uuid, an empty target), a lock file judged beside its directory or a
#   Raw name judged, an entry lost, added or moved
law meet_exact:
  for +es: List<&2, Sg.Seen>
  {Sg.meet(es) == sp_meet(es) : List<&2, Sg.Met>}

# LAW meet_minted_leftover (R3): a directory with a name Rust mints for a staging directory
# or a tombstone is judged, whatever it holds and whatever the target
# EXCLUDES: a spec of swept names narrower than what Rust mints (a target
#   with dots or dashes, one of the labels)
law meet_minted_leftover:
  for +t: String
  for +l: SpLab
  for +id: String
  for +m: Bool
  for full: {String.is_empty(t) == False{} : Bool}
  for u: {sp_hexn(32n, id) == True{} : Bool}
  {Sg.meet([Sg.Seen{Sg.Utf{sp_mint(t, l, id)}, Sg.KDir{m}}]) == [Sg.MLeftover{}] : List<&2, Sg.Met>}

# LAW meet_minted_orphan (R3): the lock file of a minted name is judged when no entry has
# the minted name, and kept beside its directory
# EXCLUDES: an orphan lock file kept forever, a live build's lock file
#   judged beside its directory
law meet_minted_orphan:
  for +t: String
  for +l: SpLab
  for +id: String
  for +m: Bool
  for full: {String.is_empty(t) == False{} : Bool}
  for u: {sp_hexn(32n, id) == True{} : Bool}
  {Sg.meet([Sg.Seen{Sg.Utf{String.append(sp_mint(t, l, id), ".lock")}, Sg.KFile{}}]) == [Sg.MOrphan{}] : List<&2, Sg.Met>} & {Sg.meet([Sg.Seen{Sg.Utf{String.append(sp_mint(t, l, id), ".lock")}, Sg.KFile{}}, Sg.Seen{Sg.Utf{sp_mint(t, l, id)}, Sg.KDir{m}}]) == [Sg.MKeep{}, Sg.MLeftover{}] : List<&2, Sg.Met>}

# LAW meet_names_example (R3): the names of the Rust sweep test: a staging directory, a
# tombstone, a plain directory, an orphan lock file, a lock file beside its
# directory, and the names that are not swept (a short uuid, another
# label, no leading dot, an empty target, an uppercase uuid; a file and a
# symlink with a staging name; a name that is not UTF-8)
# EXCLUDES: a spec that accepts any of the near misses
law meet_names_example:
  {Sg.meet([Sg.Seen{Sg.Utf{".s1.import-0123456789abcdef0123456789abcdef"}, Sg.KDir{False{}}}, Sg.Seen{Sg.Utf{".s12.deleted-0123456789abcdef0123456789abcdef"}, Sg.KDir{True{}}}, Sg.Seen{Sg.Utf{"session-1"}, Sg.KDir{False{}}}, Sg.Seen{Sg.Utf{"s2"}, Sg.KDir{True{}}}, Sg.Seen{Sg.Utf{".s3.fork-0123456789abcdef0123456789abcdef.lock"}, Sg.KFile{}}, Sg.Seen{Sg.Utf{".s1.import-0123456789abcdef0123456789abcdef.lock"}, Sg.KFile{}}, Sg.Seen{Sg.Utf{".s6.import-not-a-uuid"}, Sg.KDir{False{}}}, Sg.Seen{Sg.Utf{".s7.export-0123456789abcdef0123456789abcdef"}, Sg.KDir{False{}}}, Sg.Seen{Sg.Utf{"s8.import-0123456789abcdef0123456789abcdef"}, Sg.KDir{False{}}}, Sg.Seen{Sg.Utf{"..import-0123456789abcdef0123456789abcdef"}, Sg.KDir{False{}}}, Sg.Seen{Sg.Utf{".s9.fork-0123456789ABCDEF0123456789ABCDEF"}, Sg.KDir{False{}}}, Sg.Seen{Sg.Utf{".s10.import-0123456789abcdef0123456789abcdef"}, Sg.KFile{}}, Sg.Seen{Sg.Utf{".s11.fork-0123456789abcdef0123456789abcdef"}, Sg.KOther{}}, Sg.Seen{Sg.Raw{}, Sg.KDir{False{}}}, Sg.Seen{Sg.Raw{}, Sg.KDir{True{}}}]) == [Sg.MLeftover{}, Sg.MLeftover{}, Sg.MDescend{}, Sg.MKeep{}, Sg.MOrphan{}, Sg.MKeep{}, Sg.MDescend{}, Sg.MDescend{}, Sg.MDescend{}, Sg.MDescend{}, Sg.MDescend{}, Sg.MKeep{}, Sg.MKeep{}, Sg.MDescend{}, Sg.MKeep{}] : List<&2, Sg.Met>}

# LAW sweep_stays_out_real (R3): the walk enters exactly the plain directories: never a
# storage, a symlink, a file or a leftover (sweep_stays_out, on the real
# listing)
# EXCLUDES: a walk into a storage or behind a symlink, a plain directory
#   left unwalked (sweep_reaches_every_depth)
law sweep_stays_out_real:
  for +es: List<&2, Sg.Seen>
  {sp_descends(Sg.meet(es)) == sp_plains(es) : List<&2, Bool>}

# LAW judge_exact (R2, R4): the plan for a judged entry is the spec's
# EXCLUDES: a held or young leftover removed, a stale free one kept, a
#   lock file left behind or removed under a live build, a gone lock file
#   removed, a young inner entry ignored
law judge_exact:
  for +c: Sg.Cand
  for +l: Sg.Lock
  for +now: Sg.Time
  for +own: Sg.Time
  for +inner: List<&2, Sg.Time>
  {Sg.judge(c, l, now, own, inner) == sp_judge(c, l, now, own, inner) : Sg.Plan}

# LAW sweep_never_live_real (R2): a judged entry a live process holds the lock of stays
# (sweep_never_live, on the real facts)
# EXCLUDES: a running build's staging directory removed because it is old
law sweep_never_live_real:
  for +c: Sg.Cand
  for +now: Sg.Time
  for +own: Sg.Time
  for +inner: List<&2, Sg.Time>
  {Sg.judge(c, Sg.LHeld{}, now, own, inner) == Sg.PKeep{} : Sg.Plan}

# LAW sweep_never_young_real (R2): a judged entry that it or a direct entry of it changed
# within the day stays (sweep_never_young, on the real facts)
# EXCLUDES: staleness read from the entry alone, a time ahead of the
#   clock taken for old
law sweep_never_young_real:
  for +c: Sg.Cand
  for +l: Sg.Lock
  for +now: Sg.Time
  for +own: Sg.Time
  for +inner: List<&2, Sg.Time>
  for young: {sp_all_old(now, own <> inner) == False{} : Bool}
  {Sg.judge(c, l, now, own, inner) == Sg.PKeep{} : Sg.Plan}

# LAW sweep_takes_stale_free_real (R4): a judged free entry untouched for a day goes: a
# directory with its lock file (or alone without one), an orphan lock file
# (sweep_reaches_every_depth, on the real facts)
# EXCLUDES: a leftover kept forever, its lock file left behind
law sweep_takes_stale_free_real:
  for +now: Sg.Time
  for +own: Sg.Time
  for +inner: List<&2, Sg.Time>
  for old: {sp_all_old(now, own <> inner) == True{} : Bool}
  {Sg.judge(Sg.CDir{}, Sg.LFree{}, now, own, inner) == Sg.PRmDirLock{} : Sg.Plan} & {Sg.judge(Sg.CDir{}, Sg.LAbsent{}, now, own, inner) == Sg.PRmDir{} : Sg.Plan} & {Sg.judge(Sg.CLock{}, Sg.LFree{}, now, own, inner) == Sg.PRmFile{} : Sg.Plan}

# LAW judge_refines (R2, R4): a judged entry is removed exactly when the model removes its
# node: reached, of its sort, held as probed, stale when every time is a
# day old
# EXCLUDES: a real sweep that removes what the model keeps, or keeps what
#   it removes
law judge_refines:
  for +i: Nat
  for +c: Sg.Cand
  for +l: Sg.Lock
  for +now: Sg.Time
  for +own: Sg.Time
  for +inner: List<&2, Sg.Time>
  for probed: {sp_probed(c, l) == True{} : Bool}
  {Sg.removes(Sg.Node{i, sp_sort(c), sp_held(l), sp_all_old(now, own <> inner), True{}}) == sp_removes(Sg.judge(c, l, now, own, inner)) : Bool}

# LAW judge_day_example (R2): anchor: a day is 86400 seconds, to the nanosecond
# EXCLUDES: another bound, a bound in other units, an off-by-one at the day
law judge_day_example:
  {Sg.judge(Sg.CDir{}, Sg.LFree{}, Sg.Time{200000n, 5n}, Sg.Time{113600n, 5n}, []) == Sg.PRmDirLock{} : Sg.Plan} & {Sg.judge(Sg.CDir{}, Sg.LFree{}, Sg.Time{200000n, 4n}, Sg.Time{113600n, 5n}, []) == Sg.PKeep{} : Sg.Plan}

# Laws: the entry (R8)
# --------------------

# LAW staging_entry_answers (R8): the staging entry (bend/ffi_staging.bend) answers every
# request Rust spells, every number, length and count within the wire,
# with the spelled decision of the real rule
# EXCLUDES: a field misread, swapped or dropped; a request answered with
#   another request's rule, a default, or a reply spelled otherwise
law staging_entry_answers:
  for +r: FSg.Req
  for h: {sp_fit_req(r) == True{} : Bool}
  {FSg.ffi(sp_w_req(r, "")) == sp_w_reply(r) : String}

# LAW staging_entry_exact (R8): every input the entry does not answer with the error form is a
# spelled request that fits the wire: any other input gets the error form
# EXCLUDES: a decision made on input that is no request (an unknown tag, a
#   malformed field, input left over)
law staging_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FSg.ffi(s)) == False{} : Bool}
  exs r: FSg.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW staging_entry_example (R8): anchor: the wire strings Rust sends and the replies it reads
# EXCLUDES: tags in another order, a field order other than Rust's
law staging_entry_example:
  {FSg.ffi("0,T") == "1," : String} & {FSg.ffi("0,F") == "0," : String} & {FSg.ffi("1,2,0,43,.s1.import-0123456789abcdef0123456789abcdef0,F0,9,session-10,F") == "2,2,1," : String} & {FSg.ffi("2,0,1,200000,0,113600,0,1,50000,0,") == "2," : String} & {FSg.ffi("3,2,0,9,durable-10,T0,14,legacy-1.jsonl1,") == "2,1,9,durable-12,8,legacy-1" : String} & {FSg.ffi("4,1,0,1,a0,T1,2,/p1,30,5,") == "1,0,1,1,a30,5," : String}

# LAW staging_entry_malformed_example (R8): witness: an unknown tag and input left over get the
# error form
# EXCLUDES: a vacuous staging_entry_exact
law staging_entry_malformed_example:
  {LawsBase.wire_opens_err(FSg.ffi("5,")) == True{} : Bool} & {LawsBase.wire_opens_err(FSg.ffi("0,TX")) == True{} : Bool}
