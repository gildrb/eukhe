# eukhe: the laws of area config

import Base
import ../bend/config.bend as Cf
import ../bend/ffi_config.bend as FC
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../spec/settings/config.bend as CS

# ---- config ----

# LAWS (config audit H1-H4, M3, M7, A1; entry R1, R2): no config input is lost
# in silence. Each law is an open claim about the model in
# bend/config.bend or its entry bend/ffi_config.bend (the functions the
# entry calls: Cf.rmw, Cf.applied, Cf.reported, Cf.limits, Cf.project,
# Cf.withheld, Cf.finds of Cf.merge); PROOF.bend proves them (as
# Config.<law>) with the lemmas of proof/config/. The default model a
# setting names has its own laws (laws/default_model.bend).
#
# Requirements (stated: the audit's H/M rows, the Rust doc comments named;
# inferred: A):
# H1  A writer of a config document (settings.json, mcp-connections.json,
#     auth.json: crates/eukhe-core/src/settings/persist.rs,
#     mcp/connection_store.rs, auth/storage.rs) never writes over a
#     document it could not read; over a document it read it changes only
#     the key of its edit (a set gives every entry of the key the value, a
#     new key goes last, a delete drops every entry of the key) and keeps
#     every other entry, value and place; a missing file is the empty
#     document.
# H2  A settings setter writes the document on disk at write time, never
#     the copy it loaded (persist.rs sends the disk read to Cf.rmw).
# H3  Each leaf of a settings document applies (a good value) or is named
#     by a diagnostic (a value of a bad type, a key no setting declares),
#     never both, in the document's order (settings/load.rs).
# H4  The in-flight limit of a provider (`providerMaxInFlight`,
#     admission.rs): unset or no entry is no limit, 0 is no limit, a whole
#     n caps at n, a malformed entry or a value that is not a map caps at
#     1 (fails closed); the first entry of a provider counts; another
#     provider's entry never changes it; the limits asked come in order.
# M3  An untrusted project (settings/trust.rs:1-9, 153-161) applies only
#     its preferences: a limit (on spend, time, rounds or concurrency), a
#     system prompt file (resources/mod.rs:305-306), a credential or what
#     routes one, and a key that runs or installs code or that no rule
#     names are withheld and named once in the warning, in order, by the
#     name of their rule; a global-only key never applies from a project;
#     a trusted project applies every other key with its value; the keys
#     apply in the document's order, before the global values.
# M7  A project MCP entry is the entry that applies, whole: it never takes
#     a key (a URL, a credential) from the global entry of its name
#     (settings/merge.rs); a global entry the project does not name stays
#     whole.
# A1  (shipped as in eukhe v0.10.67; omp has no global-only settings: a
#     project merges every key, packages/coding-agent/src/config/
#     settings.ts:1403-1407, 2706-2728, test/settings-manager.test.ts:
#     2806-2815) Rust's cvar layer reads every CvarScope::Global cvar
#     (crates/eukhe-core/src/settings/cvar/table.rs) from the global
#     settings alone (settings/cvar.rs:1027-1031 document_sets): a project
#     value of one never takes effect, trusted or not, whatever this model
#     answers for its key. Of those keys the model classes trustedProjects,
#     gateway and ssh global-only (M3); for the others it decides only the
#     warning: an untrusted project's providers.tinyRuntimeLibrary
#     (credential), factory, privacy and allowedModels (no rule: code) are
#     named, its preferences (rlmMaxDepth, providerMaxInFlight,
#     providerMaxQueued, idleEvictionMinutes, sessionArchiveMaxAgeDays,
#     sessionArchiveMaxSessions, memory.model, memory.thinking) and every
#     key of a trusted project are not; Rust masks what the model applies,
#     in silence. The shipped path is pinned by the Rust test
#     settings/trust.rs `global_cvars_from_a_project_never_apply` (the
#     value never applies; the warning is v0.10.67's); the model's side by
#     the anchor trust_global_cvars_example.
# R1  Every request (the grammar in the entry's header and
#     crates/eukhe-bend/WIRE.md, every Nat, length and count within the
#     wire) is answered with the model's decision.
# R2  Any input that is not exactly one request is answered with exactly
#     the error form "config: malformed request", never a decision.

# (H1) A read/modify/write of a config document
# ---------------------------------------------

# LAW rmw_refuses_broken: a document that could not be read or parsed (or has a version
# the writer does not know) is never written
law rmw_refuses_broken:
  for e: Cf.Edit
  {Cf.rmw(Cf.Broken{}, e) == Cf.Refused{} : Cf.Write}

# LAW rmw_keeps_others: when it writes, every key the edit does not touch keeps the value
# it had in the document read
law rmw_keeps_others:
  for +d: List<&2, Cf.Entry>
  for +e: Cf.Edit
  for +j: Nat
  for +h: {Cf.touches(e, j) == False{} : Bool}
  {Cf.kept(Cf.rmw(Cf.Parsed{d}, e), j) == Cf.lookup(d, j) : Maybe<&2, Nat>}

# LAW rmw_applies_change: the key the edit sets has the value it sets
law rmw_applies_change:
  for +d: List<&2, Cf.Entry>
  for +k: Nat
  for +v: Nat
  {Cf.kept(Cf.rmw(Cf.Parsed{d}, Cf.Set{k, v}), k) == Some{v} : Maybe<&2, Nat>}

# the keys of d, in order
def cf_keys(d: List<&2, Cf.Entry>) -> List<&2, Nat>:
  match d:
    case Nil{}:
      Nil{}
    case e <> t:
      match e:
        case Cf.Entry{k, v}:
          k <> cf_keys(t)

# k is one of ks
def cf_mem(ks: List<&2, Nat>, +k: Nat) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(Nat.is_eq(x, k), cf_mem(t, k))

def cf_drop.keep(same: Bool, x: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match same:
    case True{}:
      rest
    case False{}:
      x <> rest

# ks without k
def cf_drop(ks: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  match ks:
    case Nil{}:
      Nil{}
    case +x <> t:
      cf_drop.keep(Nat.is_eq(x, k), x, cf_drop(t, k))

def cf_keys_set(there: Bool, ks: List<&2, Nat>, k: Nat) -> List<&2, Nat>:
  match there:
    case True{}:
      ks
    case False{}:
      List.append(&2, Nat, ks, [k])

# the keys after edit e of a document of keys ks: a set keeps every key
# in its place and puts a new key last; a delete drops its key
def cf_keys_after(+ks: List<&2, Nat>, e: Cf.Edit) -> List<&2, Nat>:
  match e:
    case Cf.Set{+k, v}:
      cf_keys_set(cf_mem(ks, k), ks, k)
    case Cf.Del{k}:
      cf_drop(ks, k)

def cf_written_keys(w: Cf.Write) -> Maybe<&2, List<&2, Nat>>:
  match w:
    case Cf.Refused{}:
      None{}
    case Cf.Wrote{d}:
      Some{cf_keys(d)}

# LAW rmw_keeps_place: a write keeps every key in its place: a set of a key the document
# has keeps the order of the keys, a set of a new key puts it last, a
# delete drops only its key
# EXCLUDES: a setter that moves its key to the front or the end of a
#   settings.json the user ordered, a delete that reorders the rest
law rmw_keeps_place:
  for +d: List<&2, Cf.Entry>
  for +e: Cf.Edit
  {cf_written_keys(Cf.rmw(Cf.Parsed{d}, e)) == Some{cf_keys_after(cf_keys(d), e)} : Maybe<&2, List<&2, Nat>>}

# the key an edit names
def cf_edit_key(e: Cf.Edit) -> Nat:
  match e:
    case Cf.Set{k, v}:
      k
    case Cf.Del{k}:
      k

def cf_vals.put(here: Bool, v: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match here:
    case True{}:
      v <> rest
    case False{}:
      rest

# the values of every entry of key j in d, in order
def cf_vals(d: List<&2, Cf.Entry>, +j: Nat) -> List<&2, Nat>:
  match d:
    case Nil{}:
      Nil{}
    case e <> t:
      match e:
        case Cf.Entry{k, v}:
          cf_vals.put(Nat.is_eq(k, j), v, cf_vals(t, j))

# the values of key j in what was written; none when nothing was written
def cf_written_vals(w: Cf.Write, +j: Nat) -> Maybe<&2, List<&2, Nat>>:
  match w:
    case Cf.Refused{}:
      None{}
    case Cf.Wrote{d}:
      Some{cf_vals(d, j)}

# every value of vs is v
def cf_all_v(vs: List<&2, Nat>, +v: Nat) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(Nat.is_eq(x, v), cf_all_v(t, v))

# a write that gives every entry of key k the value v
def cf_written_all(w: Cf.Write, +k: Nat, +v: Nat) -> Bool:
  match w:
    case Cf.Refused{}:
      False{}
    case Cf.Wrote{d}:
      cf_all_v(cf_vals(d, k), v)

def cf_first(vs: List<&2, Nat>) -> Maybe<&2, Nat>:
  match vs:
    case Nil{}:
      None{}
    case x <> t:
      Some{x}

# LAW rmw_missing_writes_edit (H1): a missing file is the empty document: a set over it
# writes exactly the one entry it sets, a delete writes the empty document
# EXCLUDES: a missing file refused, or written over a default document
law rmw_missing_writes_edit:
  for k: Nat
  for v: Nat
  {Cf.rmw(Cf.Missing{}, Cf.Set{k, v}) == Cf.Wrote{[Cf.Entry{k, v}]} : Cf.Write} & {Cf.rmw(Cf.Missing{}, Cf.Del{k}) == Cf.Wrote{Nil{}} : Cf.Write}

# LAW rmw_values_kept (H1): over a document it read, a write keeps the values of every
# key j its edit does not name: the entries of j in what it writes hold,
# in order, the values the entries of j held in the document read (every
# entry of j, not only the first)
# EXCLUDES: a second entry of a key changed or dropped beside the edit, a
#   value written to another key, an entry of another key added or lost
law rmw_values_kept:
  for +d: List<&2, Cf.Entry>
  for +e: Cf.Edit
  for +j: Nat
  for other: {Nat.is_eq(cf_edit_key(e), j) == False{} : Bool}
  {cf_written_vals(Cf.rmw(Cf.Parsed{d}, e), j) == Some{cf_vals(d, j)} : Maybe<&2, List<&2, Nat>>}

# LAW rmw_set_every_entry (H1): a set over a document it read writes, and gives every
# entry of its key the value it sets (the first one and every later one)
# EXCLUDES: a set that changes only the first of two entries of its key,
#   a set refused over a readable document
law rmw_set_every_entry:
  for +d: List<&2, Cf.Entry>
  for +k: Nat
  for +v: Nat
  {cf_written_all(Cf.rmw(Cf.Parsed{d}, Cf.Set{k, v}), k, v) == True{} : Bool}

# LAW lookup_first_value (H1): the value read for a key (the lookup rmw_keeps_others and
# rmw_applies_change read through) is the value of its first entry, none
# without one
# EXCLUDES: rmw_keeps_others or rmw_applies_change holding by a lookup
#   that ignores the document or reads a later entry
law lookup_first_value:
  for d: List<&2, Cf.Entry>
  for +j: Nat
  {Cf.lookup(d, j) == cf_first(cf_vals(d, j)) : Maybe<&2, Nat>}

# (H2) A settings setter
# ----------------------

# LAW save_ignores_loaded (H2): what the setter model writes does not depend on the copy
# it loaded: two setters with different loaded copies write the same over
# the same disk read (what it writes over the read is the rmw laws': the
# Rust setter sends the disk read to Cf.rmw, persist.rs:230-234)
# EXCLUDES: a setter that writes its loaded copy, or any key of it
law save_ignores_loaded:
  for l1: List<&2, Cf.Entry>
  for l2: List<&2, Cf.Entry>
  for r: Cf.Read
  for +k: Nat
  for v: Nat
  {Cf.save(l1, r, k, v) == Cf.save(l2, r, k, v) : Cf.Write}

# LAW save_refuses_broken_example: anchor: a setter with a loaded copy refuses an unreadable
# file, writes the disk's document (not the copy) with its key set in
# place, and writes a missing file as the one entry
# EXCLUDES: a vacuous save_ignores_loaded (a setter that writes nothing)
law save_refuses_broken_example:
  {Cf.save([Cf.Entry{1n, 5n}], Cf.Broken{}, 2n, 7n) == Cf.Refused{} : Cf.Write} &
  {Cf.save([Cf.Entry{1n, 5n}], Cf.Parsed{[Cf.Entry{3n, 1n}, Cf.Entry{1n, 4n}]}, 1n, 9n) == Cf.Wrote{[Cf.Entry{3n, 1n}, Cf.Entry{1n, 9n}]} : Cf.Write} &
  {Cf.save([Cf.Entry{1n, 5n}], Cf.Missing{}, 2n, 7n) == Cf.Wrote{[Cf.Entry{2n, 7n}]} : Cf.Write}

# (H3) The leaves of a settings document
# --------------------------------------
# settings.json, through the leaf load (`settings::load`): the same
# report path as config.cfg (`CvarError`, a settings-error row).

# LAW leaf_applied_or_reported: every leaf applies or is named by a diagnostic
law leaf_applied_or_reported:
  for ls: List<&2, Cf.Leaf>
  for +l: Cf.Leaf
  for i: Cf.In(l, ls)
  {Bool.or(Cf.listed(Cf.applied(ls), Cf.Leaf.path(l)), Cf.listed(Cf.reported(ls), Cf.Leaf.path(l))) == True{} : Bool}

# LAW leaf_not_both: of distinct leaves, none both applies and is named
law leaf_not_both:
  for ls: List<&2, Cf.Leaf>
  for +n: Nat
  for +d: {Cf.distinct(ls) == True{} : Bool}
  {Bool.and(Cf.listed(Cf.applied(ls), n), Cf.listed(Cf.reported(ls), n)) == False{} : Bool}

# LAW leaf_lists_split (H3): leaves are judged one by one, in order: the lists of two runs
# of leaves are the lists of the first run, then those of the second
# EXCLUDES: a diagnostic list in another order (the Rust names the
#   reported places in the order given), a leaf judged by its neighbours,
#   a leaf lost or listed twice
law leaf_lists_split:
  for +xs: List<&2, Cf.Leaf>
  for +ys: List<&2, Cf.Leaf>
  {Cf.applied(List.append(&2, Cf.Leaf, xs, ys)) == List.append(&2, Nat, Cf.applied(xs), Cf.applied(ys)) : List<&2, Nat>} & {Cf.reported(List.append(&2, Cf.Leaf, xs, ys)) == List.append(&2, Nat, Cf.reported(xs), Cf.reported(ys)) : List<&2, Nat>}

# LAW leaf_lists_one (H3): a good leaf applies and is not named; a leaf of a bad type
# and a leaf no setting declares are named and do not apply
# EXCLUDES: a bad value applied, a good one reported, an undeclared key
#   dropped in silence
law leaf_lists_one:
  for +p: Nat
  {(Cf.applied([Cf.Leaf{p, Cf.Good{}}]), Cf.reported([Cf.Leaf{p, Cf.Good{}}])) == ([p], Nil{}) : List<&2, Nat> & List<&2, Nat>} &
  {(Cf.applied([Cf.Leaf{p, Cf.BadType{}}]), Cf.reported([Cf.Leaf{p, Cf.BadType{}}])) == (Nil{}, [p]) : List<&2, Nat> & List<&2, Nat>} &
  {(Cf.applied([Cf.Leaf{p, Cf.Undeclared{}}]), Cf.reported([Cf.Leaf{p, Cf.Undeclared{}}])) == (Nil{}, [p]) : List<&2, Nat> & List<&2, Nat>}

# (H4) The limit of every provider
# --------------------------------

# LAW limit_malformed_fails_closed: a malformed in-flight limit never reads as no limit: it caps its
# provider at 1 (a value that is not a map caps every provider)
law limit_malformed_fails_closed:
  for s: Cf.InFlight
  for +p: Nat
  for h: {Cf.malformed_at(s, p) == True{} : Bool}
  {Cf.limit(s, p) == Cf.Cap{1n} : Cf.Lim}

# LAW limit_values (H4): the in-flight limit of provider p: unset is no limit, a value
# that is not a map caps at 1, a map with no entry is no limit; when the
# first entry of the map is p's, 0 is no limit, a whole number 1+q caps at
# 1+q and a malformed entry caps at 1, whatever entries follow
# EXCLUDES: an absent provider capped, an unset value read as a cap, a
#   cap off by one, a malformed entry read as no limit, a later entry of
#   the provider chosen over its first
law limit_values:
  for +p: Nat
  for +q: Nat
  for +es: List<&2, Cf.Slot>
  {Cf.limit(Cf.Unset{}, p) == Cf.Unlimited{} : Cf.Lim} &
  {Cf.limit(Cf.NotMap{}, p) == Cf.Cap{1n} : Cf.Lim} &
  {Cf.limit(Cf.Entries{Nil{}}, p) == Cf.Unlimited{} : Cf.Lim} &
  {Cf.limit(Cf.Entries{Cf.Slot{p, Cf.Num{0n}} <> es}, p) == Cf.Unlimited{} : Cf.Lim} &
  {Cf.limit(Cf.Entries{Cf.Slot{p, Cf.Num{1n+q}} <> es}, p) == Cf.Cap{1n+q} : Cf.Lim} &
  {Cf.limit(Cf.Entries{Cf.Slot{p, Cf.Malformed{}} <> es}, p) == Cf.Cap{1n} : Cf.Lim}

# LAW limit_other_slot (H4): the entry of another provider never changes the limit of p
# EXCLUDES: a limit read from the wrong provider's entry
law limit_other_slot:
  for +p: Nat
  for +r: Nat
  for v: Cf.Val
  for es: List<&2, Cf.Slot>
  for other: {Nat.is_eq(r, p) == False{} : Bool}
  {Cf.limit(Cf.Entries{Cf.Slot{r, v} <> es}, p) == Cf.limit(Cf.Entries{es}, p) : Cf.Lim}

# LAW limits_per_provider (H4): the limits of the providers asked are each provider's
# limit, in the order asked: none for none, and one more provider adds its
# limit last
# EXCLUDES: a limit answered for another provider or in another order, a
#   provider dropped or answered twice
law limits_per_provider:
  for +s: Cf.InFlight
  for qs: List<&2, Nat>
  for +q: Nat
  {Cf.limits(s, Nil{}) == Nil{} : List<&2, Cf.Lim>} & {Cf.limits(s, List.append(&2, Nat, qs, [q])) == List.append(&2, Cf.Lim, Cf.limits(s, qs), [Cf.limit(s, q)]) : List<&2, Cf.Lim>}

# (M3) An untrusted project
# -------------------------

# LAW untrusted_changes_nothing_guarded: over the items of a project (a key, the class the caller
# gave it, a value): when no item of key k is a preference, an untrusted
# project leaves k at its global value (the classes come from the caller;
# the classification of the shipped path is the trust_* laws')
law untrusted_changes_nothing_guarded:
  for +g: List<&2, Cf.Entry>
  for items: List<&2, Cf.Item>
  for +k: Nat
  for +h: {Cf.only_guarded(items, k) == True{} : Bool}
  {Cf.lookup(Cf.effective(Cf.Untrusted{}, g, items), k) == Cf.lookup(g, k) : Maybe<&2, Nat>}

# LAW trusted_project_applies: over the items of a project, the first item applies from a
# trusted project, whatever class the caller gave it
law trusted_project_applies:
  for g: List<&2, Cf.Entry>
  for +k: Nat
  for kind: Cf.Class
  for v: Nat
  for items: List<&2, Cf.Item>
  {Cf.lookup(Cf.effective(Cf.Trusted{}, g, Cf.Item{k, kind, v} <> items), k) == Some{v} : Maybe<&2, Nat>}

def cf_is_pref(c: Cf.Class) -> Bool:
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

# LAW trust_project_split (M3): the keys of a project apply one by one, in the
# document's order, before the global values: the values of two runs of
# keys are those of the first run, then those of the second over the
# global values
# EXCLUDES: keys reordered, a key applied or withheld by its neighbours,
#   project values put after the global ones, a global value dropped
law trust_project_split:
  for +t: Cf.Trust
  for +g: List<&2, Cf.Entry>
  for +xs: List<&2, Cf.PKey>
  for +ys: List<&2, Cf.PKey>
  {Cf.project(t, g, List.append(&2, Cf.PKey, xs, ys)) == List.append(&2, Cf.Entry, Cf.project(t, Nil{}, xs), Cf.project(t, g, ys)) : List<&2, Cf.Entry>}

# n is one of ns
def cf_seen(ns: List<&2, String>, +n: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(String.eq(x, n), cf_seen(t, n))

def cf_name_once.add(seen: Bool, n: String, acc: List<&2, String>) -> List<&2, String>:
  match seen:
    case True{}:
      acc
    case False{}:
      List.append(&2, String, acc, [n])

# acc, then each name of ns that acc does not hold yet, in order
def cf_name_once(ns: List<&2, String>, +acc: List<&2, String>) -> List<&2, String>:
  match ns:
    case Nil{}:
      acc
    case +n <> t:
      cf_name_once(t, cf_name_once.add(cf_seen(acc, n), n, acc))

# LAW trust_withheld_step (M3): the warning grows key by key: one more key adds what the
# warning of that key alone names, unless the warning names it already
# EXCLUDES: a name twice, names reordered, a name of an earlier key lost
law trust_withheld_step:
  for +t: Cf.Trust
  for +ks: List<&2, Cf.PKey>
  for +x: Cf.PKey
  {Cf.withheld(t, List.append(&2, Cf.PKey, ks, [x])) == cf_name_once(Cf.withheld(t, [x]), Cf.withheld(t, ks)) : List<&2, String>}

# LAW trust_untrusted_applies_prefs (M3): a key whose rule makes it a preference applies
# from an untrusted project with its value, and the warning does not name
# it
# EXCLUDES: a preference withheld or named, a value of another key
law trust_untrusted_applies_prefs:
  for k: Nat
  for +p: List<&2, String>
  for v: Nat
  for n: String
  for pref: {Cf.classify(p) == Cf.Hit{n, Cf.Proj{Cf.Pref{}}} : Cf.Hit}
  {(Cf.project(Cf.Untrusted{}, Nil{}, [Cf.PKey{k, p, v}]), Cf.withheld(Cf.Untrusted{}, [Cf.PKey{k, p, v}])) == ([Cf.Entry{k, v}], Nil{}) : List<&2, Cf.Entry> & List<&2, String>}

# LAW trust_untrusted_withholds_others (M3): a key whose rule makes it a limit, a system
# prompt file, a credential or code never applies from an untrusted
# project, and the warning names it by its rule's name
# EXCLUDES: a limit, prompt, credential or code key applied from an
#   untrusted project, or withheld in silence
law trust_untrusted_withholds_others:
  for k: Nat
  for +p: List<&2, String>
  for v: Nat
  for n: String
  for c: Cf.Class
  for other: {cf_is_pref(c) == False{} : Bool}
  for at: {Cf.classify(p) == Cf.Hit{n, Cf.Proj{c}} : Cf.Hit}
  {(Cf.project(Cf.Untrusted{}, Nil{}, [Cf.PKey{k, p, v}]), Cf.withheld(Cf.Untrusted{}, [Cf.PKey{k, p, v}])) == (Nil{}, [n]) : List<&2, Cf.Entry> & List<&2, String>}

# LAW trust_trusted_applies_project_keys (M3): a trusted project applies every key whose rule
# is not global-only, with its value, and the warning does not name it
# EXCLUDES: a trusted project's key withheld, named, or given another value
law trust_trusted_applies_project_keys:
  for k: Nat
  for +p: List<&2, String>
  for v: Nat
  for n: String
  for c: Cf.Class
  for at: {Cf.classify(p) == Cf.Hit{n, Cf.Proj{c}} : Cf.Hit}
  {(Cf.project(Cf.Trusted{}, Nil{}, [Cf.PKey{k, p, v}]), Cf.withheld(Cf.Trusted{}, [Cf.PKey{k, p, v}])) == ([Cf.Entry{k, v}], Nil{}) : List<&2, Cf.Entry> & List<&2, String>}

# LAW trust_global_only_never_applies (M3): a key whose rule is global-only never applies
# from a project, trusted or not, and the warning names it by its rule's
# name
# EXCLUDES: trustedProjects, gateway or ssh taken from a project, or
#   dropped in silence
law trust_global_only_never_applies:
  for +t: Cf.Trust
  for k: Nat
  for +p: List<&2, String>
  for v: Nat
  for n: String
  for at: {Cf.classify(p) == Cf.Hit{n, Cf.GlobalOnly{}} : Cf.Hit}
  {(Cf.project(t, Nil{}, [Cf.PKey{k, p, v}]), Cf.withheld(t, [Cf.PKey{k, p, v}])) == (Nil{}, [n]) : List<&2, Cf.Entry> & List<&2, String>}

# x is not the first name of path q (an empty rule path would name every
# key)
def cf_not_head(q: List<&2, String>, +x: String) -> Bool:
  match q:
    case Nil{}:
      False{}
    case y <> ys:
      Bool.not(String.eq(y, x))

# no rule of rs starts with the name x
def cf_no_rule_starts(rs: List<&2, Cf.Rule>, +x: String) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      match r:
        case Cf.Rule{q, s}:
          Bool.and(cf_not_head(q, x), cf_no_rule_starts(t, x))

# LAW trust_unknown_key_is_code (M3): a key whose first name starts no rule of the table
# is code, named by that first name (withheld from an untrusted project:
# trust_untrusted_withholds_others)
# EXCLUDES: an unknown key taken for a preference, a warning that names a
#   leaf instead of its top key
law trust_unknown_key_is_code:
  for +x: String
  for r: List<&2, String>
  for none: {cf_no_rule_starts(Cf.rules(), x) == True{} : Bool}
  {Cf.classify(x <> r) == Cf.Hit{x, Cf.Proj{Cf.Code{}}} : Cf.Hit}

# the key paths an untrusted project may never set, from the Rust that
# decided them before the core did (crates/eukhe-core/src/settings/trust.rs
# at 5f534bbb6^, lines 173-184: "a limit on spend, time, rounds or
# concurrency (the tool rounds, the subagent cap and stall, the tool
# blocking budget, the autonomous and Director caps, the retry counts, the
# thinking budgets)", "holds or routes credentials (MCP servers,
# `kernelTransport`, ...)"), and the project system prompt files
# (resources/mod.rs:305-306: "load only for a trusted project")
def cf_guarded() -> List<&2, List<&2, String>>:
  [
    ["maxToolRounds"],
    ["subagentMaxConcurrency"],
    ["subagentStallMs"],
    ["toolBlockingBudgetMs"],
    ["autonomous"],
    ["directors"],
    ["retry", "maxRetries"],
    ["retry", "failover", "maxRetries"],
    ["thinkingBudgets"],
    ["mcpServers"],
    ["kernelTransport"],
    ["SYSTEM.md"],
    ["APPEND_SYSTEM.md"]
  ]

# nothing applies, and the warning names something
def cf_out_one(es: List<&2, Cf.Entry>, ns: List<&2, String>) -> Bool:
  match es:
    case Nil{}:
      Bool.not(List.is_empty(&2, String, ns))
    case e <> t:
      False{}

# under trust t, the key of place k and value v at each path of ps
# extended by r applies nothing and is named
def cf_kept_out(ps: List<&2, List<&2, String>>, +t: Cf.Trust, +r: List<&2, String>, +k: Nat, +v: Nat) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> rest:
      Bool.and(cf_out_one(Cf.project(t, Nil{}, [Cf.PKey{k, List.append(&2, String, p, r), v}]), Cf.withheld(t, [Cf.PKey{k, List.append(&2, String, p, r), v}])), cf_kept_out(rest, t, r, k, v))

# LAW trust_untrusted_withholds_guarded (M3): an untrusted project applies no key at or under
# a path of cf_guarded (a limit, a credential, a system prompt file), and
# the warning names it
# EXCLUDES: a limit, credential or prompt classed as a preference in the
#   table (an untrusted project raising maxToolRounds or replacing
#   SYSTEM.md)
law trust_untrusted_withholds_guarded:
  for r: List<&2, String>
  for k: Nat
  for v: Nat
  {cf_kept_out(cf_guarded(), Cf.Untrusted{}, r, k, v) == True{} : Bool}

# LAW trust_table_example: anchor: the nested retry counts are limits, a nested key under
# `retry` a preference, a credential and a global-only key named by their
# rule, a prompt file, a name that only starts like a rule's and an
# unknown key code
# EXCLUDES: a parent rule chosen over the nested rule before it, a match
#   on a name that only starts like a rule's
law trust_table_example:
  {Cf.classify(["retry", "maxRetries"]) == Cf.Hit{"retry.maxRetries", Cf.Proj{Cf.Limit{}}} : Cf.Hit} &
  {Cf.classify(["retry", "failover", "maxRetries"]) == Cf.Hit{"retry.failover.maxRetries", Cf.Proj{Cf.Limit{}}} : Cf.Hit} &
  {Cf.classify(["retry", "failover", "enabled"]) == Cf.Hit{"retry", Cf.Proj{Cf.Pref{}}} : Cf.Hit} &
  {Cf.classify(["mcpServers", "github", "url"]) == Cf.Hit{"mcpServers", Cf.Proj{Cf.Credential{}}} : Cf.Hit} &
  {Cf.classify(["gateway", "signal", "account"]) == Cf.Hit{"gateway", Cf.GlobalOnly{}} : Cf.Hit} &
  {Cf.classify(["SYSTEM.md"]) == Cf.Hit{"SYSTEM.md", Cf.Proj{Cf.Prompt{}}} : Cf.Hit} &
  {Cf.classify(["shellPath"]) == Cf.Hit{"shellPath", Cf.Proj{Cf.Code{}}} : Cf.Hit} &
  {Cf.classify(["themex"]) == Cf.Hit{"themex", Cf.Proj{Cf.Code{}}} : Cf.Hit} &
  {Cf.classify(["unknownKey", "x"]) == Cf.Hit{"unknownKey", Cf.Proj{Cf.Code{}}} : Cf.Hit}

# the leaves of the hostile project document of the Rust trust tests
# (crates/eukhe-core/src/settings/trust.rs:290-303), in the order of the
# Settings fields
def cf_hostile() -> List<&2, Cf.PKey>:
  [
    Cf.PKey{0n, ["defaultModel"], 0n},
    Cf.PKey{1n, ["theme"], 1n},
    Cf.PKey{2n, ["shellPath"], 2n},
    Cf.PKey{3n, ["shellCommandPrefix"], 3n},
    Cf.PKey{4n, ["npmCommand"], 4n},
    Cf.PKey{5n, ["mcpServers", "evil", "type"], 5n},
    Cf.PKey{6n, ["mcpServers", "evil", "command"], 6n},
    Cf.PKey{7n, ["packages"], 7n},
    Cf.PKey{8n, ["skills"], 8n},
    Cf.PKey{9n, ["sessionDir"], 9n},
    Cf.PKey{10n, ["unknownKey"], 10n}
  ]

# LAW trust_rust_vectors_example (M3): anchor: the vectors of the Rust trust tests
# (trust.rs:305-421): untrusted, the hostile document applies its theme and
# default model and names the eight others in order; trusted, it applies
# every key; an untrusted project's trustedProjects is named after
# npmCommand
# EXCLUDES: a table that drifts from the Rust tests' expectations
law trust_rust_vectors_example:
  {(Cf.project(Cf.Untrusted{}, Nil{}, cf_hostile()), Cf.withheld(Cf.Untrusted{}, cf_hostile())) == ([Cf.Entry{0n, 0n}, Cf.Entry{1n, 1n}], ["shellPath", "shellCommandPrefix", "npmCommand", "mcpServers", "packages", "skills", "sessionDir", "unknownKey"]) : List<&2, Cf.Entry> & List<&2, String>} &
  {(List.length(&2, Cf.Entry, Cf.project(Cf.Trusted{}, Nil{}, cf_hostile())), Cf.withheld(Cf.Trusted{}, cf_hostile())) == (11n, Nil{}) : Nat & List<&2, String>} &
  {Cf.withheld(Cf.Untrusted{}, [Cf.PKey{0n, ["npmCommand"], 0n}, Cf.PKey{1n, ["trustedProjects"], 1n}]) == ["npmCommand", "trustedProjects"] : List<&2, String>}

# the leaves of a project document that sets every Global-scope cvar the
# model does not class global-only (A1), in the order of the Rust test
# settings/trust.rs global_cvar_projects
def cf_global_cvars() -> List<&2, Cf.PKey>:
  [
    Cf.PKey{0n, ["rlmMaxDepth"], 0n},
    Cf.PKey{1n, ["providerMaxInFlight", "anthropic"], 1n},
    Cf.PKey{2n, ["providerMaxQueued"], 2n},
    Cf.PKey{3n, ["idleEvictionMinutes"], 3n},
    Cf.PKey{4n, ["sessionArchiveMaxAgeDays"], 4n},
    Cf.PKey{5n, ["sessionArchiveMaxSessions"], 5n},
    Cf.PKey{6n, ["memory", "model"], 6n},
    Cf.PKey{7n, ["memory", "thinking"], 7n},
    Cf.PKey{8n, ["providers", "tinyRuntimeLibrary"], 8n},
    Cf.PKey{9n, ["factory", "enabled"], 9n},
    Cf.PKey{10n, ["privacy", "anonymizeRemote"], 10n},
    Cf.PKey{11n, ["privacy", "terms"], 11n},
    Cf.PKey{12n, ["allowedModels"], 12n}
  ]

# LAW trust_global_cvars_example (A1): anchor: the model's answer for a project setting every Global-scope cvar it does not class global-only (Rust masks every value it applies): untrusted, the eight preferences apply and providers, factory, privacy (once) and allowedModels are named; trusted, all thirteen apply and none is named, as eukhe v0.10.67 ships
# EXCLUDES: a model that drifts from the warning eukhe shows for these
#   keys (a new name, a name lost)
law trust_global_cvars_example:
  {(Cf.project(Cf.Untrusted{}, Nil{}, cf_global_cvars()), Cf.withheld(Cf.Untrusted{}, cf_global_cvars())) == ([Cf.Entry{0n, 0n}, Cf.Entry{1n, 1n}, Cf.Entry{2n, 2n}, Cf.Entry{3n, 3n}, Cf.Entry{4n, 4n}, Cf.Entry{5n, 5n}, Cf.Entry{6n, 6n}, Cf.Entry{7n, 7n}], ["providers", "factory", "privacy", "allowedModels"]) : List<&2, Cf.Entry> & List<&2, String>} &
  {(List.length(&2, Cf.Entry, Cf.project(Cf.Trusted{}, Nil{}, cf_global_cvars())), Cf.withheld(Cf.Trusted{}, cf_global_cvars())) == (13n, Nil{}) : Nat & List<&2, String>}

# (M7) Named entries
# ------------------

# LAW project_entry_never_merges: a project MCP entry is the entry that applies, whole: it never
# takes a key (a URL, a credential) from the global entry of its name
law project_entry_never_merges:
  for +g: List<&2, Cf.Named>
  for p: List<&2, Cf.Named>
  for +n: Nat
  for h: {Cf.has(p, n) == True{} : Bool}
  {Cf.find(Cf.merge(g, p), n) == Cf.find(p, n) : Maybe<&2, List<&2, Cf.Entry>>}

# LAW global_entry_kept: a global entry the project does not name stays whole
law global_entry_kept:
  for +g: List<&2, Cf.Named>
  for p: List<&2, Cf.Named>
  for +n: Nat
  for h: {Cf.has(p, n) == False{} : Bool}
  {Cf.find(Cf.merge(g, p), n) == Cf.find(g, n) : Maybe<&2, List<&2, Cf.Entry>>}

def cf_find.pick(here: Bool, fs: List<&2, Cf.Entry>, later: Maybe<&2, List<&2, Cf.Entry>>) -> Maybe<&2, List<&2, Cf.Entry>>:
  match here:
    case True{}:
      Some{fs}
    case False{}:
      later

# the fields of the first entry named n in es, none without one
def cf_find(es: List<&2, Cf.Named>, +n: Nat) -> Maybe<&2, List<&2, Cf.Entry>>:
  match es:
    case Nil{}:
      None{}
    case x <> t:
      match x:
        case Cf.Named{m, fs}:
          cf_find.pick(Nat.is_eq(m, n), fs, cf_find(t, n))

def cf_or(m: Maybe<&2, List<&2, Cf.Entry>>, other: Maybe<&2, List<&2, Cf.Entry>>) -> Maybe<&2, List<&2, Cf.Entry>>:
  match m:
    case None{}:
      other
    case Some{fs}:
      Some{fs}

# for each name of qs: the project's entry of that name, else the
# global one, else none
def cf_merged(+g: List<&2, Cf.Named>, +p: List<&2, Cf.Named>, qs: List<&2, Nat>) -> List<&2, Maybe<&2, List<&2, Cf.Entry>>>:
  match qs:
    case Nil{}:
      Nil{}
    case +q <> t:
      cf_or(cf_find(p, q), cf_find(g, q)) <> cf_merged(g, p, t)

# LAW merge_finds_exact: the entry of each name asked, in order, is the project's entry of
# that name whole, else the global one whole, else none
# EXCLUDES: fields of a global entry mixed into a project entry, a global
#   entry lost, an entry answered for another name or in another order
law merge_finds_exact:
  for +g: List<&2, Cf.Named>
  for +p: List<&2, Cf.Named>
  for qs: List<&2, Nat>
  {Cf.finds(Cf.merge(g, p), qs) == cf_merged(g, p, qs) : List<&2, Maybe<&2, List<&2, Cf.Entry>>>}

# LAW merge_find_exact: in the merged map a name's entry is the project's entry whole,
# else the global one whole, else none
# EXCLUDES: a merged map whose entries only finds reads right
law merge_find_exact:
  for +g: List<&2, Cf.Named>
  for p: List<&2, Cf.Named>
  for +n: Nat
  {Cf.find(Cf.merge(g, p), n) == cf_or(cf_find(p, n), cf_find(g, n)) : Maybe<&2, List<&2, Cf.Entry>>}

# LAW config_helpers_example: anchor: each predicate a premise of the laws above reads
# holds for one input and fails for another: touches (rmw_keeps_others),
# listed and distinct (leaf_not_both), has (project_entry_never_merges,
# global_entry_kept), malformed_at (limit_malformed_fails_closed),
# only_guarded (untrusted_changes_nothing_guarded)
# EXCLUDES: a law above made vacuous by a premise never true, or claiming
#   too little by a premise always true
law config_helpers_example:
  {[Cf.touches(Cf.Set{1n, 5n}, 1n), Cf.touches(Cf.Set{1n, 5n}, 2n), Cf.touches(Cf.Del{3n}, 3n), Cf.touches(Cf.Del{3n}, 1n),
    Cf.listed([1n, 2n], 2n), Cf.listed([1n, 2n], 3n),
    Cf.distinct([Cf.Leaf{1n, Cf.Good{}}, Cf.Leaf{2n, Cf.BadType{}}]), Cf.distinct([Cf.Leaf{1n, Cf.Good{}}, Cf.Leaf{1n, Cf.BadType{}}]),
    Cf.has([Cf.Named{1n, Nil{}}], 1n), Cf.has([Cf.Named{1n, Nil{}}], 2n),
    Cf.malformed_at(Cf.NotMap{}, 0n), Cf.malformed_at(Cf.Unset{}, 0n), Cf.malformed_at(Cf.Entries{[Cf.Slot{0n, Cf.Malformed{}}]}, 0n), Cf.malformed_at(Cf.Entries{[Cf.Slot{0n, Cf.Num{3n}}]}, 0n),
    Cf.only_guarded([Cf.Item{1n, Cf.Limit{}, 5n}], 1n), Cf.only_guarded([Cf.Item{1n, Cf.Pref{}, 5n}], 1n)] ==
   [True{}, False{}, True{}, False{},
    True{}, False{},
    True{}, False{},
    True{}, False{},
    True{}, False{}, True{}, False{},
    True{}, False{}] : List<&2, Bool>}

# The entry (bend/ffi_config.bend)
# --------------------------------

# LAW config_ffi_answers (R1): every request the laws' speller writes (CS.cf_w_ask, from
# the grammar of the entry's header), every number, length and count
# within the wire, is answered with the model's decision spelled by the
# laws' reply speller (CS.cf_w_reply): the write, the leaves that apply and
# those named, the limits, the keys that apply and the withheld names, the
# merged entries
# EXCLUDES: a field misread, swapped or dropped; a request answered with
#   another request's rule, a default, or a reply spelled otherwise
law config_ffi_answers:
  for +a: FC.Ask
  for fits: {CS.cf_fit_ask(a) == True{} : Bool}
  {FC.ffi(CS.cf_w_ask(a)) == CS.cf_w_reply(a) : String}

# LAW config_ffi_reads_only_requests (R1, R2): an input answered other than with the error
# form is a spelled request, answered with that request's decision
# EXCLUDES: a decision made on input that is no request (an unknown tag, a
#   malformed field, a short list, input left over), a reply other than
#   the decision of the request read
law config_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FC.ffi(s)) == False{} : Bool}
  exs a: FC.Ask
  {(s, FC.ffi(s)) == (CS.cf_w_ask(a), CS.cf_w_reply(a)) : String & String}

# LAW config_ffi_refuses (R2): an input answered with the error form gets exactly
# "config: malformed request"
# EXCLUDES: an error text that varies with the input, a second error form
law config_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FC.ffi(s)) == True{} : Bool}
  {FC.ffi(s) == Wr.err("config: malformed request") : String}

# LAW config_ffi_example (R1): anchor: wire strings as the grammar spells them and their
# replies: a set over a parsed document, a broken read, a delete over a
# missing file, leaves, limits, an untrusted project, a merge
# EXCLUDES: tags in another order, a field order other than the grammar's
law config_ffi_example:
  {FC.ffi("0,1,2,0,0,1,1,0,0,7,") == "1,2,0,7,1,1," : String} &
  {FC.ffi("0,1,2,0,0,1,1,0,2,7,") == "1,3,0,0,1,1,2,7," : String} &
  {FC.ffi("0,2,0,0,7,") == "0," : String} &
  {FC.ffi("0,0,1,3,") == "1,0," : String} &
  {FC.ffi("1,3,0,0,1,1,2,2,") == "1,0,2,1,2," : String} &
  {FC.ffi("2,1,2,0,0,5,1,1,3,0,1,2,") == "3,1,5,1,1,0," : String} &
  {FC.ffi("2,2,2,0,9,") == "2,1,1,1,1," : String} &
  {FC.ffi("3,1,3,0,1,5,theme0,1,2,5,retry10,maxRetries1,2,1,7,unknown2,") == "1,0,0,2,16,retry.maxRetries7,unknown" : String} &
  {FC.ffi("4,1,0,1,0,1,1,0,1,0,2,2,0,1,") == "2,1,1,0,2,0," : String}

# LAW config_ffi_refuses_example (R2): anchor: an unknown tag, a bad outcome tag and input
# left over get the error form
# EXCLUDES: a vacuous config_ffi_refuses (no input refused)
law config_ffi_refuses_example:
  {[FC.ffi("5,"), FC.ffi("1,1,0,3,"), FC.ffi("0,2,0,0,7,x")] == [Wr.err("config: malformed request"), Wr.err("config: malformed request"), Wr.err("config: malformed request")] : List<&2, String>}
