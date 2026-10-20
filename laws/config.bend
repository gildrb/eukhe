# LAWS (config audit H1-H4, M3, M7): no config input is lost in silence.
# A writer never replaces a document it could not read and keeps every
# entry it does not change; a setter writes the document on disk, not
# the copy it loaded; each leaf of a settings document applies or is
# named; a malformed limit fails closed; a saved default model runs or
# its substitution is shown; an untrusted project changes no limit,
# prompt or credential; a project MCP entry never takes the keys of a
# global one. Each law is an open claim about the models in
# bend/config.bend and bend/default_model.bend; PROOF.bend proves them
# (as Cfg.<law>) with the lemmas of bend/proof_config.bend.

import Base
import ../bend/config.bend as Cf
import ../bend/default_model.bend as Dm

# (H1) A read/modify/write of a config document
# ---------------------------------------------
# settings.json (`eukhe mcp add`, the resource arrays, every setter),
# mcp-connections.json (`remove`, verify) and auth.json (`set`,
# `remove`): the writer reads the document under its lock.

# LAW: a document that could not be read or parsed (or has a version
# the writer does not know) is never written
law rmw_refuses_broken:
  for e: Cf.Edit
  {Cf.rmw(Cf.Broken{}, e) == Cf.Refused{} : Cf.Write}

# LAW: when it writes, every key the edit does not touch keeps the value
# it had in the document read
law rmw_keeps_others:
  for +d: List<&2, Cf.Entry>
  for +e: Cf.Edit
  for +j: Nat
  for +h: {Cf.touches(e, j) == False{} : Bool}
  {Cf.kept(Cf.rmw(Cf.Parsed{d}, e), j) == Cf.lookup(d, j) : Maybe<&2, Nat>}

# LAW: the key the edit sets has the value it sets
law rmw_applies_change:
  for +d: List<&2, Cf.Entry>
  for +k: Nat
  for +v: Nat
  {Cf.kept(Cf.rmw(Cf.Parsed{d}, Cf.Set{k, v}), k) == Some{v} : Maybe<&2, Nat>}

# (H2) A settings setter
# ----------------------

# LAW: a setter of key k to v writes D[k := v], where D is the document
# on disk at write time, whatever copy the setter loaded before (a copy
# without a key that failed to load, or without a key another writer
# added since)
law settings_save_preserves:
  for loaded: List<&2, Cf.Entry>
  for d: List<&2, Cf.Entry>
  for +k: Nat
  for v: Nat
  {Cf.save(loaded, Cf.Parsed{d}, k, v) == Cf.Wrote{Cf.set(d, k, v)} : Cf.Write}

# (H3) The leaves of a settings document
# --------------------------------------
# settings.json, through the leaf load (`settings::load`): the same
# report path as config.cfg (`CvarError`, a settings-error row).

# LAW: every leaf applies or is named by a diagnostic
law leaf_applied_or_reported:
  for ls: List<&2, Cf.Leaf>
  for +l: Cf.Leaf
  for i: Cf.In(l, ls)
  {Bool.or(Cf.listed(Cf.applied(ls), Cf.Leaf.path(l)), Cf.listed(Cf.reported(ls), Cf.Leaf.path(l))) == True{} : Bool}

# LAW: of distinct leaves, none both applies and is named
law leaf_not_both:
  for ls: List<&2, Cf.Leaf>
  for +n: Nat
  for +d: {Cf.distinct(ls) == True{} : Bool}
  {Bool.and(Cf.listed(Cf.applied(ls), n), Cf.listed(Cf.reported(ls), n)) == False{} : Bool}

# LAW: a malformed in-flight limit never reads as no limit: it caps its
# provider at 1 (a value that is not a map caps every provider)
law limit_malformed_fails_closed:
  for s: Cf.InFlight
  for +p: Nat
  for h: {Cf.malformed_at(s, p) == True{} : Bool}
  {Cf.limit(s, p) == Cf.Cap{1n} : Cf.Lim}

# LAW: a well-formed entry is the provider's limit
law limit_number_applies:
  for es: List<&2, Cf.Slot>
  for +p: Nat
  for +n: Nat
  for h: {Cf.slot(es, p) == Some{Cf.Num{n}} : Maybe<&2, Cf.Val>}
  {Cf.limit(Cf.Entries{es}, p) == Cf.val_limit(Cf.Num{n}) : Cf.Lim}

# (H4) The saved default model
# ----------------------------
# bend/default_model.bend: the session-model resolution at open.

# LAW: a session started with a saved default runs on it, or its notices
# name the saved default and the reason it did not run
law default_honoured_or_reported:
  for x: Dm.In
  {Dm.reported(x, Dm.open(Dm.resolve(x))) == True{} : Bool}

# LAW: a session that runs on its saved default has no notice
law default_quiet_when_honoured:
  for x: Dm.In
  for h: {Dm.on_saved(Dm.Session.run(Dm.open(Dm.resolve(x)))) == True{} : Bool}
  {Dm.none(Dm.Session.notes(Dm.open(Dm.resolve(x)))) == True{} : Bool}

# LAW: with no saved default the session has no notice
law default_quiet_when_unset:
  for cat: Bool
  for key: Bool
  for out: Bool
  for next: Dm.Next
  {Dm.Session.notes(Dm.open(Dm.resolve(Dm.In{Dm.NoDefault{}, cat, key, out, next}))) == Nil{} : List<&2, Dm.Key>}

# LAW: a saved default whose provider has no credentials opens the
# session with no model: no other provider runs in its place
law default_unkeyed_never_moves:
  for m: Nat
  for out: Bool
  for next: Dm.Next
  {Dm.Session.run(Dm.open(Dm.resolve(Dm.In{Dm.Default{m}, True{}, False{}, out, next}))) == Dm.Idle{} : Dm.Run}

# (M3) An untrusted project
# -------------------------

# LAW: an untrusted project changes no limit, system prompt or
# credential: a key that no preference item of the project sets keeps
# its global value
law untrusted_changes_nothing_guarded:
  for +g: List<&2, Cf.Entry>
  for items: List<&2, Cf.Item>
  for +k: Nat
  for +h: {Cf.only_guarded(items, k) == True{} : Bool}
  {Cf.lookup(Cf.effective(Cf.Untrusted{}, g, items), k) == Cf.lookup(g, k) : Maybe<&2, Nat>}

# LAW: a trusted project's item applies, whatever it is
law trusted_project_applies:
  for g: List<&2, Cf.Entry>
  for +k: Nat
  for kind: Cf.Class
  for v: Nat
  for items: List<&2, Cf.Item>
  {Cf.lookup(Cf.effective(Cf.Trusted{}, g, Cf.Item{k, kind, v} <> items), k) == Some{v} : Maybe<&2, Nat>}

# (M7) Named entries
# ------------------

# LAW: a project MCP entry is the entry that applies, whole: it never
# takes a key (a URL, a credential) from the global entry of its name
law project_entry_never_merges:
  for +g: List<&2, Cf.Named>
  for p: List<&2, Cf.Named>
  for +n: Nat
  for h: {Cf.has(p, n) == True{} : Bool}
  {Cf.find(Cf.merge(g, p), n) == Cf.find(p, n) : Maybe<&2, List<&2, Cf.Entry>>}

# LAW: a global entry the project does not name stays whole
law global_entry_kept:
  for +g: List<&2, Cf.Named>
  for p: List<&2, Cf.Named>
  for +n: Nat
  for h: {Cf.has(p, n) == False{} : Bool}
  {Cf.find(Cf.merge(g, p), n) == Cf.find(g, n) : Maybe<&2, List<&2, Cf.Entry>>}
