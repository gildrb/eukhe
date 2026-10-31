# eukhe: the laws of area config

import Base
import ../bend/config.bend as Cf
import ../bend/ffi_config.bend as FC
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../spec/settings/config.bend as CS
import ../spec/settings/config_rules.bend as CR

# ---- config ----

# LAWS (config audit H1-H4, M3, M7): no config input is lost in silence.
# A writer never replaces a document it could not read and keeps every
# entry it does not change; a setter writes the document on disk, not
# the copy it loaded; each leaf of a settings document applies or is
# named; a malformed limit fails closed; a saved default model runs or
# its substitution is shown; an untrusted project changes no limit,
# prompt or credential; a project MCP entry never takes the keys of a
# global one. Each law is an open claim about the models in
# bend/config.bend and bend/default_model.bend; PROOF.bend proves them
# (as Config.<law>) with the lemmas of proof/config/.

# (H1) A read/modify/write of a config document
# ---------------------------------------------
# settings.json (`eukhe mcp add`, the resource arrays, every setter),
# mcp-connections.json (`remove`, verify) and auth.json (`set`,
# `remove`): the writer reads the document under its lock.

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

# (H2) A settings setter
# ----------------------

# LAW settings_save_preserves: a setter of key k to v writes D[k := v], where D is the document
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

# LAW limit_malformed_fails_closed: a malformed in-flight limit never reads as no limit: it caps its
# provider at 1 (a value that is not a map caps every provider)
law limit_malformed_fails_closed:
  for s: Cf.InFlight
  for +p: Nat
  for h: {Cf.malformed_at(s, p) == True{} : Bool}
  {Cf.limit(s, p) == Cf.Cap{1n} : Cf.Lim}

# LAW limit_number_applies: a well-formed entry is the provider's limit
law limit_number_applies:
  for es: List<&2, Cf.Slot>
  for +p: Nat
  for +n: Nat
  for h: {Cf.slot(es, p) == Some{Cf.Num{n}} : Maybe<&2, Cf.Val>}
  {Cf.limit(Cf.Entries{es}, p) == Cf.val_limit(Cf.Num{n}) : Cf.Lim}

# (M3) An untrusted project
# -------------------------

# LAW untrusted_changes_nothing_guarded: an untrusted project changes no limit, system prompt or
# credential: a key that no preference item of the project sets keeps
# its global value
law untrusted_changes_nothing_guarded:
  for +g: List<&2, Cf.Entry>
  for items: List<&2, Cf.Item>
  for +k: Nat
  for +h: {Cf.only_guarded(items, k) == True{} : Bool}
  {Cf.lookup(Cf.effective(Cf.Untrusted{}, g, items), k) == Cf.lookup(g, k) : Maybe<&2, Nat>}

# LAW trusted_project_applies: a trusted project's item applies, whatever it is
law trusted_project_applies:
  for g: List<&2, Cf.Entry>
  for +k: Nat
  for kind: Cf.Class
  for v: Nat
  for items: List<&2, Cf.Item>
  {Cf.lookup(Cf.effective(Cf.Trusted{}, g, Cf.Item{k, kind, v} <> items), k) == Some{v} : Maybe<&2, Nat>}

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

# (H1) The order of a written document
# ------------------------------------

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

# LAW rmw_missing_is_empty: only a missing file reads as the empty document: an edit of it
# writes what the same edit of the empty document writes
# EXCLUDES: a missing file refused, or written over a default document
law rmw_missing_is_empty:
  for e: Cf.Edit
  {Cf.rmw(Cf.Missing{}, e) == Cf.rmw(Cf.Parsed{Nil{}}, e) : Cf.Write}

def cf_put_v(same: Bool, v: Nat, w: Nat) -> Nat:
  match same:
    case True{}:
      v
    case False{}:
      w

# d with every entry of key k holding v, each in its place
def cf_replace(d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> List<&2, Cf.Entry>:
  match d:
    case Nil{}:
      Nil{}
    case e <> t:
      match e:
        case Cf.Entry{+j, w}:
          Cf.Entry{j, cf_put_v(Nat.is_eq(j, k), v, w)} <> cf_replace(t, k, v)

def cf_set_in(there: Bool, d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> List<&2, Cf.Entry>:
  match there:
    case True{}:
      cf_replace(d, k, v)
    case False{}:
      List.append(&2, Cf.Entry, d, [Cf.Entry{k, v}])

def cf_without.keep(drop: Bool, e: Cf.Entry, rest: List<&2, Cf.Entry>) -> List<&2, Cf.Entry>:
  match drop:
    case True{}:
      rest
    case False{}:
      e <> rest

# d without the entries of key k
def cf_without(d: List<&2, Cf.Entry>, +k: Nat) -> List<&2, Cf.Entry>:
  match d:
    case Nil{}:
      Nil{}
    case e <> t:
      match e:
        case Cf.Entry{+j, w}:
          cf_without.keep(Nat.is_eq(j, k), Cf.Entry{j, w}, cf_without(t, k))

# the document d after edit e
def cf_edited(+d: List<&2, Cf.Entry>, e: Cf.Edit) -> List<&2, Cf.Entry>:
  match e:
    case Cf.Set{+k, v}:
      cf_set_in(cf_mem(cf_keys(d), k), d, k, v)
    case Cf.Del{k}:
      cf_without(d, k)

# LAW rmw_written_exact: a write over a document it read writes exactly that document
# with the edit applied: a set gives every entry of its key the new value
# in its place, or puts a new entry last; a delete drops every entry of
# its key; no other entry changes, moves, appears or goes
# EXCLUDES: a set that changes only the first of two entries of its key,
#   a value written to another key, an entry dropped or added beside the
#   edit
law rmw_written_exact:
  for +d: List<&2, Cf.Entry>
  for e: Cf.Edit
  {Cf.rmw(Cf.Parsed{d}, e) == Cf.Wrote{cf_edited(d, e)} : Cf.Write}

# (H3) The leaves, in order
# -------------------------

def cf_good(o: Cf.Outcome) -> Bool:
  match o:
    case Cf.Good{}:
      True{}
    case Cf.BadType{}:
      False{}
    case Cf.Undeclared{}:
      False{}

def cf_paths.put(b: Bool, p: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      p <> rest
    case False{}:
      rest

# the paths of the leaves whose outcome is good, in order
def cf_good_paths(ls: List<&2, Cf.Leaf>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> t:
      match l:
        case Cf.Leaf{p, o}:
          cf_paths.put(cf_good(o), p, cf_good_paths(t))

# the paths of the leaves whose outcome is not good, in order
def cf_bad_paths(ls: List<&2, Cf.Leaf>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> t:
      match l:
        case Cf.Leaf{p, o}:
          cf_paths.put(Bool.not(cf_good(o)), p, cf_bad_paths(t))

# LAW leaf_lists_exact: the leaves that apply are exactly the good ones and the leaves named
# are exactly the others, each list in the document's order
# EXCLUDES: a diagnostic list in another order (the Rust names the
#   reported places in the order given), a leaf lost or listed twice
law leaf_lists_exact:
  for +ls: List<&2, Cf.Leaf>
  {Cf.applied(ls) == cf_good_paths(ls) : List<&2, Nat>} & {Cf.reported(ls) == cf_bad_paths(ls) : List<&2, Nat>}

# (H4) The limit of every provider
# --------------------------------

def cf_lim_of(n: Nat) -> Cf.Lim:
  match n:
    case 0n:
      Cf.Unlimited{}
    case 1n+q:
      Cf.Cap{1n+q}

def cf_lim_val(v: Cf.Val) -> Cf.Lim:
  match v:
    case Cf.Num{n}:
      cf_lim_of(n)
    case Cf.Malformed{}:
      Cf.Cap{1n}

def cf_slot_lim.pick(here: Bool, v: Cf.Val, later: Cf.Lim) -> Cf.Lim:
  match here:
    case True{}:
      cf_lim_val(v)
    case False{}:
      later

# the limit of the first slot of provider p: no slot is no limit
def cf_slot_lim(es: List<&2, Cf.Slot>, +p: Nat) -> Cf.Lim:
  match es:
    case Nil{}:
      Cf.Unlimited{}
    case x <> t:
      match x:
        case Cf.Slot{q, v}:
          cf_slot_lim.pick(Nat.is_eq(q, p), v, cf_slot_lim(t, p))

# the limit of provider p: unset is no limit, not a map caps at 1
def cf_limit(s: Cf.InFlight, +p: Nat) -> Cf.Lim:
  match s:
    case Cf.Unset{}:
      Cf.Unlimited{}
    case Cf.Entries{es}:
      cf_slot_lim(es, p)
    case Cf.NotMap{}:
      Cf.Cap{1n}

def cf_limits(+s: Cf.InFlight, qs: List<&2, Nat>) -> List<&2, Cf.Lim>:
  match qs:
    case Nil{}:
      Nil{}
    case q <> t:
      cf_limit(s, q) <> cf_limits(s, t)

# LAW limits_exact: the limits of providers qs are, in order, each provider's: unset or no
# entry is no limit, 0 is no limit, a whole number n is n, a malformed
# entry or a value that is not a map caps at 1
# EXCLUDES: an absent provider capped, an unset value read as a cap, a
#   limit answered for another provider or in another order
law limits_exact:
  for +s: Cf.InFlight
  for qs: List<&2, Nat>
  {Cf.limits(s, qs) == cf_limits(s, qs) : List<&2, Cf.Lim>}

# (M7) The merged entries of every name
# -------------------------------------

def cf_find.pick(here: Bool, fs: List<&2, Cf.Entry>, later: Maybe<&2, List<&2, Cf.Entry>>) -> Maybe<&2, List<&2, Cf.Entry>>:
  match here:
    case True{}:
      Some{fs}
    case False{}:
      later

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

# (M3) Project keys by name
# -------------------------

# path a is a prefix of path b, name by name
def cf_prefix(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a:
    case Nil{}:
      True{}
    case x <> xs:
      match b:
        case Nil{}:
          False{}
        case y <> ys:
          Bool.and(String.eq(x, y), cf_prefix(xs, ys))

def cf_join.go(xs: List<&2, String>, x: String) -> String:
  match xs:
    case Nil{}:
      x
    case y <> ys:
      String.append(x, SCon{'.', cf_join.go(ys, y)})

# the names of p joined by '.'
def cf_join(p: List<&2, String>) -> String:
  match p:
    case Nil{}:
      ""
    case x <> xs:
      cf_join.go(xs, x)

def cf_head(p: List<&2, String>) -> String:
  match p:
    case Nil{}:
      ""
    case x <> xs:
      x

def cf_hit.pick(here: Bool, q: List<&2, String>, s: Cf.Scope, later: Cf.Hit) -> Cf.Hit:
  match here:
    case True{}:
      Cf.Hit{cf_join(q), s}
    case False{}:
      later

# the hit of path p: the first rule of rs whose path is a prefix of p;
# none: code, named by p's first name
def cf_hit(rs: List<&2, Cf.Rule>, +p: List<&2, String>) -> Cf.Hit:
  match rs:
    case Nil{}:
      Cf.Hit{cf_head(p), Cf.Proj{Cf.Code{}}}
    case r <> t:
      match r:
        case Cf.Rule{+q, s}:
          cf_hit.pick(cf_prefix(q, p), q, s, cf_hit(t, p))

def cf_rule(p: List<&2, String>, c: Cf.Class) -> Cf.Rule:
  Cf.Rule{p, Cf.Proj{c}}

# the table: what each key of a settings document (and each project
# prompt file) is, nested rules first; every key it does not name is
# code
def cf_rules() -> List<&2, Cf.Rule>:
  [
    cf_rule(["retry", "maxRetries"], Cf.Limit{}),
    cf_rule(["retry", "failover", "maxRetries"], Cf.Limit{}),
    cf_rule(["onboardingShown"], Cf.Pref{}),
    cf_rule(["onboardingCompleted"], Cf.Pref{}),
    cf_rule(["defaultProvider"], Cf.Pref{}),
    cf_rule(["defaultModel"], Cf.Pref{}),
    cf_rule(["subagentDefaultModel"], Cf.Pref{}),
    cf_rule(["recentModels"], Cf.Pref{}),
    cf_rule(["auxiliaryModel"], Cf.Pref{}),
    cf_rule(["defaultThinkingLevel"], Cf.Pref{}),
    cf_rule(["defaultServiceTier"], Cf.Pref{}),
    cf_rule(["rlmMaxDepth"], Cf.Pref{}),
    cf_rule(["providerMaxInFlight"], Cf.Pref{}),
    cf_rule(["providerMaxQueued"], Cf.Pref{}),
    cf_rule(["idleEvictionMinutes"], Cf.Pref{}),
    cf_rule(["sessionArchiveMaxAgeDays"], Cf.Pref{}),
    cf_rule(["sessionArchiveMaxSessions"], Cf.Pref{}),
    cf_rule(["transport"], Cf.Pref{}),
    cf_rule(["steeringMode"], Cf.Pref{}),
    cf_rule(["followUpMode"], Cf.Pref{}),
    cf_rule(["theme"], Cf.Pref{}),
    cf_rule(["compaction"], Cf.Pref{}),
    cf_rule(["memory"], Cf.Pref{}),
    cf_rule(["autoRefine"], Cf.Pref{}),
    cf_rule(["branchSummary"], Cf.Pref{}),
    cf_rule(["retry"], Cf.Pref{}),
    cf_rule(["providerBackupModel"], Cf.Pref{}),
    cf_rule(["imageModel"], Cf.Pref{}),
    cf_rule(["prompts"], Cf.Pref{}),
    cf_rule(["themes"], Cf.Pref{}),
    cf_rule(["enableSkillCommands"], Cf.Pref{}),
    cf_rule(["enableBuiltinSkills"], Cf.Pref{}),
    cf_rule(["terminal"], Cf.Pref{}),
    cf_rule(["images"], Cf.Pref{}),
    cf_rule(["enabledModels"], Cf.Pref{}),
    cf_rule(["treeFilterMode"], Cf.Pref{}),
    cf_rule(["chatDetail"], Cf.Pref{}),
    cf_rule(["editorPaddingX"], Cf.Pref{}),
    cf_rule(["autocompleteMaxVisible"], Cf.Pref{}),
    cf_rule(["showHardwareCursor"], Cf.Pref{}),
    cf_rule(["markdown"], Cf.Pref{}),
    cf_rule(["workflow"], Cf.Pref{}),
    cf_rule(["warnings"], Cf.Pref{}),
    cf_rule(["requestTiming"], Cf.Pref{}),
    cf_rule(["modelRoles"], Cf.Pref{}),
    cf_rule(["titles"], Cf.Pref{}),
    cf_rule(["tts"], Cf.Pref{}),
    cf_rule(["stt"], Cf.Pref{}),
    cf_rule(["subagentMaxConcurrency"], Cf.Limit{}),
    cf_rule(["subagentStallMs"], Cf.Limit{}),
    cf_rule(["toolBlockingBudgetMs"], Cf.Limit{}),
    cf_rule(["maxToolRounds"], Cf.Limit{}),
    cf_rule(["autonomous"], Cf.Limit{}),
    cf_rule(["directors"], Cf.Limit{}),
    cf_rule(["thinkingBudgets"], Cf.Limit{}),
    cf_rule(["SYSTEM.md"], Cf.Prompt{}),
    cf_rule(["APPEND_SYSTEM.md"], Cf.Prompt{}),
    cf_rule(["mcpServers"], Cf.Credential{}),
    cf_rule(["kernelTransport"], Cf.Credential{}),
    cf_rule(["providers"], Cf.Credential{}),
    Cf.Rule{["trustedProjects"], Cf.GlobalOnly{}},
    Cf.Rule{["gateway"], Cf.GlobalOnly{}},
    Cf.Rule{["ssh"], Cf.GlobalOnly{}}
  ]

# LAW trust_classify_exact: a key is what the first rule of the table (cf_rules) whose path
# is a prefix of the key's path says, named by that rule's path joined by
# '.'; a key no rule names is code (withheld from an untrusted project),
# named by its first name
# EXCLUDES: a parent rule chosen over the nested rule before it, a match
#   on a name that only starts like the rule's, an unknown key taken for
#   a preference, a warning that names a leaf instead of its rule, a rule
#   of the table changed, added, dropped or moved
law trust_classify_exact:
  for +p: List<&2, String>
  {Cf.classify(p) == cf_hit(cf_rules(), p) : Cf.Hit}

# LAW trust_table_example: anchor: the table is cf_rules; the nested retry counts are
# limits, a nested key under `retry` a preference, a name that only
# starts like a rule's and an unknown key code
# EXCLUDES: a key moved to another class, a limit or credential
#   admitted from an untrusted project, a preference withheld
law trust_table_example:
  {Cf.rules() == cf_rules() : List<&2, Cf.Rule>} &
  {Cf.classify(["retry", "maxRetries"]) == Cf.Hit{"retry.maxRetries", Cf.Proj{Cf.Limit{}}} : Cf.Hit} &
  {Cf.classify(["retry", "failover", "maxRetries"]) == Cf.Hit{"retry.failover.maxRetries", Cf.Proj{Cf.Limit{}}} : Cf.Hit} &
  {Cf.classify(["retry", "failover", "enabled"]) == Cf.Hit{"retry", Cf.Proj{Cf.Pref{}}} : Cf.Hit} &
  {Cf.classify(["mcpServers", "github", "url"]) == Cf.Hit{"mcpServers", Cf.Proj{Cf.Credential{}}} : Cf.Hit} &
  {Cf.classify(["gateway", "signal", "account"]) == Cf.Hit{"gateway", Cf.GlobalOnly{}} : Cf.Hit} &
  {Cf.classify(["SYSTEM.md"]) == Cf.Hit{"SYSTEM.md", Cf.Proj{Cf.Prompt{}}} : Cf.Hit} &
  {Cf.classify(["shellPath"]) == Cf.Hit{"shellPath", Cf.Proj{Cf.Code{}}} : Cf.Hit} &
  {Cf.classify(["themex"]) == Cf.Hit{"themex", Cf.Proj{Cf.Code{}}} : Cf.Hit} &
  {Cf.classify(["unknownKey", "x"]) == Cf.Hit{"unknownKey", Cf.Proj{Cf.Code{}}} : Cf.Hit}

# a key of scope s applies from a project of trust t: a trusted project's
# every key but a global-only one, an untrusted project's preferences
def cf_pref_only(c: Cf.Class) -> Bool:
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

def cf_applies(t: Cf.Trust, s: Cf.Scope) -> Bool:
  match t:
    case Cf.Trusted{}:
      match s:
        case Cf.GlobalOnly{}:
          False{}
        case Cf.Proj{c}:
          True{}
    case Cf.Untrusted{}:
      match s:
        case Cf.GlobalOnly{}:
          False{}
        case Cf.Proj{c}:
          cf_pref_only(c)

# LAW trust_applies_exact: a trusted project applies every key but a global-only one; an
# untrusted project applies only its preferences
# EXCLUDES: a global-only key taken from a trusted project, a limit,
#   prompt, credential or code key taken from an untrusted one
law trust_applies_exact:
  for +t: Cf.Trust
  for s: Cf.Scope
  {Cf.applies(t, s) == cf_applies(t, s) : Bool}

def cf_project.put(ok: Bool, k: Nat, v: Nat, rest: List<&2, Cf.Entry>) -> List<&2, Cf.Entry>:
  match ok:
    case True{}:
      Cf.Entry{k, v} <> rest
    case False{}:
      rest

def cf_scope(h: Cf.Hit) -> Cf.Scope:
  match h:
    case Cf.Hit{n, s}:
      s

# the keys of ks that apply under t, in order, as entries, over g
def cf_project(+t: Cf.Trust, g: List<&2, Cf.Entry>, ks: List<&2, Cf.PKey>) -> List<&2, Cf.Entry>:
  match ks:
    case Nil{}:
      g
    case x <> rest:
      match x:
        case Cf.PKey{k, +p, v}:
          cf_project.put(cf_applies(t, cf_scope(cf_hit(cf_rules(), p))), k, v, cf_project(t, g, rest))

# LAW trust_project_exact: the values that apply from a project are exactly its keys whose
# scope applies under its trust, each with its value, in the document's
# order, before the global values
# EXCLUDES: a withheld key applied, an admitted key dropped, a key given
#   another key's value, keys reordered
law trust_project_exact:
  for +t: Cf.Trust
  for g: List<&2, Cf.Entry>
  for ks: List<&2, Cf.PKey>
  {Cf.project(t, g, ks) == cf_project(t, g, ks) : List<&2, Cf.Entry>}

def cf_names.put(ok: Bool, n: String, rest: List<&2, String>) -> List<&2, String>:
  match ok:
    case True{}:
      rest
    case False{}:
      n <> rest

def cf_names.hit(+t: Cf.Trust, h: Cf.Hit, rest: List<&2, String>) -> List<&2, String>:
  match h:
    case Cf.Hit{n, s}:
      cf_names.put(cf_applies(t, s), n, rest)

# the name of each key of ks that does not apply under t, in order
def cf_names(+t: Cf.Trust, ks: List<&2, Cf.PKey>) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case Cf.PKey{k, +p, v}:
          cf_names.hit(t, cf_hit(cf_rules(), p), cf_names(t, rest))

def cf_seen(ns: List<&2, String>, +n: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(String.eq(x, n), cf_seen(t, n))

def cf_once.add(seen: Bool, n: String, acc: List<&2, String>) -> List<&2, String>:
  match seen:
    case True{}:
      acc
    case False{}:
      List.append(&2, String, acc, [n])

# acc, then each name of ns not named before, in order
def cf_once(ns: List<&2, String>, +acc: List<&2, String>) -> List<&2, String>:
  match ns:
    case Nil{}:
      acc
    case +n <> t:
      cf_once(t, cf_once.add(cf_seen(acc, n), n, acc))

# LAW trust_withheld_exact: the warning names each key that does not apply, once, in the
# order the keys come, by the name its rule gives
# EXCLUDES: a withheld key the warning does not name, a name of a key
#   that applies, a name twice
law trust_withheld_exact:
  for +t: Cf.Trust
  for ks: List<&2, Cf.PKey>
  {Cf.withheld(t, ks) == cf_once(cf_names(t, ks), Nil{}) : List<&2, String>}

# The entry (bend/ffi_config.bend)
# --------------------------------
# R1: every request Rust writes (the grammar in the entry's header, every
#     Nat, length and count within the wire) is answered with the model's
#     decision, spelled as Rust reads it: no field lost, swapped or
#     invented. R2: any input that is not exactly one request (an unknown
#     tag, a malformed field, input left over) is answered with exactly
#     the error form "config: malformed request", never a decision.

# LAW config_ffi_answers: every request Rust writes, every number, length and count within
# the wire, is answered with the model's decision spelled as Rust reads
# it: the write, the leaves that apply and those named, the limits, the
# keys that apply and the withheld names, the merged entries
# EXCLUDES: a field misread, swapped or dropped; a request answered with
#   another request's rule, a default, or a reply spelled otherwise
law config_ffi_answers:
  for +a: FC.Ask
  for fits: {CS.cf_fit_ask(a) == True{} : Bool}
  {FC.ffi(CS.cf_w_ask(a)) == CS.cf_w_reply(a) : String}

# LAW config_ffi_reads_spelled: the laws' reader reads every spelled request that fits the
# wire back whole, so config_ffi_malformed_exact refuses only what Rust
# never writes
# EXCLUDES: a reader (and so an entry) that refuses a request Rust writes
law config_ffi_reads_spelled:
  for +a: FC.Ask
  for fits: {CS.cf_fit_ask(a) == True{} : Bool}
  {CS.cf_read(CS.cf_w_ask(a)) == Some{a} : Maybe<&2, FC.Ask>}

# LAW config_ffi_malformed_exact: every input that is not exactly one request (an unknown
# tag, a malformed field, input left over) gets exactly the error form
# 'E ', then "config: malformed request"
# EXCLUDES: a decision made on input that is no request, another error
#   text, a reply Rust would read as a value
law config_ffi_malformed_exact:
  for +s: String
  for no: {CS.cf_read(s) == None{} : Maybe<&2, FC.Ask>}
  {FC.ffi(s) == SCon{'E', SCon{' ', "config: malformed request"}} : String}

# LAW config_ffi_example: anchor: the strings Rust sends and the replies it reads: a set
# over a parsed document, a broken read, a delete over a missing file,
# leaves, limits, an untrusted project, a merge
# EXCLUDES: tags in another order, a field order other than Rust's
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

# LAW config_ffi_refuses_example: witness: an unknown tag, a bad outcome tag and input left
# over get the error form
# EXCLUDES: a vacuous config_ffi_malformed_exact
law config_ffi_refuses_example:
  {CS.cf_read("5,") == None{} : Maybe<&2, FC.Ask>} &
  {CS.cf_read("1,1,0,3,") == None{} : Maybe<&2, FC.Ask>} &
  {CS.cf_read("0,2,0,0,7,x") == None{} : Maybe<&2, FC.Ask>} &
  {FC.ffi("0,2,0,0,7,x") == SCon{'E', SCon{' ', "config: malformed request"}} : String}

# The helpers the laws read, each pinned
# --------------------------------------
# Every model function a law or spec helper reads is fixed by an exact law
# against a restatement that does not call it (spec/settings/config_rules.bend or
# the helpers above), so no law holds by a pair of helpers wrong together.

# what a setter writes over the read r: the read document with key k set
# to v; nothing over a read that failed
def cf_saved(r: Cf.Read, +k: Nat, +v: Nat) -> Cf.Write:
  match r:
    case Cf.Missing{}:
      Cf.Wrote{cf_edited(Nil{}, Cf.Set{k, v})}
    case Cf.Parsed{+d}:
      Cf.Wrote{cf_edited(d, Cf.Set{k, v})}
    case Cf.Broken{}:
      Cf.Refused{}

# LAW save_exact: a setter writes exactly the document it read on disk with its key set,
# whatever copy it loaded; over a document it could not read it writes
# nothing; over a missing file it writes the one entry
# EXCLUDES: a setter that writes its loaded copy over an unreadable file,
#   a setter that writes its loaded copy at all
law save_exact:
  for loaded: List<&2, Cf.Entry>
  for r: Cf.Read
  for +k: Nat
  for +v: Nat
  {Cf.save(loaded, r, k, v) == cf_saved(r, k, v) : Cf.Write}

# LAW save_refuses_broken_example: anchor: a setter with a loaded copy refuses an unreadable
# file, writes the disk's document (not the copy) with its key set in
# place, and writes a missing file as the one entry
# EXCLUDES: a vacuous save_exact
law save_refuses_broken_example:
  {Cf.save([Cf.Entry{1n, 5n}], Cf.Broken{}, 2n, 7n) == Cf.Refused{} : Cf.Write} &
  {Cf.save([Cf.Entry{1n, 5n}], Cf.Parsed{[Cf.Entry{3n, 1n}, Cf.Entry{1n, 4n}]}, 1n, 9n) == Cf.Wrote{[Cf.Entry{3n, 1n}, Cf.Entry{1n, 9n}]} : Cf.Write} &
  {Cf.save([Cf.Entry{1n, 5n}], Cf.Missing{}, 2n, 7n) == Cf.Wrote{[Cf.Entry{2n, 7n}]} : Cf.Write}

# LAW set_exact: a set of key k to v is the document with every entry of k holding v in
# its place, or a new entry last
# EXCLUDES: settings_save_preserves holding by a wrong set and a save wrong alike
law set_exact:
  for +d: List<&2, Cf.Entry>
  for +k: Nat
  for +v: Nat
  {Cf.set(d, k, v) == cf_edited(d, Cf.Set{k, v}) : List<&2, Cf.Entry>}

# LAW lookup_exact: the value of a key is the value of its first entry, none without one
# EXCLUDES: rmw_keeps_others holding by a lookup that ignores the document
law lookup_exact:
  for d: List<&2, Cf.Entry>
  for +j: Nat
  {Cf.lookup(d, j) == CR.cr_lookup(d, j) : Maybe<&2, Nat>}

# LAW kept_exact: the value of a key in a write is its value in the written document, none
# when nothing was written
# EXCLUDES: rmw_applies_change holding by a kept that answers the set value
law kept_exact:
  for w: Cf.Write
  for +j: Nat
  {Cf.kept(w, j) == CR.cr_kept(w, j) : Maybe<&2, Nat>}

# LAW touches_exact: an edit touches exactly the key it names
# EXCLUDES: rmw_keeps_others made vacuous by an edit that touches every key
law touches_exact:
  for e: Cf.Edit
  for +j: Nat
  {Cf.touches(e, j) == Nat.is_eq(CR.cr_edit_key(e), j) : Bool}

# LAW listed_exact: a number is listed exactly when it is one of the list's
# EXCLUDES: leaf_applied_or_reported holding by a listed that is always true
law listed_exact:
  for ns: List<&2, Nat>
  for +n: Nat
  {Cf.listed(ns, n) == CR.cr_listed(ns, n) : Bool}

# LAW leaf_path_exact: a leaf's path is the path it carries
# EXCLUDES: the leaf laws read at a path the leaf does not have
law leaf_path_exact:
  for l: Cf.Leaf
  {Cf.Leaf.path(l) == CR.cr_path(l) : Nat}

# LAW leaf_in_exact: a leaf is in a list exactly when it is one of its leaves
# EXCLUDES: leaf_applied_or_reported made vacuous by an empty membership
law leaf_in_exact:
  for +l: Cf.Leaf
  for ls: List<&2, Cf.Leaf>
  {Cf.In(l, ls) == CR.cr_in(l, ls) : Type}

# LAW distinct_exact: leaves are distinct exactly when no two share a path
# EXCLUDES: leaf_not_both made vacuous by a distinct that is never true
law distinct_exact:
  for ls: List<&2, Cf.Leaf>
  {Cf.distinct(ls) == CR.cr_distinct(ls) : Bool}

# LAW slot_exact: a provider's slot is the value of its first slot, none without one
# EXCLUDES: limit_number_applies holding by a slot that never answers
law slot_exact:
  for es: List<&2, Cf.Slot>
  for +p: Nat
  {Cf.slot(es, p) == CR.cr_slot(es, p) : Maybe<&2, Cf.Val>}

# LAW val_limit_exact: a slot's limit: 0 is no limit, a whole n is n, a malformed one 1
# EXCLUDES: limit_number_applies holding by a limit and a val_limit wrong alike
law val_limit_exact:
  for v: Cf.Val
  {Cf.val_limit(v) == cf_lim_val(v) : Cf.Lim}

# LAW limit_exact: a provider's limit: unset or no slot is no limit, its first slot's
# limit, a value that is not a map caps at 1
# EXCLUDES: the one-provider limit laws holding by a wrong limit
law limit_exact:
  for s: Cf.InFlight
  for +p: Nat
  {Cf.limit(s, p) == cf_limit(s, p) : Cf.Lim}

# LAW malformed_at_exact: a provider's limit is malformed exactly when its first slot is
# malformed or the value is not a map
# EXCLUDES: limit_malformed_fails_closed made vacuous by a malformed_at that is never true
law malformed_at_exact:
  for s: Cf.InFlight
  for +p: Nat
  {Cf.malformed_at(s, p) == CR.cr_malformed_at(s, p) : Bool}

# LAW effective_exact: the values that apply are the items the trust keeps (every item
# when trusted, the preferences when not), in order, before the global ones
# EXCLUDES: the trust laws holding by an effective that drops or adds items
law effective_exact:
  for +t: Cf.Trust
  for g: List<&2, Cf.Entry>
  for items: List<&2, Cf.Item>
  {Cf.effective(t, g, items) == CR.cr_effective(t, g, items) : List<&2, Cf.Entry>}

# LAW only_guarded_exact: a key is guarded exactly when no item is a preference of it
# EXCLUDES: untrusted_changes_nothing_guarded made vacuous by a premise never true
law only_guarded_exact:
  for items: List<&2, Cf.Item>
  for +k: Nat
  {Cf.only_guarded(items, k) == CR.cr_only_guarded(items, k) : Bool}

# LAW has_exact: a map has a name exactly when one of its entries has it
# EXCLUDES: the merge laws made vacuous or misapplied by a wrong has
law has_exact:
  for es: List<&2, Cf.Named>
  for +n: Nat
  {Cf.has(es, n) == CR.cr_has(es, n) : Bool}

# LAW find_exact: the entry of a name is the first entry of that name, none without one
# EXCLUDES: project_entry_never_merges holding by a find that ignores the map
law find_exact:
  for es: List<&2, Cf.Named>
  for +n: Nat
  {Cf.find(es, n) == cf_find(es, n) : Maybe<&2, List<&2, Cf.Entry>>}

def cf_finds(+es: List<&2, Cf.Named>, qs: List<&2, Nat>) -> List<&2, Maybe<&2, List<&2, Cf.Entry>>>:
  match qs:
    case Nil{}:
      Nil{}
    case q <> t:
      cf_find(es, q) <> cf_finds(es, t)

# LAW finds_exact: the entries of names qs are, in order, the entry of each
# EXCLUDES: an answer for another name or in another order
law finds_exact:
  for +es: List<&2, Cf.Named>
  for qs: List<&2, Nat>
  {Cf.finds(es, qs) == cf_finds(es, qs) : List<&2, Maybe<&2, List<&2, Cf.Entry>>>}

# LAW merge_find_exact: in the merged map a name's entry is the project's entry whole,
# else the global one whole, else none
# EXCLUDES: a merged map whose entries only finds reads right
law merge_find_exact:
  for +g: List<&2, Cf.Named>
  for p: List<&2, Cf.Named>
  for +n: Nat
  {Cf.find(Cf.merge(g, p), n) == cf_or(cf_find(p, n), cf_find(g, n)) : Maybe<&2, List<&2, Cf.Entry>>}
