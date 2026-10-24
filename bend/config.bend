# config: what eukhe does with its config documents (settings.json,
# mcp-connections.json, auth.json) and with the layers over them. This is
# the code that runs: bend/ffi_config.bend is its entry in the compiled
# core, and the Rust (crates/eukhe-core/src/settings/, mcp/
# connection_store.rs, auth/, admission.rs, resources/) reads and writes
# the files, turns their bytes into the facts below, and acts on the
# answer. The laws are laws/config.bend.
#
# A document is a list of entries: a key and a value, both numbers (a
# key stands for a key path, a value for the JSON at it; the Rust keeps
# the names and the values and sends their places).

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

def pick_v(b: Bool, v: Nat, w: Nat) -> Nat:
  match b:
    case True{}:
      v
    case False{}:
      w

# d with every entry of key k holding v, each in its place
def replace(d: List<&2, Entry>, +k: Nat, +v: Nat) -> List<&2, Entry>:
  match d:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Entry{+j, w}:
          Entry{j, pick_v(Nat.is_eq(j, k), v, w)} <> replace(rest, k, v)

# an entry of d has key k
def has_key(d: List<&2, Entry>, +k: Nat) -> Bool:
  match d:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Entry{j, v}:
          Bool.or(Nat.is_eq(j, k), has_key(rest, k))

def set.go(b: Bool, d: List<&2, Entry>, +k: Nat, +v: Nat) -> List<&2, Entry>:
  match b:
    case True{}:
      replace(d, k, v)
    case False{}:
      List.append(&2, Entry, d, [Entry{k, v}])

# d with key k set to v: a key d has keeps its place (every other key
# keeps its place too), a new key goes last
def set(+d: List<&2, Entry>, +k: Nat, +v: Nat) -> List<&2, Entry>:
  set.go(has_key(d, k), d, k, v)

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

# the in-flight limit of each provider of qs, in order
def limits(+s: InFlight, qs: List<&2, Nat>) -> List<&2, Lim>:
  match qs:
    case Nil{}:
      Nil{}
    case q <> rest:
      limit(s, q) <> limits(s, rest)

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
# prompt file, a credential (or what routes one) and a key that runs or
# installs code (or that no rule names) are withheld.

type Class is Data:
  Pref{}
  Limit{}
  Prompt{}
  Credential{}
  Code{}

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
        case Code{}:
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
    case Code{}:
      True{}

# no preference item of the project has key k (every item of key k is a
# limit, a prompt, a credential or code)
def only_guarded(items: List<&2, Item>, +k: Nat) -> Bool:
  match items:
    case Nil{}:
      True{}
    case i <> rest:
      match i:
        case Item{j, kind, v}:
          Bool.and(guarded_at(j, kind, k), only_guarded(rest, k))

# Project keys by name
# --------------------
# The Rust sends each leaf of the project document (a value that is not
# an object, or an empty object) as a key: its place, its path (the key
# names from the top) and its value's place; a project prompt file is
# the key of its file name. The first rule whose path is a prefix of the
# key's path says what the key is (the table lists a nested rule before
# the rule of its parent); a key no rule names runs code as far as a
# project knows: it is withheld from an untrusted project. A global-only
# key never applies from a project, trusted or not. Every withheld key is
# named once in the warning: by its rule's path (the names joined by
# '.'), or by its first name when no rule names it.

type Scope is Data:
  Proj{c: Class}
  GlobalOnly{}

type Rule is Data:
  Rule{p: List<&2, String>, s: Scope}

type Hit is Data:
  Hit{name: String, s: Scope}

type PKey is Data:
  PKey{k: Nat, p: List<&2, String>, v: Nat}

# what each key of a settings document is; nested rules first
def rules() -> List<&2, Rule>:
  [
    Rule{["retry", "maxRetries"], Proj{Limit{}}},
    Rule{["retry", "failover", "maxRetries"], Proj{Limit{}}},
    Rule{["onboardingShown"], Proj{Pref{}}},
    Rule{["onboardingCompleted"], Proj{Pref{}}},
    Rule{["defaultProvider"], Proj{Pref{}}},
    Rule{["defaultModel"], Proj{Pref{}}},
    Rule{["subagentDefaultModel"], Proj{Pref{}}},
    Rule{["recentModels"], Proj{Pref{}}},
    Rule{["auxiliaryModel"], Proj{Pref{}}},
    Rule{["defaultThinkingLevel"], Proj{Pref{}}},
    Rule{["defaultServiceTier"], Proj{Pref{}}},
    Rule{["rlmMaxDepth"], Proj{Pref{}}},
    Rule{["providerMaxInFlight"], Proj{Pref{}}},
    Rule{["providerMaxQueued"], Proj{Pref{}}},
    Rule{["idleEvictionMinutes"], Proj{Pref{}}},
    Rule{["sessionArchiveMaxAgeDays"], Proj{Pref{}}},
    Rule{["sessionArchiveMaxSessions"], Proj{Pref{}}},
    Rule{["transport"], Proj{Pref{}}},
    Rule{["steeringMode"], Proj{Pref{}}},
    Rule{["followUpMode"], Proj{Pref{}}},
    Rule{["theme"], Proj{Pref{}}},
    Rule{["compaction"], Proj{Pref{}}},
    Rule{["memory"], Proj{Pref{}}},
    Rule{["autoRefine"], Proj{Pref{}}},
    Rule{["branchSummary"], Proj{Pref{}}},
    Rule{["retry"], Proj{Pref{}}},
    Rule{["providerBackupModel"], Proj{Pref{}}},
    Rule{["imageModel"], Proj{Pref{}}},
    Rule{["prompts"], Proj{Pref{}}},
    Rule{["themes"], Proj{Pref{}}},
    Rule{["enableSkillCommands"], Proj{Pref{}}},
    Rule{["enableBuiltinSkills"], Proj{Pref{}}},
    Rule{["terminal"], Proj{Pref{}}},
    Rule{["images"], Proj{Pref{}}},
    Rule{["enabledModels"], Proj{Pref{}}},
    Rule{["treeFilterMode"], Proj{Pref{}}},
    Rule{["chatDetail"], Proj{Pref{}}},
    Rule{["editorPaddingX"], Proj{Pref{}}},
    Rule{["autocompleteMaxVisible"], Proj{Pref{}}},
    Rule{["showHardwareCursor"], Proj{Pref{}}},
    Rule{["markdown"], Proj{Pref{}}},
    Rule{["workflow"], Proj{Pref{}}},
    Rule{["warnings"], Proj{Pref{}}},
    Rule{["requestTiming"], Proj{Pref{}}},
    Rule{["modelRoles"], Proj{Pref{}}},
    Rule{["titles"], Proj{Pref{}}},
    Rule{["tts"], Proj{Pref{}}},
    Rule{["stt"], Proj{Pref{}}},
    Rule{["subagentMaxConcurrency"], Proj{Limit{}}},
    Rule{["subagentStallMs"], Proj{Limit{}}},
    Rule{["toolBlockingBudgetMs"], Proj{Limit{}}},
    Rule{["maxToolRounds"], Proj{Limit{}}},
    Rule{["autonomous"], Proj{Limit{}}},
    Rule{["directors"], Proj{Limit{}}},
    Rule{["thinkingBudgets"], Proj{Limit{}}},
    Rule{["SYSTEM.md"], Proj{Prompt{}}},
    Rule{["APPEND_SYSTEM.md"], Proj{Prompt{}}},
    Rule{["mcpServers"], Proj{Credential{}}},
    Rule{["kernelTransport"], Proj{Credential{}}},
    Rule{["providers"], Proj{Credential{}}},
    Rule{["trustedProjects"], GlobalOnly{}},
    Rule{["gateway"], GlobalOnly{}},
    Rule{["ssh"], GlobalOnly{}}
  ]

# path a is a prefix of path b, name by name
def prefix(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a:
    case Nil{}:
      True{}
    case x <> xs:
      match b:
        case Nil{}:
          False{}
        case y <> ys:
          Bool.and(String.eq(x, y), prefix(xs, ys))

# the names of p joined by '.'
def join(p: List<&2, String>) -> String:
  match p:
    case Nil{}:
      ""
    case x <> xs:
      match xs:
        case Nil{}:
          x
        case y <> ys:
          String.append(x, SCon{'.', join(y <> ys)})

# the first name of p
def first_name(p: List<&2, String>) -> String:
  match p:
    case Nil{}:
      ""
    case x <> xs:
      x

def classify.pick(b: Bool, q: List<&2, String>, s: Scope, later: Hit) -> Hit:
  match b:
    case True{}:
      Hit{join(q), s}
    case False{}:
      later

def classify.go(rs: List<&2, Rule>, +p: List<&2, String>) -> Hit:
  match rs:
    case Nil{}:
      Hit{first_name(p), Proj{Code{}}}
    case r <> rest:
      match r:
        case Rule{+q, s}:
          classify.pick(prefix(q, p), q, s, classify.go(rest, p))

# what the key of path p is, and the name the warning gives it
def classify(+p: List<&2, String>) -> Hit:
  classify.go(rules(), p)

def Hit.scope(h: Hit) -> Scope:
  match h:
    case Hit{n, s}:
      s

def Hit.name(h: Hit) -> String:
  match h:
    case Hit{n, s}:
      n

# a key of scope s applies from a project of trust t
def applies(+t: Trust, s: Scope) -> Bool:
  match s:
    case Proj{c}:
      admits(t, c)
    case GlobalOnly{}:
      False{}

def item.of(s: Scope, k: Nat, v: Nat, rest: List<&2, Item>) -> List<&2, Item>:
  match s:
    case Proj{c}:
      Item{k, c, v} <> rest
    case GlobalOnly{}:
      rest

# the project items of the keys: a global-only key is none
def items(ks: List<&2, PKey>) -> List<&2, Item>:
  match ks:
    case Nil{}:
      Nil{}
    case x <> rest:
      match x:
        case PKey{k, +p, v}:
          item.of(Hit.scope(classify(p)), k, v, items(rest))

# the values that apply: the keys of a project of trust t over g
def project(+t: Trust, g: List<&2, Entry>, ks: List<&2, PKey>) -> List<&2, Entry>:
  effective(t, g, items(ks))

# n is one of ns
def named(ns: List<&2, String>, +n: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(String.eq(x, n), named(rest, n))

def withheld.put(seen: Bool, n: String, acc: List<&2, String>) -> List<&2, String>:
  match seen:
    case True{}:
      acc
    case False{}:
      List.append(&2, String, acc, [n])

def withheld.add(ok: Bool, +n: String, +acc: List<&2, String>) -> List<&2, String>:
  match ok:
    case True{}:
      acc
    case False{}:
      withheld.put(named(acc, n), n, acc)

def withheld.step(+t: Trust, h: Hit, acc: List<&2, String>) -> List<&2, String>:
  match h:
    case Hit{n, s}:
      withheld.add(applies(t, s), n, acc)

def withheld.go(+t: Trust, ks: List<&2, PKey>, acc: List<&2, String>) -> List<&2, String>:
  match ks:
    case Nil{}:
      acc
    case x <> rest:
      match x:
        case PKey{k, +p, v}:
          withheld.go(t, rest, withheld.step(t, classify(p), acc))

# the names of the keys that do not apply, each once, in order
def withheld(+t: Trust, ks: List<&2, PKey>) -> List<&2, String>:
  withheld.go(t, ks, Nil{})

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

# the entry of each name of qs in es, in order
def finds(+es: List<&2, Named>, qs: List<&2, Nat>) -> List<&2, Maybe<&2, List<&2, Entry>>>:
  match qs:
    case Nil{}:
      Nil{}
    case q <> rest:
      find(es, q) <> finds(es, rest)
