# aux_fallback: where a summarizer pass runs, and the notice a session
# shows when the `auxiliaryModel` setting is set but not used. The Rust
# code is crates/eukhe-core/src/durable/compaction/auxiliary_model.rs
# (`decide_auxiliary_route` and `AuxiliaryNotices::take`); the compaction
# summary and the daemon's branch summary both use it.
#
# A pass has a purpose, the selector the setting names, whether
# `allowedModels` admits it, what the resolver's own lookups found, and
# the size of the request (0: unknown). The decision checks in order:
#
#   - an unset selector, or one that names the session model, keeps the
#     session model (nothing is put in its place);
#   - a selector `allowedModels` does not admit falls back (reason 0);
#   - a lookup that finds nothing usable falls back with its reason
#     (1: the model list was not read, 2: not found, 3: no key, 4: not in
#     the session's collection);
#   - a found model whose known window (not 0) is smaller than the
#     request falls back (reason 5);
#   - else the pass runs on the selector's model.
#
# A session runs passes in order. Each fallback is a substitution event
# with its key (purpose, selector, reason). The first fallback of each
# key in the session is also a notice event with that key; a key the
# session has shown stays quiet.

import Base

# The selector the setting names.
type Sel is Data:
  Unset{}
  Same{}
  Other{s: Nat}

# What the resolver's lookups found: nothing usable (with the reason), or
# a model with its context window.
type Look is Data:
  Miss{r: Nat}
  Hit{w: Nat}

# One summarizer pass.
type Pass is Data:
  Pass{p: Nat, sel: Sel, ok: Bool, look: Look, need: Nat}

# The key of a fallback: the purpose, the selector and the reason.
type Key is Data:
  K{p: Nat, s: Nat, r: Nat}

# Where a pass runs.
type Route is Data:
  Session{}
  Routed{}
  Fallback{k: Key}

# What a pass shows: it stayed on the session model, it ran on the
# selector's model, the session model was put in place of the selector,
# or a notice of that.
type Ev is Data:
  Stay{}
  Went{}
  Sub{k: Key}
  Note{k: Key}

# The decision
# ------------

# a known window w is not smaller than the request; an unknown one (0)
# fits
def fits(w: Nat, +need: Nat) -> Bool:
  match w:
    case 0n:
      True{}
    case 1n+x:
      Bool.not(Nat.is_lt(1n+x, need))

def fits.route(b: Bool, p: Nat, s: Nat) -> Route:
  match b:
    case True{}:
      Routed{}
    case False{}:
      Fallback{K{p, s, 5n}}

# the lookups of an admitted selector s
def found(+p: Nat, +s: Nat, look: Look, +need: Nat) -> Route:
  match look:
    case Miss{r}:
      Fallback{K{p, s, r}}
    case Hit{w}:
      fits.route(fits(w, need), p, s)

# What the decision knows before the resolver's lookups (which read the
# catalog, the credentials and the session's models, so they run only
# when needed): the route, or that the lookups of the selector s for the
# purpose p must run.
type Gate is Data:
  Known{r: Route}
  Lookup{p: Nat, s: Nat}

# the selector, then the allowedModels check
def gate(p: Nat, sel: Sel, ok: Bool) -> Gate:
  match sel:
    case Unset{}:
      Known{Session{}}
    case Same{}:
      Known{Session{}}
    case Other{s}:
      match ok:
        case True{}:
          Lookup{p, s}
        case False{}:
          Known{Fallback{K{p, s, 0n}}}

# the route, given the gate and what the lookups found (read only when
# the gate asked for them)
def settle(g: Gate, look: Look, +need: Nat) -> Route:
  match g:
    case Known{r}:
      r
    case Lookup{p, s}:
      found(p, s, look, need)

# where the pass x runs
def decide(x: Pass) -> Route:
  match x:
    case Pass{p, sel, ok, look, need}:
      settle(gate(p, sel, ok), look, need)

# The session
# -----------

def Key.eq(a: Key, b: Key) -> Bool:
  match a b:
    case K{ap, as1, ar} K{bp, bs1, br}:
      Bool.and(Nat.is_eq(ap, bp), Bool.and(Nat.is_eq(as1, bs1), Nat.is_eq(ar, br)))

# the key k is in ks
def listed(ks: List<&2, Key>, +k: Key) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(Key.eq(x, k), listed(rest, k))

# the notice of k, before the events t, when the session has not shown k
def noted(seen: Bool, k: Key, t: List<&2, Ev>) -> List<&2, Ev>:
  match seen:
    case True{}:
      t
    case False{}:
      Note{k} <> t

# the keys shown after k: k joins when the session had not shown it
def shown(seen: Bool, k: Key, sh: List<&2, Key>) -> List<&2, Key>:
  match seen:
    case True{}:
      sh
    case False{}:
      k <> sh

# the events of a pass routed r, before the events t of the passes after
# it; sh is the keys the session has shown
def put(r: Route, +sh: List<&2, Key>, t: List<&2, Ev>) -> List<&2, Ev>:
  match r:
    case Session{}:
      Stay{} <> t
    case Routed{}:
      Went{} <> t
    case Fallback{+k}:
      Sub{k} <> noted(listed(sh, k), k, t)

# the keys shown after a pass routed r
def after(r: Route, +sh: List<&2, Key>) -> List<&2, Key>:
  match r:
    case Session{}:
      sh
    case Routed{}:
      sh
    case Fallback{+k}:
      shown(listed(sh, k), k, sh)

# the events of the passes ps, with the keys sh already shown
def go(ps: List<&2, Pass>, +sh: List<&2, Key>) -> List<&2, Ev>:
  match ps:
    case Nil{}:
      Nil{}
    case +x <> rest:
      put(decide(x), sh, go(rest, after(decide(x), sh)))

# the events of a session that runs the passes ps
def run(ps: List<&2, Pass>) -> List<&2, Ev>:
  go(ps, Nil{})

# the keys of the substitution events of es
def subs(es: List<&2, Ev>) -> List<&2, Key>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Stay{}:
          subs(rest)
        case Went{}:
          subs(rest)
        case Sub{k}:
          k <> subs(rest)
        case Note{k}:
          subs(rest)

# the keys of the notice events of es
def notes(es: List<&2, Ev>) -> List<&2, Key>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Stay{}:
          notes(rest)
        case Went{}:
          notes(rest)
        case Sub{k}:
          notes(rest)
        case Note{k}:
          k <> notes(rest)
