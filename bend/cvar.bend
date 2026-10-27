# cvar: the model of settings as console variables. Each setting (a cvar) is declared once, with a type, a scope, and
# flags for persistence and replication. Values come in layers; a higher
# layer wins:
#
#   default < config.cfg < the agent's profile (subagent.cfg, <agent>.cfg)
#           < the agent's own sets
#
# A subagent starts from its parent's values: its profile and its sets go
# on top of them. A Global cvar has one value for the whole family: a
# profile or a set of it in an agent is rejected. A set with a value of
# the wrong type is rejected. A set of an undeclared cvar is rejected.
#
# Commands share one language: set, toggle, and run of an alias. An alias
# names a list of commands. A key bind names the commands a key press
# runs; a press expands them like any command list. Expansion nests at
# most as many aliases deep as the table holds: a deeper nest repeats an
# alias, so it is a cycle. An error names its alias (the run at which the
# nesting ran out, or the alias that does not exist), and the first error,
# left to right, stops the expansion.
#
# A recursive scan takes the test of its first item as a parameter (Bend
# matches only parameters); `*.at` computes that test.

import Base

# Types and values
# ----------------

type Ty is Data:
  TNat{}
  TBool{}

type Val is Data:
  VNat{n: Nat}
  VBool{b: Bool}

def Val.ty(v: Val) -> Ty:
  match v:
    case VNat{n}:
      TNat{}
    case VBool{b}:
      TBool{}

def Ty.eq(a: Ty, b: Ty) -> Bool:
  match a b:
    case TNat{} TNat{}:
      True{}
    case TNat{} TBool{}:
      False{}
    case TBool{} TNat{}:
      False{}
    case TBool{} TBool{}:
      True{}

type Scope is Data:
  Global{}  # one value for the whole family
  Local{}   # each agent may have its own value

# A declaration
type Decl is Data:
  Decl{id: Nat, ty: Ty, scope: Scope, persist: Bool, replicate: Bool, init: Val}

def Decl.id(d: Decl) -> Nat:
  match d:
    case Decl{i, t, s, p, r, v}:
      i

def Decl.ty(d: Decl) -> Ty:
  match d:
    case Decl{i, t, s, p, r, v}:
      t

def Decl.local(d: Decl) -> Bool:
  match d:
    case Decl{i, t, s, p, r, v}:
      match s:
        case Global{}:
          False{}
        case Local{}:
          True{}

def Decl.persist(d: Decl) -> Bool:
  match d:
    case Decl{i, t, s, p, r, v}:
      p

def Decl.replicate(d: Decl) -> Bool:
  match d:
    case Decl{i, t, s, p, r, v}:
      r

def Decl.init(d: Decl) -> Val:
  match d:
    case Decl{i, t, s, p, r, v}:
      v

# a declaration's default has its type
def Decl.typed(d: Decl) -> Bool:
  match d:
    case Decl{i, t, s, p, r, v}:
      Ty.eq(Val.ty(v), t)

# The registry
# ------------

# the first declaration of ds has id x
def id.at(+ds: List<&2, Decl>, +x: Nat) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> rest:
      Nat.is_eq(Decl.id(d), x)

# the declaration of x; hit is id.at(ds, x)
def find.go(ds: List<&2, Decl>, +x: Nat, hit: Bool) -> Maybe<&2, Decl>:
  match ds:
    case Nil{}:
      None{}
    case d <> +rest:
      match hit:
        case True{}:
          Some{d}
        case False{}:
          find.go(rest, x, id.at(rest, x))

def find(+ds: List<&2, Decl>, +x: Nat) -> Maybe<&2, Decl>:
  find.go(ds, x, id.at(ds, x))

# add d to ds, or keep ds when d's id is taken or its default has the
# wrong type
def declare.at(taken: Bool, good: Bool, +ds: List<&2, Decl>, +d: Decl) -> List<&2, Decl>:
  match taken:
    case True{}:
      ds
    case False{}:
      match good:
        case True{}:
          List.append(&2, Decl, ds, [d])
        case False{}:
          ds

def declare(+ds: List<&2, Decl>, +d: Decl) -> List<&2, Decl>:
  declare.at(Maybe.is_some(&2, Decl, find(ds, Decl.id(d))), Decl.typed(d), ds, d)

# the registry of the declarations xs, onto ds
def registry.go(xs: List<&2, Decl>, +ds: List<&2, Decl>) -> List<&2, Decl>:
  match xs:
    case Nil{}:
      ds
    case d <> rest:
      registry.go(rest, declare(ds, d))

def registry(xs: List<&2, Decl>) -> List<&2, Decl>:
  registry.go(xs, Nil{})

# no two declarations of ds share an id
def unique(ds: List<&2, Decl>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case +d <> +rest:
      Bool.and(Bool.not(Maybe.is_some(&2, Decl, find(rest, Decl.id(d)))), unique(rest))

# every declaration of ds is well typed
def all_typed(ds: List<&2, Decl>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case +d <> rest:
      Bool.and(Decl.typed(d), all_typed(rest))

# Layers of values
# ----------------

type Bind is Data:
  Bind{id: Nat, val: Val}

def Bind.id(s: Bind) -> Nat:
  match s:
    case Bind{i, v}:
      i

def Bind.val(s: Bind) -> Val:
  match s:
    case Bind{i, v}:
      v

# which layer a set comes from
type Layer is Data:
  Config{}  # config.cfg: Global and Local cvars
  Agent{}   # a profile or an agent's own set: Local cvars only

# the set s is valid in layer l under declaration m
def valid.at(m: Maybe<&2, Decl>, l: Layer, +s: Bind) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+d}:
      match l:
        case Config{}:
          Ty.eq(Val.ty(Bind.val(s)), Decl.ty(d))
        case Agent{}:
          Bool.and(Decl.local(d), Ty.eq(Val.ty(Bind.val(s)), Decl.ty(d)))

def valid(+ds: List<&2, Decl>, l: Layer, +s: Bind) -> Bool:
  valid.at(find(ds, Bind.id(s)), l, s)

# the first set of ss is a valid set of x in layer l
def hit.at(+ss: List<&2, Bind>, +ds: List<&2, Decl>, +l: Layer, +x: Nat) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case +s <> rest:
      Bool.and(Nat.is_eq(Bind.id(s), x), valid(ds, l, s))

# the value of x in layer l: the last valid set of x in ss, else cur;
# hit is hit.at(ss, ds, l, x)
def layer.go(ss: List<&2, Bind>, +ds: List<&2, Decl>, +l: Layer, +x: Nat, cur: Maybe<&2, Val>, hit: Bool) -> Maybe<&2, Val>:
  match ss:
    case Nil{}:
      cur
    case s <> +rest:
      match hit:
        case True{}:
          layer.go(rest, ds, l, x, Some{Bind.val(s)}, hit.at(rest, ds, l, x))
        case False{}:
          layer.go(rest, ds, l, x, cur, hit.at(rest, ds, l, x))

def layer(+ss: List<&2, Bind>, +ds: List<&2, Decl>, +l: Layer, +x: Nat, cur: Maybe<&2, Val>) -> Maybe<&2, Val>:
  layer.go(ss, ds, l, x, cur, hit.at(ss, ds, l, x))

# An agent: its profile and its own sets
type Ag is Data:
  Ag{profile: List<&2, Bind>, sets: List<&2, Bind>}

def Ag.profile(a: Ag) -> List<&2, Bind>:
  match a:
    case Ag{p, s}:
      p

def Ag.sets(a: Ag) -> List<&2, Bind>:
  match a:
    case Ag{p, s}:
      s

# The values
# ----------

# the value of x on top of base: the agent's profile, then its sets
def over(+ds: List<&2, Decl>, +a: Ag, +x: Nat, base: Val) -> Val:
  Maybe.default(&2, Val, layer(Ag.sets(a), ds, Agent{}, x, layer(Ag.profile(a), ds, Agent{}, x, None{})), base)

# the value of x for the family: config.cfg on the default
def root.val(+ds: List<&2, Decl>, +cfg: List<&2, Bind>, +x: Nat, d: Decl) -> Val:
  Maybe.default(&2, Val, layer(cfg, ds, Config{}, x, None{}), Decl.init(d))

# the value of x down a family chain (root first), from base
def chain(fam: List<&2, Ag>, +ds: List<&2, Decl>, +x: Nat, base: Val) -> Val:
  match fam:
    case Nil{}:
      base
    case a <> rest:
      chain(rest, ds, x, over(ds, a, x, base))

def value.at(m: Maybe<&2, Decl>, +ds: List<&2, Decl>, +cfg: List<&2, Bind>, fam: List<&2, Ag>, +x: Nat) -> Maybe<&2, Val>:
  match m:
    case None{}:
      None{}
    case Some{d}:
      Some{chain(fam, ds, x, root.val(ds, cfg, x, d))}

# The value of cvar x for the last agent of the family chain fam (root
# first) with config.cfg cfg; None when x is not declared
def value(+ds: List<&2, Decl>, +cfg: List<&2, Bind>, +fam: List<&2, Ag>, +x: Nat) -> Maybe<&2, Val>:
  value.at(find(ds, x), ds, cfg, fam, x)

# a value has the type of its declaration (or both are absent)
def typed.at(m: Maybe<&2, Decl>, v: Maybe<&2, Val>) -> Bool:
  match m:
    case None{}:
      match v:
        case None{}:
          True{}
        case Some{y}:
          False{}
    case Some{d}:
      match v:
        case None{}:
          False{}
        case Some{y}:
          Ty.eq(Val.ty(y), Decl.ty(d))

# Persistence and replication
# ---------------------------

type Flag is Data:
  Persist{}
  Replicate{}

# the cvar of declaration m has flag f
def flag.at(m: Maybe<&2, Decl>, f: Flag) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{d}:
      match f:
        case Persist{}:
          Decl.persist(d)
        case Replicate{}:
          Decl.replicate(d)

# the first set of ss is a valid agent set of a cvar with flag f
def out.at(+ss: List<&2, Bind>, +ds: List<&2, Decl>, +f: Flag) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case +s <> rest:
      Bool.and(flag.at(find(ds, Bind.id(s)), f), valid(ds, Agent{}, s))

# the sets an agent writes to its cfg (Persist) or replicates
# (Replicate): only valid sets of cvars with that flag, in order; hit is
# out.at(ss, ds, f)
def written.go(ss: List<&2, Bind>, +ds: List<&2, Decl>, +f: Flag, hit: Bool) -> List<&2, Bind>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> +rest:
      match hit:
        case True{}:
          s <> written.go(rest, ds, f, out.at(rest, ds, f))
        case False{}:
          written.go(rest, ds, f, out.at(rest, ds, f))

def written(+ss: List<&2, Bind>, +ds: List<&2, Decl>, +f: Flag) -> List<&2, Bind>:
  written.go(ss, ds, f, out.at(ss, ds, f))

# every set of ss is of a cvar with flag f
def all_flag(ss: List<&2, Bind>, +ds: List<&2, Decl>, +f: Flag) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case +s <> rest:
      Bool.and(flag.at(find(ds, Bind.id(s)), f), all_flag(rest, ds, f))

# Toggle
# ------

# the set that toggles a Bool value v of x (None for another type)
def flip(+x: Nat, v: Maybe<&2, Val>) -> Maybe<&2, Bind>:
  match v:
    case None{}:
      None{}
    case Some{y}:
      match y:
        case VNat{n}:
          None{}
        case VBool{b}:
          Some{Bind{x, VBool{Bool.not(b)}}}

# an agent with one more set (no change for None)
def add(a: Ag, s: Maybe<&2, Bind>) -> Ag:
  match a:
    case Ag{p, ss}:
      match s:
        case None{}:
          Ag{p, ss}
        case Some{t}:
          Ag{p, List.append(&2, Bind, ss, [t])}

# agent a, the last of the family chain fam ++ [a], after a toggle of x:
# it flips the value a has, inherited values included
def toggle(+ds: List<&2, Decl>, +cfg: List<&2, Bind>, +fam: List<&2, Ag>, +a: Ag, +x: Nat) -> Ag:
  add(a, flip(x, value(ds, cfg, List.append(&2, Ag, fam, [a]), x)))

# Commands
# --------

type Cmd is Data:
  CSet{id: Nat, val: Val}
  CToggle{id: Nat}
  CRun{name: Nat}
  CGone{name: Nat}  # a run of an alias that does not exist

type Alias is Data:
  Alias{name: Nat, body: List<&2, Cmd>}

def name.at(+as: List<&2, Alias>, +n: Nat) -> Bool:
  match as:
    case Nil{}:
      False{}
    case a <> rest:
      match a:
        case Alias{m, b}:
          Nat.is_eq(m, n)

# the body of alias n, or [CGone{n}]; hit is name.at(as, n)
def body.go(as: List<&2, Alias>, +n: Nat, hit: Bool) -> List<&2, Cmd>:
  match as:
    case Nil{}:
      [CGone{n}]
    case Alias{m, b} <> +rest:
      match hit:
        case True{}:
          b
        case False{}:
          body.go(rest, n, name.at(rest, n))

def body(+as: List<&2, Alias>, +n: Nat) -> List<&2, Cmd>:
  body.go(as, n, name.at(as, n))

# The outcome of an expansion
type Exp is Data:
  Flat{cmds: List<&2, Cmd>}  # the commands to run; no alias left
  Cycle{name: Nat}           # an alias runs itself: the run at which the
                             # nesting ran out
  Unknown{name: Nat}         # a run of alias name, which does not exist

# xs reversed onto acc
def rev(xs: List<&2, Cmd>, acc: List<&2, Cmd>) -> List<&2, Cmd>:
  match xs:
    case Nil{}:
      acc
    case x <> rest:
      rev(rest, x <> acc)

# expand cs with d levels of alias nesting left, onto acc: the commands
# so far, last first, or the first error, which stops the expansion (no
# command after it is looked at)
def expand.go(d: Nat, cs: List<&2, Cmd>, +as: List<&2, Alias>, acc: Exp) -> Exp:
  match d:
    case 0n:
      match cs:
        case Nil{}:
          acc
        case c <> rest:
          match c:
            case CSet{i, v}:
              match acc:
                case Flat{out}:
                  expand.go(0n, rest, as, Flat{CSet{i, v} <> out})
                case Cycle{m}:
                  Cycle{m}
                case Unknown{m}:
                  Unknown{m}
            case CToggle{i}:
              match acc:
                case Flat{out}:
                  expand.go(0n, rest, as, Flat{CToggle{i} <> out})
                case Cycle{m}:
                  Cycle{m}
                case Unknown{m}:
                  Unknown{m}
            case CRun{n}:
              match acc:
                case Flat{out}:
                  Cycle{n}
                case Cycle{m}:
                  Cycle{m}
                case Unknown{m}:
                  Unknown{m}
            case CGone{n}:
              match acc:
                case Flat{out}:
                  Unknown{n}
                case Cycle{m}:
                  Cycle{m}
                case Unknown{m}:
                  Unknown{m}
    case 1n+(+e):
      match cs:
        case Nil{}:
          acc
        case c <> rest:
          match c:
            case CSet{i, v}:
              match acc:
                case Flat{out}:
                  expand.go(1n+e, rest, as, Flat{CSet{i, v} <> out})
                case Cycle{m}:
                  Cycle{m}
                case Unknown{m}:
                  Unknown{m}
            case CToggle{i}:
              match acc:
                case Flat{out}:
                  expand.go(1n+e, rest, as, Flat{CToggle{i} <> out})
                case Cycle{m}:
                  Cycle{m}
                case Unknown{m}:
                  Unknown{m}
            case CRun{n}:
              match acc:
                case Flat{out}:
                  expand.go(1n+e, rest, as, expand.go(e, body(as, n), as, Flat{out}))
                case Cycle{m}:
                  Cycle{m}
                case Unknown{m}:
                  Unknown{m}
            case CGone{n}:
              match acc:
                case Flat{out}:
                  Unknown{n}
                case Cycle{m}:
                  Cycle{m}
                case Unknown{m}:
                  Unknown{m}

# the commands of an expansion in order (they were gathered last first)
def fin(e: Exp) -> Exp:
  match e:
    case Flat{out}:
      Flat{rev(out, Nil{})}
    case Cycle{n}:
      Cycle{n}
    case Unknown{n}:
      Unknown{n}

# expand cs with the alias table as: the top level and one level per
# alias; nesting deeper than that repeats an alias, so it is a cycle
def expand(cs: List<&2, Cmd>, +as: List<&2, Alias>) -> Exp:
  fin(expand.go(1n+List.length(&2, Alias, as), cs, as, Flat{Nil{}}))

# cs holds no run of an alias
def plain(cs: List<&2, Cmd>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> rest:
      match c:
        case CSet{i, v}:
          plain(rest)
        case CToggle{i}:
          plain(rest)
        case CRun{n}:
          False{}
        case CGone{n}:
          False{}

def Exp.plain(e: Exp) -> Bool:
  match e:
    case Flat{cs}:
      plain(cs)
    case Cycle{n}:
      True{}
    case Unknown{n}:
      True{}

# Key binds
# ---------

type KeyBind is Data:
  KeyBind{key: Nat, cmds: List<&2, Cmd>}

def key.at(+bs: List<&2, KeyBind>, +k: Nat) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case b <> rest:
      match b:
        case KeyBind{j, c}:
          Nat.is_eq(j, k)

# the commands bound to key k (the first bind of k), or none; hit is
# key.at(bs, k)
def bound.go(bs: List<&2, KeyBind>, +k: Nat, hit: Bool) -> List<&2, Cmd>:
  match bs:
    case Nil{}:
      Nil{}
    case KeyBind{j, c} <> +rest:
      match hit:
        case True{}:
          c
        case False{}:
          bound.go(rest, k, key.at(rest, k))

def bound(+bs: List<&2, KeyBind>, +k: Nat) -> List<&2, Cmd>:
  bound.go(bs, k, key.at(bs, k))

# a press of key k: its commands, expanded with the alias table
def press(+bs: List<&2, KeyBind>, +k: Nat, +as: List<&2, Alias>) -> Exp:
  expand(bound(bs, k), as)
