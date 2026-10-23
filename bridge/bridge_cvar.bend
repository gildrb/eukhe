# bridge_cvar: runs the cvar model (bend/cvar.bend) on an events file and
# prints what it did, line for line as the Rust bridge test
# (crates/eukhe-core/src/settings/cvar/bridge.rs) prints the Rust cvars.
# Build it with
#
#   bend bridge/bridge_cvar.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line; an id
# I is cvar `c<I>` and a value V is `t`, `f` or `n<N>` (the expansion of
# aliases and key binds runs as the compiled core, bend/ffi_cvar.bend):
#
#   d I T S P R V   declare cvar I: type T (n Nat, b Bool), scope S (g
#                   Global, l Local), persist P and replicate R (0 or 1),
#                   default V
#   g               the registry of the declarations so far
#   c I V           a set of I in config.cfg
#   p I V           a set of I in the current agent's profile
#   s I V           a set of I in the current agent's own sets
#   a               the current agent joins the family; a new agent (its
#                   subagent) is current
#   v I             the value of I for the current agent
#   t I             toggle I in the current agent, over its family
#   w F             the current agent's own sets it writes (F p, persist)
#                   or replicates (F r)
#
# It prints, after g, v, t and w:
#
#   registry accept | registry reject dup|bad c<I>
#   value c<I> <value|none>
#   toggle c<I> <value|none>          (the value after the toggle)
#   written persist|replicate c<I>=<value> ...
#
# Every value of v, t and w is computed on the registry of the
# declarations (the model's `registry`).

import Base
import ../bend/cvar.bend as C

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

# the words after the first
def skip(ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      rest

# a value word: t, f or n<N>
def val.of(w: String) -> C.Val:
  match w:
    case SCon{'t', r}:
      C.VBool{True{}}
    case SCon{'n', r}:
      C.VNat{tok.nat(r)}
    case r:
      C.VBool{False{}}

def ty.of(w: String) -> C.Ty:
  match w:
    case SCon{'n', r}:
      C.TNat{}
    case r:
      C.TBool{}

def scope.of(w: String) -> C.Scope:
  match w:
    case SCon{'g', r}:
      C.Global{}
    case r:
      C.Local{}

def bool.of(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      True{}

def flag.of(w: String) -> C.Flag:
  match w:
    case SCon{'p', r}:
      C.Persist{}
    case r:
      C.Replicate{}

def decl.of(+ws: List<&2, String>) -> C.Decl:
  C.Decl{arg(ws, 1n), ty.of(tok.at(ws, 2n)), scope.of(tok.at(ws, 3n)), bool.of(arg(ws, 4n)), bool.of(arg(ws, 5n)), val.of(tok.at(ws, 6n))}

def bind.of(+ws: List<&2, String>) -> C.Bind:
  C.Bind{arg(ws, 1n), val.of(tok.at(ws, 2n))}

# Writing
# -------

def show.id(n: Nat) -> String:
  String.append("c", Nat.show(n))

def show.val(v: C.Val) -> String:
  match v:
    case C.VNat{n}:
      Nat.show(n)
    case C.VBool{b}:
      match b:
        case True{}:
          "true"
        case False{}:
          "false"

def show.maybe(m: Maybe<&2, C.Val>) -> String:
  match m:
    case None{}:
      "none"
    case Some{v}:
      show.val(v)

def show.binds(ss: List<&2, C.Bind>) -> String:
  match ss:
    case Nil{}:
      ""
    case s <> rest:
      match s:
        case C.Bind{i, v}:
          String.concat([" ", show.id(i), "=", show.val(v), show.binds(rest)])

def show.flag(f: C.Flag) -> String:
  match f:
    case C.Persist{}:
      "persist"
    case C.Replicate{}:
      "replicate"

# the first declaration of xs is taken in ds
def taken.at(+xs: List<&2, C.Decl>, +ds: List<&2, C.Decl>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case d <> rest:
      Maybe.is_some(&2, C.Decl, C.find(ds, C.Decl.id(d)))

# the default of the first declaration of xs has its type
def typed.at(+xs: List<&2, C.Decl>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case d <> rest:
      C.Decl.typed(d)

# the first declaration of xs the registry drops on ds, and why; taken is
# taken.at(xs, ds) and good typed.at(xs)
def dropped.go(xs: List<&2, C.Decl>, +ds: List<&2, C.Decl>, taken: Bool, good: Bool) -> String:
  match xs:
    case Nil{}:
      "none"
    case +d <> +rest:
      match taken:
        case True{}:
          String.append("dup ", show.id(C.Decl.id(d)))
        case False{}:
          match good:
            case True{}:
              +kept = List.append(&2, C.Decl, ds, [d])
              dropped.go(rest, kept, taken.at(rest, kept), typed.at(rest))
            case False{}:
              String.append("bad ", show.id(C.Decl.id(d)))

def show.kept(all: Bool, +xs: List<&2, C.Decl>) -> String:
  match all:
    case True{}:
      "registry accept\n"
    case False{}:
      String.concat(["registry reject ", dropped.go(xs, Nil{}, taken.at(xs, Nil{}), typed.at(xs)), "\n"])

# accept when the model's registry keeps every declaration
def show.registry(+xs: List<&2, C.Decl>) -> String:
  show.kept(Nat.is_eq(List.length(&2, C.Decl, C.registry(xs)), List.length(&2, C.Decl, xs)), xs)

# Running
# -------

# the declarations, config.cfg, the family above the current agent (root
# first), the current agent, and the output of the last line
type St is Data:
  St{ds: List<&2, C.Decl>, cfg: List<&2, C.Bind>, fam: List<&2, C.Ag>, cur: C.Ag, text: String}

def St.text(s: St) -> String:
  match s:
    case St{ds, cfg, fam, cur, x}:
      x

def ag.profile(a: C.Ag, +b: C.Bind) -> C.Ag:
  match a:
    case C.Ag{p, ss}:
      C.Ag{List.append(&2, C.Bind, p, [b]), ss}

def ag.set(a: C.Ag, +b: C.Bind) -> C.Ag:
  match a:
    case C.Ag{p, ss}:
      C.Ag{p, List.append(&2, C.Bind, ss, [b])}

# the toggled agent and the value of x after the toggle, over the family
def toggled(+ds: List<&2, C.Decl>, +cfg: List<&2, C.Bind>, +a: C.Ag, +x: Nat, +fam: List<&2, C.Ag>) -> St:
  +t = C.toggle(C.registry(ds), cfg, fam, a, x)
  St{ds, cfg, fam, t, String.concat(["toggle ", show.id(x), " ", show.maybe(C.value(C.registry(ds), cfg, List.append(&2, C.Ag, fam, [t]), x)), "\n"])}

# one line; h is its first word, ws all its words
def line(s: St, h: String, +ws: List<&2, String>) -> St:
  match s:
    case St{+ds, +cfg, +fam, +cur, x}:
      match h:
        case SCon{'d', r}:
          St{List.append(&2, C.Decl, ds, [decl.of(ws)]), cfg, fam, cur, ""}
        case SCon{'g', r}:
          St{ds, cfg, fam, cur, show.registry(ds)}
        case SCon{'c', r}:
          St{ds, List.append(&2, C.Bind, cfg, [bind.of(ws)]), fam, cur, ""}
        case SCon{'p', r}:
          St{ds, cfg, fam, ag.profile(cur, bind.of(ws)), ""}
        case SCon{'s', r}:
          St{ds, cfg, fam, ag.set(cur, bind.of(ws)), ""}
        case SCon{'a', r}:
          St{ds, cfg, List.append(&2, C.Ag, fam, [cur]), C.Ag{Nil{}, Nil{}}, ""}
        case SCon{'v', r}:
          +i = arg(ws, 1n)
          St{ds, cfg, fam, cur, String.concat(["value ", show.id(i), " ", show.maybe(C.value(C.registry(ds), cfg, List.append(&2, C.Ag, fam, [cur]), i)), "\n"])}
        case SCon{'t', r}:
          toggled(ds, cfg, cur, arg(ws, 1n), fam)
        case SCon{'w', r}:
          +f = flag.of(tok.at(ws, 1n))
          St{ds, cfg, fam, cur, String.concat(["written ", show.flag(f), show.binds(C.written(C.Ag.sets(cur), C.registry(ds), f)), "\n"])}
        case r:
          St{ds, cfg, fam, cur, ""}

def go(ls: List<&2, String>, +s: St) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +o = line(s, tok.at(ws, 0n), ws)
      String.append(St.text(o), go(rest, o))

def read.done(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{text}:
      text
    case Fail{e}:
      ""

def read.file(m: File & Result<&1, &1, U32 & String, String>) -> IO(String):
  (f, r) = m
  do IO<String>:
    Unit <- File.close(f)
    IO.pure(String, read.done(r))

def scenario(args: List<String>) -> IO(String):
  match args:
    case Nil{}:
      IO.die(String, 2, "usage: bridge_cvar <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_cvar <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), St{Nil{}, Nil{}, Nil{}, C.Ag{Nil{}, Nil{}}, ""}))
