# bridge_director: runs the Director stack model (bend/director.bend) on
# an events file and prints what it did, line for line as the Rust bridge
# test prints the Rust stack (crates/eukhe-core/src/durable/directors/
# bridge.rs). Build it with
#
#   bend bend/bridge_director.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   c N            the stack cap is N
#   l N K:B ...    a new loop: global budget N, no end, and the stack, top
#                  first (each layer its kind K and its budget B)
#   t V ...        one tick of the loop on the verdicts, top first: d
#                  Defer, a Again, y Yield, p:K:B Stack{Layer{K, B}}, v
#                  Leave, x Abort
#   d V ...        one decision of the loop's stack on the verdicts (the
#                  loop does not change)
#   r              run the loop from its start on every tick since its l
#   e              encode the loop's stack into the tree, and decode it
#
# After each event it prints:
#
#   t END N | K:B ...   after t: how the loop ended (run while it runs,
#                       hand, fail), its global budget left, and its
#                       stack, top first
#   r END N | K:B ...   after r: the same of the loop run gives
#   d OUT | K:B ...     after d: the decision (cont, hand, fail) and its
#                       stack
#   e K:P:V ...         after e: the nodes encode gives, then
#   b K:B ...           the stack decode reads back from them
#
# c and l print nothing.

import Base
import ./director.bend as D
import ./tree.bend as T

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

# a `K:B` word
def layer.of(w: String) -> D.Layer:
  +ps = String.split(w, ':')
  D.Layer{arg(ps, 0n), arg(ps, 1n)}

def layers.of(ws: List<&2, String>) -> List<&2, D.Layer>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      layer.of(w) <> layers.of(rest)

# one verdict word (`p:K:B`: the rest of the word after `p` is `:K:B`)
def verdict.of(w: String) -> D.Verdict:
  match w:
    case SCon{'a', t}:
      D.Again{}
    case SCon{'y', t}:
      D.Yield{}
    case SCon{'p', t}:
      +ps = String.split(t, ':')
      D.Stack{D.Layer{arg(ps, 1n), arg(ps, 2n)}}
    case SCon{'v', t}:
      D.Leave{}
    case SCon{'x', t}:
      D.Abort{}
    case t:
      D.Defer{}

def verdicts.of(ws: List<&2, String>) -> List<&2, D.Verdict>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      verdict.of(w) <> verdicts.of(rest)

# Writing
# -------

def show.layers(s: List<&2, D.Layer>) -> String:
  match s:
    case Nil{}:
      ""
    case l <> rest:
      match l:
        case D.Layer{k, b}:
          String.concat([" ", Nat.show(k), ":", Nat.show(b), show.layers(rest)])

def show.out(o: D.Out) -> String:
  match o:
    case D.Cont{}:
      "cont"
    case D.Hand{}:
      "hand"
    case D.Failed{}:
      "fail"

def show.end(e: Maybe<&2, D.Out>) -> String:
  match e:
    case None{}:
      "run"
    case Some{o}:
      show.out(o)

def show.loop(head: String, l: D.Loop) -> String:
  match l:
    case D.Loop{n, s, e}:
      String.concat([head, " ", show.end(e), " ", Nat.show(n), " |", show.layers(s), "\n"])

def show.dec(d: D.Dec) -> String:
  match d:
    case D.Dec{o, s}:
      String.concat(["d ", show.out(o), " |", show.layers(s), "\n"])

def show.ents(t: List<&2, T.Ent>) -> String:
  match t:
    case Nil{}:
      ""
    case +e <> rest:
      String.concat([" ", Nat.show(T.Ent.k(e)), ":", Nat.show(T.Ent.p(e)), ":", Nat.show(T.Ent.v(e)), show.ents(rest)])

def show.tree(+s: List<&2, D.Layer>) -> String:
  +t = D.encode(s)
  String.concat(["e", show.ents(t), "\n", "b", show.layers(D.decode(t)), "\n"])

# Running
# -------

# the run so far: the cap, the loop at its l, the loop now, the ticks since
# the l (in order), and the output of the last line
type St is Data:
  St{cap: Nat, start: D.Loop, now: D.Loop, ticks: List<&2, List<&2, D.Verdict>>, text: String}

def St.cap(s: St) -> Nat:
  match s:
    case St{c, a, n, ts, x}:
      c

def St.start(s: St) -> D.Loop:
  match s:
    case St{c, a, n, ts, x}:
      a

def St.now(s: St) -> D.Loop:
  match s:
    case St{c, a, n, ts, x}:
      n

def St.ticks(s: St) -> List<&2, List<&2, D.Verdict>>:
  match s:
    case St{c, a, n, ts, x}:
      ts

def St.text(s: St) -> String:
  match s:
    case St{c, a, n, ts, x}:
      x

# one tick on the verdicts vs
def tick(+vs: List<&2, D.Verdict>, +s: St) -> St:
  +n = D.tick(St.cap(s), St.now(s), vs)
  St{St.cap(s), St.start(s), n, List.append(&2, List<&2, D.Verdict>, St.ticks(s), [vs]), show.loop("t", n)}

# a new loop with n steps and the stack ls
def start(+n: Nat, +ls: List<&2, D.Layer>, +s: St) -> St:
  +l = {D.Loop{n, ls, None{}} : D.Loop}
  St{St.cap(s), l, l, Nil{}, ""}

# one line; h is its first word, ws all its words
def line(h: String, +ws: List<&2, String>, +s: St) -> St:
  match h:
    case SCon{'c', r}:
      St{arg(ws, 1n), St.start(s), St.now(s), St.ticks(s), ""}
    case SCon{'l', r}:
      start(arg(ws, 1n), layers.of(skip(skip(ws))), s)
    case SCon{'t', r}:
      tick(verdicts.of(skip(ws)), s)
    case SCon{'d', r}:
      St{St.cap(s), St.start(s), St.now(s), St.ticks(s), show.dec(D.decide(D.Loop.stack(St.now(s)), verdicts.of(skip(ws)), St.cap(s)))}
    case SCon{'r', r}:
      St{St.cap(s), St.start(s), St.now(s), St.ticks(s), show.loop("r", D.run(St.ticks(s), St.cap(s), St.start(s)))}
    case SCon{'e', r}:
      St{St.cap(s), St.start(s), St.now(s), St.ticks(s), show.tree(D.Loop.stack(St.now(s)))}
    case r:
      St{St.cap(s), St.start(s), St.now(s), St.ticks(s), ""}

def go(ls: List<&2, String>, +s: St) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +o = line(tok.at(ws, 0n), ws, s)
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
      IO.die(String, 2, "usage: bridge_director <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_director <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  +l = {D.Loop{0n, Nil{}, None{}} : D.Loop}
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), St{0n, l, l, Nil{}, ""}))
