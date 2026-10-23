# bridge_kernel_local: runs the model of the kernel setup, the session's
# tools and the bootstrap lock (bend/kernel_local.bend) on an events file
# and prints what it did, line for line as the Rust bridge tests print
# the Rust code (crates/eukhe-core/src/kernel/bootstrap/bridge.rs: the
# setup, the session's tools, the lock). Build it with
#
#   bend bridge/bridge_kernel_local.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   p F S      a setup that finds F (0 current, 1 skills stale, 2 stale)
#              under S (0 a session, 1 `eukhe kernel install`)
#   o B        its sync or build worked (1) or failed (0)
#   k B        the kernel is up (1) or missing (0), with no setup line
#   t T        a tool call: 0 the ipython tool, N > 0 another tool
#   l L        the lock an attempt finds: 0 none, 1 a live owner, 2 a
#              dead owner
#   f K O      a file beside the lock: K 0 a candidate, 1 a stale lock
#              renamed aside, 2 another file; O 1 a live owner, 0 a dead
#              one
#
# Then it prints, for a setup line,
#
#   a A A ...  the setup's actions: f1 a hashed fetch, f0 a fetch that is
#              not hashed, o a local command, c the check, r the start
#   k up|missing
#
# for each tool call, in order,
#
#   t ran|install
#
# and for a lock line
#
#   e got|busy|freed   how the attempt ended
#   w N                the attempt's own candidates left after it
#   s K O              each file the sweep kept, in the events' order

import Base
import ../bend/kernel_local.bend as KL

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

def nth(xs: List<&2, Nat>, k: Nat) -> Nat:
  Maybe.default(&2, Nat, List.get(&2, Nat, xs, k), 0n)

def yes(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+m:
      True{}

def found(n: Nat) -> KL.Found:
  match n:
    case 0n:
      KL.Current{}
    case 1n+a:
      match a:
        case 0n:
          KL.Skills{}
        case 1n+b:
          KL.Stale{}

def setup(n: Nat) -> KL.Setup:
  match n:
    case 0n:
      KL.Local{}
    case 1n+a:
      KL.Install{}

def tool(n: Nat) -> KL.Tool:
  match n:
    case 0n:
      KL.Python{}
    case 1n+a:
      KL.Other{1n+a}

def kernel(b: Bool) -> KL.Kernel:
  match b:
    case True{}:
      KL.Up{}
    case False{}:
      KL.Missing{}

def lock(n: Nat) -> KL.Lock:
  match n:
    case 0n:
      KL.Free{}
    case 1n+a:
      match a:
        case 0n:
          KL.Live{}
        case 1n+b:
          KL.Gone{}

def kind(n: Nat) -> KL.FileKind:
  match n:
    case 0n:
      KL.Cand{}
    case 1n+a:
      match a:
        case 0n:
          KL.Aside{}
        case 1n+b:
          KL.Foreign{}

def owner(b: Bool) -> KL.Owner:
  match b:
    case True{}:
      KL.Alive{}
    case False{}:
      KL.Dead{}

# What the events set up
# ----------------------

# p: [F, S]; o: [B]; k: [B]; tools and files newest first; l: [L]
type St is Data:
  St{p: List<&2, Nat>, o: List<&2, Nat>, k: List<&2, Nat>, tools: List<&2, Nat>, l: List<&2, Nat>, files: List<&2, KL.Left>}

def line(h: String, +ws: List<&2, String>, +s: St) -> St:
  match h:
    case SCon{'p', r}:
      match s:
        case St{p, o, k, ts, l, fs}:
          St{[arg(ws, 1n), arg(ws, 2n)], o, k, ts, l, fs}
    case SCon{'o', r}:
      match s:
        case St{p, o, k, ts, l, fs}:
          St{p, [arg(ws, 1n)], k, ts, l, fs}
    case SCon{'k', r}:
      match s:
        case St{p, o, k, ts, l, fs}:
          St{p, o, [arg(ws, 1n)], ts, l, fs}
    case SCon{'t', r}:
      match s:
        case St{p, o, k, ts, l, fs}:
          St{p, o, k, arg(ws, 1n) <> ts, l, fs}
    case SCon{'l', r}:
      match s:
        case St{p, o, k, ts, l, fs}:
          St{p, o, k, ts, [arg(ws, 1n)], fs}
    case SCon{'f', r}:
      match s:
        case St{p, o, k, ts, l, fs}:
          St{p, o, k, ts, l, KL.Left{kind(arg(ws, 1n)), owner(yes(arg(ws, 2n)))} <> fs}
    case r:
      s

def setup.all(ls: List<&2, String>, +s: St) -> St:
  match ls:
    case Nil{}:
      s
    case l <> rest:
      +ws = String.split(l, ' ')
      setup.all(rest, line(tok.at(ws, 0n), ws, s))

# Writing
# -------

def show.act(a: KL.Act) -> String:
  match a:
    case KL.Fetch{h}:
      match h:
        case True{}:
          " f1"
        case False{}:
          " f0"
    case KL.Offline{}:
      " o"
    case KL.Check{}:
      " c"
    case KL.Run{}:
      " r"

def show.acts(xs: List<&2, KL.Act>) -> String:
  match xs:
    case Nil{}:
      ""
    case a <> rest:
      String.concat([show.act(a), show.acts(rest)])

def show.kernel(k: KL.Kernel) -> String:
  match k:
    case KL.Up{}:
      "up"
    case KL.Missing{}:
      "missing"

def show.answer(a: KL.Answer) -> String:
  match a:
    case KL.Ran{}:
      "ran"
    case KL.NamesInstall{}:
      "install"

# the setup section: none without a setup line
def show.setup(+p: List<&2, Nat>, +o: List<&2, Nat>) -> String:
  match p:
    case Nil{}:
      ""
    case f <> rest:
      String.concat(["a", show.acts(KL.plan(found(nth(p, 0n)), setup(nth(p, 1n)))), "\nk ", show.kernel(KL.start(found(nth(p, 0n)), yes(nth(o, 0n)))), "\n"])

# the kernel the tools see: the k line, else the setup's, else up
def kernel.of(k: List<&2, Nat>, +p: List<&2, Nat>, +o: List<&2, Nat>) -> KL.Kernel:
  match k:
    case b <> rest:
      kernel(yes(b))
    case Nil{}:
      match p:
        case Nil{}:
          KL.Up{}
        case f <> rest:
          KL.start(found(nth(p, 0n)), yes(nth(o, 0n)))

def show.tools(ts: List<&2, Nat>, +k: KL.Kernel) -> String:
  match ts:
    case Nil{}:
      ""
    case t <> rest:
      String.concat(["t ", show.answer(KL.answer(tool(t), k)), "\n", show.tools(rest, k)])

def show.end(e: KL.End) -> String:
  match e:
    case KL.Got{}:
      "got"
    case KL.Busy{}:
      "busy"
    case KL.Freed{}:
      "freed"
    case KL.Crash{}:
      "crash"

def show.kind(k: KL.FileKind) -> String:
  match k:
    case KL.Cand{}:
      "0"
    case KL.Aside{}:
      "1"
    case KL.Foreign{}:
      "2"

def show.owner(o: KL.Owner) -> String:
  match o:
    case KL.Alive{}:
      "1"
    case KL.Dead{}:
      "0"

def show.files(fs: List<&2, KL.Left>) -> String:
  match fs:
    case Nil{}:
      ""
    case KL.Left{k, o} <> rest:
      String.concat(["s ", show.kind(k), " ", show.owner(o), "\n", show.files(rest)])

# the lock section: none without a lock line
def show.lock(l: List<&2, Nat>, fs: List<&2, KL.Left>) -> String:
  match l:
    case Nil{}:
      ""
    case n <> rest:
      +e = KL.attempt(lock(n))
      String.concat(["e ", show.end(e), "\nw ", Nat.show(KL.own_left(e)), "\n", show.files(KL.sweep(fs))])

def run(s: St) -> String:
  match s:
    case St{+p, +o, k, ts, l, fs}:
      String.concat([show.setup(p, o), show.tools(List.reverse(&2, Nat, ts), kernel.of(k, p, o)), show.lock(l, List.reverse(&2, KL.Left, fs))])

def go(text: String) -> String:
  run(setup.all(String.lines(text), St{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}))

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
      IO.die(String, 2, "usage: bridge_kernel_local <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_kernel_local <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(text))
