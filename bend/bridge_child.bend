# bridge_child: runs the child watch's verdict (`look` in child.bend) on
# a scenario file and prints what it decided, line for line as the Rust
# bridge test prints `Vigil::judge`
# (crates/eukhe-core/src/durable/children/watch/bridge.rs). Build it with
#
#   bend bend/bridge_child.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one event per line:
#
#   9 stall fails     the settings (first line); a fresh clock
#   0 dt tok          a poll that read the child unsettled with token tok
#                     (`-` for none), 1 + dt ms after the last
#   1 dt              a failed poll, 1 + dt ms after the last
#
# After each poll it prints `W q=<quiet ms> f=<failed polls> t=<token>`,
# or `S` (stalled) or `U` (unreachable); after S or U the next poll
# watches a fresh child.

import Base
import ./child.bend as C

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

# Writing
# -------

def show.tok(t: Maybe<&2, Nat>) -> String:
  match t:
    case None{}:
      "-"
    case Some{x}:
      Nat.show(x)

def show.owed(k: C.Report) -> String:
  match k:
    case C.Completed{}:
      "C\n"
    case C.Failed{}:
      "F\n"
    case C.Cancelled{}:
      "X\n"
    case C.Stalled{}:
      "S\n"
    case C.Unreachable{}:
      "U\n"

def show.next(+cfg: C.Cfg, x: C.Next) -> String:
  match x:
    case C.Watch{w}:
      match w:
        case C.W{t, l, n}:
          String.concat(["W q=", Nat.show(Nat.sub(C.Cfg.stall(cfg), l)), " f=", Nat.show(Nat.sub(C.Cfg.fails(cfg), n)), " t=", show.tok(t), "\n"])
    case C.Owe{k}:
      show.owed(k)
    case C.Quiet{}:
      "Q\n"

# the clock of the next poll: a report starts a fresh child
def next.clock(+cfg: C.Cfg, x: C.Next) -> C.W:
  match x:
    case C.Watch{w}:
      w
    case C.Owe{k}:
      C.W.fresh(cfg, None{})
    case C.Quiet{}:
      C.W.fresh(cfg, None{})

# Running
# -------

# what one line did: the settings and the clock after it, and its output
type Out is Data:
  Out{cfg: C.Cfg, w: C.W, text: String}

def Out.cfg(o: Out) -> C.Cfg:
  match o:
    case Out{c, w, t}:
      c

def Out.w(o: Out) -> C.W:
  match o:
    case Out{c, w, t}:
      w

def Out.text(o: Out) -> String:
  match o:
    case Out{c, w, t}:
      t

def out.poll(+cfg: C.Cfg, +x: C.Next) -> Out:
  Out{cfg, next.clock(cfg, x), show.next(cfg, x)}

def apply(k: Nat, +ws: List<&2, String>, +cfg: C.Cfg, +w: C.W) -> Out:
  match k:
    case 0n:
      out.poll(cfg, C.look(cfg, w, 1n+tok.nat(tok.at(ws, 1n)), C.Busy{Nat.read(tok.at(ws, 2n))}))
    case 1n:
      out.poll(cfg, C.look(cfg, w, 1n+tok.nat(tok.at(ws, 1n)), C.Lost{}))
    case 9n:
      Out{C.Cfg{tok.nat(tok.at(ws, 1n)), tok.nat(tok.at(ws, 2n))}, C.W.fresh(C.Cfg{tok.nat(tok.at(ws, 1n)), tok.nat(tok.at(ws, 2n))}, None{}), ""}
    case _:
      Out{cfg, w, ""}

# the output of each line of the scenario
def go(ls: List<&2, String>, +cfg: C.Cfg, +w: C.W) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +o = apply(Maybe.default(&2, Nat, Nat.read(tok.at(ws, 0n)), 8n), ws, cfg, w)
      String.append(Out.text(o), go(rest, Out.cfg(o), Out.w(o)))

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
      IO.die(String, 2, "usage: bridge_child <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_child <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), C.Cfg{1n, 1n}, C.W.fresh(C.Cfg{1n, 1n}, None{})))
