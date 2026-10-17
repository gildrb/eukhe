# bridge_sandbox: runs the model of the host and the sandbox
# (bend/sandbox.bend) on an events file and prints what it did, line for
# line as the Rust bridge tests print the Rust code: the frame gate
# (crates/eukhe-core/src/kernel/manager/frames/bridge.rs) and the
# workspace hand-back (crates/eukhe-core/src/child_workspace/bridge.rs).
# Build it with
#
#   bend bend/bridge_sandbox.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   m MAX          the size limit of a frame
#   a K K ...      the frame kinds the host allows
#   f I L K        a frame: id I, length L, kind K
#   k P P ...      the paths of a hand-back, in order
#   p P V          the parent's file P holds V
#   b P V          the base's file P holds V
#   c P V          the child's file P holds V
#   h              print the hand-back (else the protocol)
#
# Then it prints the protocol: `serve` over the frames, in order,
#
#   r ok I         frame I was accepted
#   r err I        frame I was refused
#   x I I ...      the frames that ran, in order
#
# or the hand-back: `back` over the paths,
#
#   w P:V P:V ...  the parent's new workspace, in path order
#   c P P ...      the conflicts, in path order

import Base
import ./sandbox.bend as Sb

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

# every word as a number
def nats(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      tok.nat(w) <> nats(rest)

# the words after the first, as numbers
def args(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      nats(rest)

# What the events set up
# ----------------------

type St is Data:
  St{max: Nat, allowed: List<&2, Nat>, frames: List<&2, Sb.Frame>, ks: List<&2, Nat>, par: List<&2, Sb.Doc>, base: List<&2, Sb.Doc>, child: List<&2, Sb.Doc>, hand: Bool}

def St.max(s: St) -> Nat:
  match s:
    case St{m, a, f, k, p, b, c, h}:
      m

def St.allowed(s: St) -> List<&2, Nat>:
  match s:
    case St{m, a, f, k, p, b, c, h}:
      a

def St.frames(s: St) -> List<&2, Sb.Frame>:
  match s:
    case St{m, a, f, k, p, b, c, h}:
      f

def St.ks(s: St) -> List<&2, Nat>:
  match s:
    case St{m, a, f, k, p, b, c, h}:
      k

def St.par(s: St) -> List<&2, Sb.Doc>:
  match s:
    case St{m, a, f, k, p, b, c, h}:
      p

def St.base(s: St) -> List<&2, Sb.Doc>:
  match s:
    case St{m, a, f, k, p, b, c, h}:
      b

def St.child(s: St) -> List<&2, Sb.Doc>:
  match s:
    case St{m, a, f, k, p, b, c, h}:
      c

def St.hand(s: St) -> Bool:
  match s:
    case St{m, a, f, k, p, b, c, h}:
      h

# one line; h is its first word, ws all its words. Frames and files are
# kept newest first.
def line(h: String, +ws: List<&2, String>, +s: St) -> St:
  match h:
    case SCon{'m', r}:
      match s:
        case St{m, a, f, k, p, b, c, hd}:
          St{arg(ws, 1n), a, f, k, p, b, c, hd}
    case SCon{'a', r}:
      match s:
        case St{m, a, f, k, p, b, c, hd}:
          St{m, args(ws), f, k, p, b, c, hd}
    case SCon{'f', r}:
      match s:
        case St{m, a, f, k, p, b, c, hd}:
          St{m, a, Sb.Frame{arg(ws, 1n), arg(ws, 2n), arg(ws, 3n)} <> f, k, p, b, c, hd}
    case SCon{'k', r}:
      match s:
        case St{m, a, f, k, p, b, c, hd}:
          St{m, a, f, args(ws), p, b, c, hd}
    case SCon{'p', r}:
      match s:
        case St{m, a, f, k, p, b, c, hd}:
          St{m, a, f, k, Sb.Doc{arg(ws, 1n), arg(ws, 2n)} <> p, b, c, hd}
    case SCon{'b', r}:
      match s:
        case St{m, a, f, k, p, b, c, hd}:
          St{m, a, f, k, p, Sb.Doc{arg(ws, 1n), arg(ws, 2n)} <> b, c, hd}
    case SCon{'c', r}:
      match s:
        case St{m, a, f, k, p, b, c, hd}:
          St{m, a, f, k, p, b, Sb.Doc{arg(ws, 1n), arg(ws, 2n)} <> c, hd}
    case SCon{'h', r}:
      match s:
        case St{m, a, f, k, p, b, c, hd}:
          St{m, a, f, k, p, b, c, True{}}
    case r:
      s

def setup(ls: List<&2, String>, +s: St) -> St:
  match ls:
    case Nil{}:
      s
    case l <> rest:
      +ws = String.split(l, ' ')
      setup(rest, line(tok.at(ws, 0n), ws, s))

# Writing
# -------

def show.reply(r: Sb.Reply) -> String:
  match r:
    case Sb.Ok{i}:
      String.concat(["r ok ", Nat.show(i), "\n"])
    case Sb.Err{i}:
      String.concat(["r err ", Nat.show(i), "\n"])

def show.replies(rs: List<&2, Sb.Reply>) -> String:
  match rs:
    case Nil{}:
      ""
    case r <> rest:
      String.append(show.reply(r), show.replies(rest))

def show.ids(ns: List<&2, Nat>) -> String:
  match ns:
    case Nil{}:
      ""
    case n <> rest:
      String.concat([" ", Nat.show(n), show.ids(rest)])

def show.docs(ws: List<&2, Sb.Doc>) -> String:
  match ws:
    case Nil{}:
      ""
    case +d <> rest:
      String.concat([" ", Nat.show(Sb.Doc.path(d)), ":", Nat.show(Sb.Doc.body(d)), show.docs(rest)])

def show.host(+h: Sb.Host) -> String:
  String.concat([show.replies(Sb.Host.replies(h)), "x", show.ids(Sb.frame.ids(Sb.Host.ran(h))), "\n"])

def show.back(+x: Sb.Back) -> String:
  String.concat(["w", show.docs(Sb.Back.ws(x)), "\nc", show.ids(Sb.Back.clashes(x)), "\n"])

def run(+s: St, hand: Bool) -> String:
  match hand:
    case True{}:
      show.back(Sb.back(St.ks(s), St.par(s), St.base(s), St.child(s)))
    case False{}:
      show.host(Sb.serve(List.reverse(&2, Sb.Frame, St.frames(s)), St.max(s), St.allowed(s)))

def go(text: String) -> String:
  +s = setup(String.lines(text), St{0n, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, False{}})
  run(s, St.hand(s))

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
      IO.die(String, 2, "usage: bridge_sandbox <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_sandbox <events>")
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
