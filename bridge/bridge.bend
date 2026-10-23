# bridge: runs the optchat model on a scenario file and prints what it
# did, line for line as the Rust bridge test prints the Rust planner
# (crates/eukhe-core/tests/memory_bridge.rs). Build it with
#
#   bend bridge/bridge.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one event per line; a node is
# `l bits`, its index in binary, lowest bit first, `-` for 0:
#
#   9 ph ceil floor cceil cfloor jobs   the sizes (first line)
#   0                                   a message
#   1 l bits size                       node built, size bytes
#   2 l bits                            node's call starts
#   3 l bits                            node's call fails
#   4 l bits                            print the compaction's view of node
#   5                                   print the view
#   6                                   a turn starts to wait
#
# After each event 0-3 and 6 it prints `v=<view> c=<compaction view> s=<0|1>
# b=<batch> q=<queue> n=<queue while a turn waits>`, parts as `l.bits`
# joined by commas. A node's text is a newline then size-1 `x`s.

import Base
import ../bend/optchat.bend as O

# Reading
# -------

def tok.bit(dash: Bool, one: Bool, rest: List<&2, Bool>) -> List<&2, Bool>:
  match dash:
    case True{}:
      Nil{}
    case False{}:
      one <> rest

def tok.bits(s: String) -> List<&2, Bool>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{+c, t}:
      tok.bit(Char.is_eq(c, '-'), Char.is_eq(c, '1'), tok.bits(t))

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.node(+ws: List<&2, String>) -> O.Node:
  O.Node{tok.nat(tok.at(ws, 1n)), tok.bits(tok.at(ws, 2n))}

# Writing
# -------

def dec.cons(over: Bool, +x: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match over:
    case True{}:
      Nat.sub(x, 10n) <> rest
    case False{}:
      x <> rest

# ds·2 + c, ds the decimal digits lowest first, c 0 or 1
def dec.step(ds: List<&2, Nat>, +c: Nat) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      match c:
        case 0n:
          Nil{}
        case 1n+p:
          [1n]
    case d <> t:
      +x = Nat.add(Nat.double(d), c)
      dec.cons(Nat.is_ge(x, 10n), x, dec.step(t, O.bit(Nat.is_ge(x, 10n), 0n)))

def dec.go(hi: List<&2, Bool>, ds: List<&2, Nat>) -> List<&2, Nat>:
  match hi:
    case Nil{}:
      ds
    case b <> t:
      dec.go(t, dec.step(ds, O.bit(b, 0n)))

def dec.chars(ds: List<&2, Nat>, acc: String) -> String:
  match ds:
    case Nil{}:
      acc
    case d <> t:
      dec.chars(t, SCon{Chr{U32.from_nat(Nat.add(48n, d))}, acc})

def dec.show(ds: List<&2, Nat>) -> String:
  match ds:
    case Nil{}:
      "0"
    case d <> t:
      dec.chars(d <> t, "")

# a number in binary, in decimal
def dec(bs: List<&2, Bool>) -> String:
  dec.show(dec.go(List.reverse(&2, Bool, bs), Nil{}))

# a node as id+n
def show.node(+n: O.Node) -> String:
  String.concat([dec(O.pair_start(n)), "+", dec(O.Bits.shl(O.Node.lvl(n), [True{}]))])

def show.nodes(ns: List<&2, O.Node>) -> String:
  match ns:
    case Nil{}:
      ""
    case n <> t:
      match t:
        case Nil{}:
          show.node(n)
        case h <> r:
          String.append(show.node(n), String.append(",", show.nodes(h <> r)))

def show.bool(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

# a node's text: a newline, then size-1 x's
def text.of(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "(not summarized yet: zoom it)"
    case Some{s}:
      match s:
        case 0n:
          ""
        case 1n+p:
          SCon{'\n', String.repeat("x", p)}

def flat.char(nl: Bool, c: Char) -> Char:
  match nl:
    case True{}:
      ' '
    case False{}:
      c

# newlines as spaces
def flat(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      SCon{flat.char(Char.is_eq(c, '\n'), c), flat(t)}

# one line: id+n|text
def line(+info: O.Info, +n: O.Node) -> String:
  String.concat([dec(O.pair_start(n)), "+", dec(O.Bits.shl(O.Node.lvl(n), [True{}])), "|", flat(text.of(O.Info.get(info, n))), "\n"])

def lines(+info: O.Info, ns: List<&2, O.Node>) -> String:
  match ns:
    case Nil{}:
      ""
    case n <> t:
      String.append(line(info, n), lines(info, t))

# <chat>, a line per node, </chat>
def render(+info: O.Info, ns: List<&2, O.Node>) -> String:
  String.concat(["<chat>\n", lines(info, ns), "</chat>"])

def show.state(+cfg: O.Cfg, +s: O.St, batch: List<&2, O.Node>) -> String:
  String.concat(["v=", show.nodes(O.St.view(s)), " c=", show.nodes(O.St.cview(s)), " s=", show.bool(O.St.shrink(s)), " b=", show.nodes(batch), " q=", show.nodes(O.cands(cfg, s)), " n=", show.nodes(O.cands.need(cfg, s)), "\n"])

# Running
# -------

def cfg.of(+ws: List<&2, String>) -> O.Cfg:
  O.Cfg{tok.nat(tok.at(ws, 1n)), tok.nat(tok.at(ws, 2n)), tok.nat(tok.at(ws, 3n)), tok.nat(tok.at(ws, 4n)), tok.nat(tok.at(ws, 5n)), tok.nat(tok.at(ws, 6n))}

# what one line did: the sizes and the chat after it, and its output
type Out is Data:
  Out{cfg: O.Cfg, s: O.St, text: String}

def Out.cfg(o: Out) -> O.Cfg:
  match o:
    case Out{c, s, t}:
      c

def Out.s(o: Out) -> O.St:
  match o:
    case Out{c, s, t}:
      s

def Out.text(o: Out) -> String:
  match o:
    case Out{c, s, t}:
      t

def out.event(+cfg: O.Cfg, r: O.St & List<&2, O.Node>) -> Out:
  (s, batch) = r
  +s2 = s
  Out{cfg, s2, show.state(cfg, s2, batch)}

def apply(k: Nat, +ws: List<&2, String>, +cfg: O.Cfg, +s: O.St) -> Out:
  match k:
    case 0n:
      out.event(cfg, O.step(cfg, s, O.Msg{}))
    case 1n:
      out.event(cfg, O.step(cfg, s, O.Build{tok.node(ws), tok.nat(tok.at(ws, 3n))}))
    case 2n:
      out.event(cfg, O.step(cfg, s, O.Start{tok.node(ws)}))
    case 3n:
      out.event(cfg, O.step(cfg, s, O.Free{tok.node(ws)}))
    case 4n:
      Out{cfg, s, String.concat(["x=", render(O.St.info(s), O.ctx(s, tok.node(ws))), "\n"])}
    case 5n:
      Out{cfg, s, String.concat(["r=", render(O.St.info(s), O.St.view(s)), "\n"])}
    case 6n:
      out.event(cfg, (O.St.wait(s), Nil{}))
    case 9n:
      Out{cfg.of(ws), s, ""}
    case _:
      Out{cfg, s, ""}

# the output of each line of the scenario
def go(ls: List<&2, String>, +cfg: O.Cfg, +s: O.St) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +o = apply(Maybe.default(&2, Nat, Nat.read(tok.at(ws, 0n)), 8n), ws, cfg, s)
      String.append(Out.text(o), go(rest, Out.cfg(o), Out.s(o)))

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
      IO.die(String, 2, "usage: bridge <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), O.Cfg.gist(), O.St.empty()))
