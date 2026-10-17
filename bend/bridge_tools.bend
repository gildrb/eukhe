# bridge_tools: runs the tool surface model (bend/tools.bend, sections 1
# and 2) on a scenario file and prints what it did, line for line as the
# Rust bridge test (crates/eukhe-core/src/durable/tool_surface/bridge.rs)
# prints the Rust registry, tool surface and schema build. Build it with
#
#   bend bend/bridge_tools.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one op per line; tool k is
# `t<k>`, parameter 0 is the intent `i` and parameter k is `p<k>`:
#
#   0 R...        a new session whose roster is the tools R, in order
#   1 t           tool t joins (an MCP server, a skill, an extension)
#   2 t           tool t quits
#   3             a request is sent
#   4 V P...      a tool declares the parameters P, in order, at version V
#                 (0: no version)
#
# After ops 0 to 3 it prints `r=<roster> d=<reach> n=<requests> eq=<same>`:
# the roster, whether `dyn` reaches each of the tools 0 to 5 (1/0), the
# requests sent so far, and whether every one sent the roster (1/0). After
# op 4 it prints `b=<params> v=<version> idem=<same>`: the schema the
# harness sends, and whether building it again changes nothing (1/0).

import Base
import ./tools.bend as Tl

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def nats(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      tok.nat(w) <> nats(rest)

def rest(+ws: List<&2, String>, k: Nat) -> List<&2, String>:
  List.drop(&2, String, ws, k)

# Writing
# -------

def show.bool(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def show.ids.go(xs: List<&2, Nat>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> more:
      Nat.show(x) <> show.ids.go(more)

def show.ids(xs: List<&2, Nat>) -> String:
  String.join(show.ids.go(xs), ",")

# for the tools i .. i+k-1: 1 when `dyn` reaches it
def reach(+s: Tl.Sess, k: Nat, +i: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      String.append(show.bool(Tl.dyn_call(s, i)), reach(s, m, 1n+i))

def show.sess(+s: Tl.Sess) -> String:
  String.concat(["r=", show.ids(Tl.Sess.roster(s)), " d=", reach(s, 6n, 0n), " n=", Nat.show(List.length(&2, List<&2, Nat>, Tl.Sess.sent(s))), " eq=", show.bool(Tl.all_eq(Tl.Sess.sent(s), Tl.Sess.roster(s))), "\n"])

def schema.eq(+a: Tl.Schema, +b: Tl.Schema) -> Bool:
  Bool.and(Tl.ids.eq(Tl.Schema.params(a), Tl.Schema.params(b)), Nat.is_eq(Tl.Schema.version(a), Tl.Schema.version(b)))

# a built schema, and whether building it again changes nothing
def show.schema(+b: Tl.Schema) -> String:
  String.concat(["b=", show.ids(Tl.Schema.params(b)), " v=", Nat.show(Tl.Schema.version(b)), " idem=", show.bool(schema.eq(Tl.build(b), b)), "\n"])

# what one line did: the session after it, and its output
type Out is Data:
  Out{s: Tl.Sess, text: String}

def Out.s(o: Out) -> Tl.Sess:
  match o:
    case Out{s, t}:
      s

def Out.text(o: Out) -> String:
  match o:
    case Out{s, t}:
      t

def out(+s: Tl.Sess) -> Out:
  Out{s, show.sess(s)}

# Running
# -------

def apply(k: Nat, +ws: List<&2, String>, +s: Tl.Sess) -> Out:
  match k:
    case 0n:
      out(Tl.Sess{nats(rest(ws, 1n)), Nil{}, Nil{}})
    case 1n:
      out(Tl.step(s, Tl.Join{tok.nat(tok.at(ws, 1n))}))
    case 2n:
      out(Tl.step(s, Tl.Quit{tok.nat(tok.at(ws, 1n))}))
    case 3n:
      out(Tl.step(s, Tl.Turn{}))
    case 4n:
      Out{s, show.schema(Tl.build(Tl.Schema{nats(rest(ws, 2n)), tok.nat(tok.at(ws, 1n))}))}
    case _:
      Out{s, ""}

# the output of each line of the scenario
def go(ls: List<&2, String>, +s: Tl.Sess) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> more:
      +ws = String.split(l, ' ')
      +o = apply(Maybe.default(&2, Nat, Nat.read(tok.at(ws, 0n)), 9n), ws, s)
      String.append(Out.text(o), go(more, Out.s(o)))

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
      IO.die(String, 2, "usage: bridge_tools <scenario>")
    case prog <> more:
      match more:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_tools <scenario>")
        case path <> others:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), Tl.Sess{Nil{}, Nil{}, Nil{}}))
