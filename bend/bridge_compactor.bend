# bridge_compactor: runs the compactor's line and failure cap
# (bend/compactor.bend) on a scenario file and prints what they did, line
# for line as the Rust bridge test
# (crates/eukhe-core/src/memory/compactor/bridge.rs) prints the Rust
# build_line and Pend::after. Build it with
#
#   bend bend/bridge_compactor.bend -o <out>
#
# and run `<out> <scenario>`. A text is its characters' UTF-8 widths,
# digits 1-4 (`r` alone is an empty reply):
#
#   s tries node input   a new line: its tries, its size, its input
#   r text               the model's next reply
#   e                    the model's next call fails
#   .                    run the line; print `c=<calls> l=<text>`, `!` for
#                        a failed call
#   p cap outcomes       a line with cap failures before the cap builds it,
#                        then its calls' outcomes (f: the call failed, d:
#                        the disk failed); print `p=` and its failures left
#                        at the start and after each outcome, `M` once built

import Base
import ./compactor.bend as C

def w.pick(four: Bool, three: Bool, two: Bool) -> C.W:
  match four three two:
    case True{} _ _:
      C.W4{}
    case False{} True{} _:
      C.W3{}
    case False{} False{} True{}:
      C.W2{}
    case False{} False{} False{}:
      C.W1{}

def w.of(+c: Char) -> C.W:
  w.pick(Char.is_eq(c, '4'), Char.is_eq(c, '3'), Char.is_eq(c, '2'))

def text.of(s: String) -> List<&2, C.W>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      w.of(c) <> text.of(t)

def w.show(c: C.W) -> Char:
  match c:
    case C.W1{}:
      '1'
    case C.W2{}:
      '2'
    case C.W3{}:
      '3'
    case C.W4{}:
      '4'

def text.show(t: List<&2, C.W>) -> String:
  match t:
    case Nil{}:
      ""
    case c <> rest:
      SCon{w.show(c), text.show(rest)}

def line.show(m: Maybe<&2, List<&2, C.W>>) -> String:
  match m:
    case None{}:
      "!"
    case Some{t}:
      text.show(t)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

# a line being written: tries, node, input, the replies newest first
type Sc is Data:
  Sc{tries: Nat, node: Nat, input: List<&2, C.W>, rs: List<&2, C.Reply>}

# a scenario line's effect: the line after it, and what it printed
type Step is Data:
  Step{s: Sc, out: String}

def Step.s(st: Step) -> Sc:
  match st:
    case Step{s, o}:
      s

def Step.out(st: Step) -> String:
  match st:
    case Step{s, o}:
      o

def Sc.add(s: Sc, r: C.Reply) -> Sc:
  match s:
    case Sc{t, n, i, rs}:
      Sc{t, n, i, r <> rs}

def Sc.run(s: Sc) -> String:
  match s:
    case Sc{t, n, i, rs}:
      +o = C.line(t, n, i, List.reverse(&2, C.Reply, rs))
      String.concat(["c=", Nat.show(C.Line.calls(o)), " l=", line.show(C.Line.line(o)), "\n"])

def pend.pick(failed: Bool) -> C.Outcome:
  match failed:
    case True{}:
      C.Failed{}
    case False{}:
      C.Disk{}

def pend.show(p: C.Pend) -> String:
  match p:
    case C.Made{}:
      "M"
    case C.Owed{n}:
      Nat.show(n)

def pend.go(os: String, p: C.Pend) -> String:
  match os:
    case SNil{}:
      "\n"
    case SCon{c, t}:
      +q = C.Pend.after(p, pend.pick(Char.is_eq(c, 'f')))
      String.concat([" ", pend.show(q), pend.go(t, q)])

def pend.run(cap: Nat, os: String) -> String:
  +p = {C.Owed{Nat.sub(cap, 1n)} : C.Pend}
  String.concat(["p=", pend.show(p), pend.go(os, p)])

def apply.k(start: Bool, says: Bool, err: Bool, dot: Bool, cap: Bool, +ws: List<&2, String>, +s: Sc) -> Step:
  match start says err dot cap:
    case True{} _ _ _ _:
      Step{Sc{tok.nat(tok.at(ws, 1n)), tok.nat(tok.at(ws, 2n)), text.of(tok.at(ws, 3n)), Nil{}}, ""}
    case False{} True{} _ _ _:
      Step{Sc.add(s, C.Says{text.of(tok.at(ws, 1n))}), ""}
    case False{} False{} True{} _ _:
      Step{Sc.add(s, C.Erred{}), ""}
    case False{} False{} False{} True{} _:
      Step{s, Sc.run(s)}
    case False{} False{} False{} False{} True{}:
      Step{s, pend.run(tok.nat(tok.at(ws, 1n)), tok.at(ws, 2n))}
    case False{} False{} False{} False{} False{}:
      Step{s, ""}

def apply(+ws: List<&2, String>, +tag: String, s: Sc) -> Step:
  apply.k(String.eq(tag, "s"), String.eq(tag, "r"), String.eq(tag, "e"), String.eq(tag, "."), String.eq(tag, "p"), ws, s)

def go(ls: List<&2, String>, s: Sc) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +st = apply(ws, tok.at(ws, 0n), s)
      String.append(Step.out(st), go(rest, Step.s(st)))

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
      IO.die(String, 2, "usage: bridge_compactor <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_compactor <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), Sc{0n, 0n, Nil{}, Nil{}}))
