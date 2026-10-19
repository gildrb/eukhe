# bridge_aux_fallback: runs a session of summarizer passes through the
# auxiliary-model model (`run` in aux_fallback.bend) on a scenario file
# and prints its events, line for line as the Rust bridge test prints
# `decide_auxiliary_route` and `AuxiliaryNotices::take`
# (crates/eukhe-core/src/durable/compaction/auxiliary_model/tests/bridge.rs).
# Build it with
#
#   bend bend/bridge_aux_fallback.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one pass per line:
#
#   p sel s ok look arg need
#
#   p      the purpose (0: compaction summary, 1: branch summary)
#   sel    the selector (0: unset, 1: the session model, 2: model s)
#   ok     1 when allowedModels admits the selector
#   look   0: the lookups found nothing usable, with reason arg;
#          1: they found a model with context window arg (0: unknown)
#   need   the size of the request (0: unknown)
#
# It prints `S` (the session model), `R` (the selector's model),
# `F p s r` (the session model in place of selector s, reason r) and
# `N p s r` (the notice of that).

import Base
import ./aux_fallback.bend as Af

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def sel.of(k: Nat, s: Nat) -> Af.Sel:
  match k:
    case 0n:
      Af.Unset{}
    case 1n:
      Af.Same{}
    case _:
      Af.Other{s}

def look.of(k: Nat, a: Nat) -> Af.Look:
  match k:
    case 0n:
      Af.Miss{a}
    case _:
      Af.Hit{a}

def pass.of(+ws: List<&2, String>) -> Af.Pass:
  Af.Pass{tok.nat(tok.at(ws, 0n)), sel.of(tok.nat(tok.at(ws, 1n)), tok.nat(tok.at(ws, 2n))), Nat.is_eq(tok.nat(tok.at(ws, 3n)), 1n), look.of(tok.nat(tok.at(ws, 4n)), tok.nat(tok.at(ws, 5n))), tok.nat(tok.at(ws, 6n))}

# a line that starts with a number is a pass; others are skipped
def pass.add(m: Maybe<&2, Nat>, +ws: List<&2, String>, t: List<&2, Af.Pass>) -> List<&2, Af.Pass>:
  match m:
    case None{}:
      t
    case Some{x}:
      pass.of(ws) <> t

def passes(ls: List<&2, String>) -> List<&2, Af.Pass>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      +ws = String.split(l, ' ')
      pass.add(Nat.read(tok.at(ws, 0n)), ws, passes(rest))

# Writing
# -------

def show.key(k: Af.Key) -> String:
  match k:
    case Af.K{p, s, r}:
      String.concat([Nat.show(p), " ", Nat.show(s), " ", Nat.show(r), "\n"])

def show.ev(e: Af.Ev) -> String:
  match e:
    case Af.Stay{}:
      "S\n"
    case Af.Went{}:
      "R\n"
    case Af.Sub{k}:
      String.append("F ", show.key(k))
    case Af.Note{k}:
      String.append("N ", show.key(k))

def show(es: List<&2, Af.Ev>) -> String:
  match es:
    case Nil{}:
      ""
    case e <> rest:
      String.append(show.ev(e), show(rest))

# Running
# -------

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
      IO.die(String, 2, "usage: bridge_aux_fallback <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_aux_fallback <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(show(Af.run(passes(String.lines(text)))))
