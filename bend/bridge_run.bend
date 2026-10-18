# bridge_run: runs the run model (bend/run.bend) on a scenario file and
# prints what it did, line for line as the Rust bridge test prints the
# Rust decisions (crates/eukhe-durable/src/harness/generation/bridge.rs).
# Build it with
#
#   bend bend/bridge_run.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one input per line:
#
#   9 cap polls retries loop      the limits (first line)
#   a                             an abort
#   g kind flag hash fin got      a Go: kind t text, c calls, d deferred,
#     [tool text calls]           e error (flag: retryable), o overflow
#                                 (flag: a cut exists), m a message that
#                                 ends the model's turn, which
#                                 R.Ended.reply reads (flag: the retry
#                                 policy is on; tool: its stop reason is
#                                 tool use, text: it has text, calls: it
#                                 has a tool call); fin 0 goes on, 1
#                                 stops, 2 resets; got 0 built, 1 kept,
#                                 2 broke
#
# After each input it prints the run with the counts left, as the model
# keeps them (the Rust side subtracts its counts from the limits):
#
#   prepare a=<retries> c=<compactions> r=<rounds> s=<same>
#   call a=<retries> p=<polls> c=<compactions> r=<rounds> s=<same>
#   compact overflow|threshold a=<retries> c=<compactions> r=<rounds> s=<same>
#   tools a=<retries> c=<compactions> r=<rounds> s=<same>
#   answered | aborted | failed model|polls|rounds|loop

import Base
import ./run.bend as R

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.bool(s: String) -> Bool:
  Nat.is_eq(tok.nat(s), 1n)

def tok.head(s: String) -> Char:
  match s:
    case SNil{}:
      ' '
    case SCon{c, t}:
      c

def reply.pick(m: Bool, t: Bool, c: Bool, d: Bool, e: Bool, flag: Bool, +ws: List<&2, String>) -> R.Reply:
  match m t c d e:
    case True{} t c d e:
      R.Ended.reply(R.Ended{tok.bool(tok.at(ws, 6n)), tok.bool(tok.at(ws, 7n)), tok.bool(tok.at(ws, 8n)), flag})
    case False{} True{} c d e:
      R.Text{}
    case False{} False{} True{} d e:
      R.Calls{}
    case False{} False{} False{} True{} e:
      R.Deferred{}
    case False{} False{} False{} False{} True{}:
      R.Error{flag}
    case False{} False{} False{} False{} False{}:
      R.Overflow{flag}

def reply.of(+k: Char, flag: Bool, +ws: List<&2, String>) -> R.Reply:
  reply.pick(Char.is_eq(k, 'm'), Char.is_eq(k, 't'), Char.is_eq(k, 'c'), Char.is_eq(k, 'd'), Char.is_eq(k, 'e'), flag, ws)

def fin.of(n: Nat) -> R.Fin:
  match n:
    case 0n:
      R.Goes{}
    case 1n+m:
      match m:
        case 0n:
          R.Stops{}
        case 1n+k:
          R.Resets{}

def got.of(n: Nat) -> R.Got:
  match n:
    case 0n:
      R.Built{}
    case 1n+m:
      match m:
        case 0n:
          R.Kept{}
        case 1n+k:
          R.Broke{}

def ev.pick(abort: Bool, +ws: List<&2, String>) -> R.Ev:
  match abort:
    case True{}:
      R.Abort{}
    case False{}:
      R.Go{reply.of(tok.head(tok.at(ws, 1n)), tok.bool(tok.at(ws, 2n)), ws), tok.nat(tok.at(ws, 3n)), fin.of(tok.nat(tok.at(ws, 4n))), got.of(tok.nat(tok.at(ws, 5n)))}

def ev.of(+ws: List<&2, String>) -> R.Ev:
  ev.pick(Char.is_eq(tok.head(tok.at(ws, 0n)), 'a'), ws)

def limits.of(+ws: List<&2, String>) -> R.Cfg:
  R.Cfg{tok.nat(tok.at(ws, 1n)), tok.nat(tok.at(ws, 2n)), tok.nat(tok.at(ws, 3n)), tok.nat(tok.at(ws, 4n))}

# Writing
# -------

def show.why(w: R.Why) -> String:
  match w:
    case R.Model{}:
      "model"
    case R.Polls{}:
      "polls"
    case R.Rounds{}:
      "rounds"
    case R.Loop{}:
      "loop"

def show.over(over: Bool) -> String:
  match over:
    case True{}:
      " overflow"
    case False{}:
      " threshold"

# a=<retries> c=<compactions> r=<rounds> s=<same>, all left
def show.counts(+s: R.St) -> String:
  String.concat([" a=", Nat.show(R.St.a(s)), " c=", Nat.show(R.St.c(s)), " r=", Nat.show(R.St.r(s)), " s=", Nat.show(R.St.same(s))])

def show.ph(ph: R.Ph, +s: R.St) -> String:
  match ph:
    case R.Prepare{}:
      String.concat(["prepare", show.counts(s), "\n"])
    case R.Call{}:
      String.concat(["call a=", Nat.show(R.St.a(s)), " p=", Nat.show(R.St.p(s)), " c=", Nat.show(R.St.c(s)), " r=", Nat.show(R.St.r(s)), " s=", Nat.show(R.St.same(s)), "\n"])
    case R.Compact{over}:
      String.concat(["compact", show.over(over), show.counts(s), "\n"])
    case R.Tools{}:
      String.concat(["tools", show.counts(s), "\n"])
    case R.Answered{}:
      "answered\n"
    case R.Aborted{}:
      "aborted\n"
    case R.Failed{why}:
      String.concat(["failed ", show.why(why), "\n"])

def show.st(+s: R.St) -> String:
  show.ph(R.St.ph(s), s)

# Running
# -------

# what one line did: the limits and the run after it, and its output
type Out is Data:
  Out{cfg: R.Cfg, s: R.St, text: String}

def Out.cfg(o: Out) -> R.Cfg:
  match o:
    case Out{c, s, t}:
      c

def Out.s(o: Out) -> R.St:
  match o:
    case Out{c, s, t}:
      s

def Out.text(o: Out) -> String:
  match o:
    case Out{c, s, t}:
      t

# a line: the limits (`9 ...`), nothing (a blank line), or an input
def line(config: Bool, blank: Bool, +ws: List<&2, String>, +cfg: R.Cfg, +s: R.St) -> Out:
  match config blank:
    case True{} blank:
      +c = limits.of(ws)
      Out{c, R.init(c), ""}
    case False{} True{}:
      Out{cfg, s, ""}
    case False{} False{}:
      +t = R.step(cfg, s, ev.of(ws))
      Out{cfg, t, show.st(t)}

def go(ls: List<&2, String>, +cfg: R.Cfg, +s: R.St) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +k = tok.head(tok.at(ws, 0n))
      +o = line(Char.is_eq(k, '9'), Char.is_eq(k, ' '), ws, cfg, s)
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
      IO.die(String, 2, "usage: bridge_run <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_run <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), R.Cfg{0n, 0n, 0n, 0n}, R.init(R.Cfg{0n, 0n, 0n, 0n})))
