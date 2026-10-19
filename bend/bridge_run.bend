# bridge_run: runs the run model (bend/run.bend) on a scenario file and
# prints what it did, line for line as the Rust bridge test prints the
# Rust decisions (crates/eukhe-durable/src/harness/generation/bridge.rs).
# Build it with
#
#   bend bend/bridge_run.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one input per line:
#
#   9 cap polls retries notes     the limits (first line)
#   a                             an abort
#   g kind flag fin got [extra]   a Go: kind t text, c calls, d deferred,
#                                 e error (flag: retryable; extra: noted
#                                 0/1, the reply was cut), o overflow
#                                 (flag: a cut exists), m a message that
#                                 ends the model's turn, which
#                                 R.Ended.reply reads (flag unused, 0;
#                                 extra: text 0/1, then calls 0/1); fin 0
#                                 goes on, 1 stops, 2 resets; got 0
#                                 built, 1 kept, 2 broke
#
# After each input it prints what the input did to the requests (R.Reqs),
# then the run with the counts left, as the model keeps them (the Rust
# side subtracts its counts from the limits):
#
#   sent <ctx>.<note>             the run sent this request
#   cut <ctx>.<note>              the reply to this request was noted
#   prepare a=<retries> n=<notes> c=<compactions> r=<rounds>
#   call a=<retries> n=<notes> p=<polls> c=<compactions> r=<rounds>
#   compact overflow|threshold a=<retries> n=<notes> c=<compactions> r=<rounds>
#   tools a=<retries> n=<notes> c=<compactions> r=<rounds>
#   answered | aborted | failed model|polls|rounds

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
      R.Ended.reply(R.Ended{tok.bool(tok.at(ws, 5n)), tok.bool(tok.at(ws, 6n))})
    case False{} True{} c d e:
      R.Text{}
    case False{} False{} True{} d e:
      R.Calls{}
    case False{} False{} False{} True{} e:
      R.Deferred{}
    case False{} False{} False{} False{} True{}:
      R.Error{flag, tok.bool(tok.at(ws, 5n))}
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
      R.Go{reply.of(tok.head(tok.at(ws, 1n)), tok.bool(tok.at(ws, 2n)), ws), fin.of(tok.nat(tok.at(ws, 3n))), got.of(tok.nat(tok.at(ws, 4n)))}

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

def show.over(over: Bool) -> String:
  match over:
    case True{}:
      " overflow"
    case False{}:
      " threshold"

# a=<retries> n=<notes> c=<compactions> r=<rounds>, all left
def show.counts(+s: R.St) -> String:
  String.concat([" a=", Nat.show(R.St.a(s)), " n=", Nat.show(R.St.n(s)), " c=", Nat.show(R.St.c(s)), " r=", Nat.show(R.St.r(s))])

def show.ph(ph: R.Ph, +s: R.St) -> String:
  match ph:
    case R.Prepare{}:
      String.concat(["prepare", show.counts(s), "\n"])
    case R.Call{}:
      String.concat(["call a=", Nat.show(R.St.a(s)), " n=", Nat.show(R.St.n(s)), " p=", Nat.show(R.St.p(s)), " c=", Nat.show(R.St.c(s)), " r=", Nat.show(R.St.r(s)), "\n"])
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

def show.req(q: R.Req) -> String:
  match q:
    case R.Req{ctx, note}:
      String.concat([Nat.show(ctx), ".", Nat.show(note), "\n"])

def show.sent(x: R.Sent) -> String:
  match x:
    case R.Sent{q}:
      String.append("sent ", show.req(q))
    case R.Cut{q}:
      String.append("cut ", show.req(q))

# the request the input sent or cut: the newest of the log, when it grew
def show.new(same: Bool, log: List<&2, R.Sent>) -> String:
  match same log:
    case True{} log:
      ""
    case False{} Nil{}:
      ""
    case False{} x <> t:
      show.sent(x)

# Running
# -------

# what one line did: the limits, the run and its requests after it, and
# its output
type Out is Data:
  Out{cfg: R.Cfg, s: R.St, t: R.Reqs, text: String}

def Out.cfg(o: Out) -> R.Cfg:
  match o:
    case Out{c, s, t, x}:
      c

def Out.s(o: Out) -> R.St:
  match o:
    case Out{c, s, t, x}:
      s

def Out.t(o: Out) -> R.Reqs:
  match o:
    case Out{c, s, t, x}:
      t

def Out.text(o: Out) -> String:
  match o:
    case Out{c, s, t, x}:
      x

# a line: the limits (`9 ...`), nothing (a blank line), or an input
def line(config: Bool, blank: Bool, +ws: List<&2, String>, +cfg: R.Cfg, +s: R.St, +t: R.Reqs) -> Out:
  match config blank:
    case True{} blank:
      +c = limits.of(ws)
      Out{c, R.init(c), R.Reqs.init(), ""}
    case False{} True{}:
      Out{cfg, s, t, ""}
    case False{} False{}:
      +e = ev.of(ws)
      +s2 = R.step(cfg, s, e)
      +t2 = R.Reqs.step(R.St.ph(s), e, R.St.ph(s2), t)
      +same = Nat.is_eq(List.length(&2, R.Sent, R.Reqs.log(t)), List.length(&2, R.Sent, R.Reqs.log(t2)))
      Out{cfg, s2, t2, String.append(show.new(same, R.Reqs.log(t2)), show.st(s2))}

def go(ls: List<&2, String>, +cfg: R.Cfg, +s: R.St, +t: R.Reqs) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +k = tok.head(tok.at(ws, 0n))
      +o = line(Char.is_eq(k, '9'), Char.is_eq(k, ' '), ws, cfg, s, t)
      String.append(Out.text(o), go(rest, Out.cfg(o), Out.s(o), Out.t(o)))

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
    IO.write(go(String.lines(text), R.Cfg{0n, 0n, 0n, 0n}, R.init(R.Cfg{0n, 0n, 0n, 0n}), R.Reqs.init()))
