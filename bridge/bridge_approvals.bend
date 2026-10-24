# bridge_approvals: runs the model of where an approval question goes
# (bend/approvals.bend `route`) on an events file and prints what
# happened, line for line as the Rust bridge test prints the real
# approvals of a chain of sessions (crates/eukhe-daemon/src/
# shell_approval/bridge.rs). Each session's own decision runs in Rust as
# the compiled core (bend/ffi_approvals.bend); this bridge checks the
# interleaving: the relay over the supervisor, clients that leave, the
# first answer. Build it
# with
#
#   bend bridge/bridge_approvals.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   q E D D ...    a question. E: the step's effects, their codes
#                  (bend/tools.bend `Eff.code`) joined by `,`; then the
#                  chain, from the session that asks up to its root; each
#                  session D is 0 (no client), 1 (clients that leave
#                  without an answer), 2 (clients that deny), 3 (clients
#                  that approve), 4 (the phone gateway alone) or 5
#                  (clients that leave without an answer while the phone
#                  gateway stays)
#
# A question prints one line per session that showed it, in order,
#
#   shown K named 0|1   session K (0: the asker) showed it; the frame
#                       names the subagent that asks (1) or not (0)
#
# then how it ended:
#
#   end approve K | end deny K | end unanswered
#   end ruled run | end ruled refuse      (a gateway rule answered)

import Base
import ../bend/approvals.bend as Am

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def desk(n: Nat) -> Am.Desk:
  match n:
    case 0n:
      Am.Away{}
    case 1n+a:
      match a:
        case 0n:
          Am.Left{}
        case 1n+b:
          match b:
            case 0n:
              Am.Says{False{}}
            case 1n+c:
              match c:
                case 0n:
                  Am.Says{True{}}
                case 1n+d:
                  match d:
                    case 0n:
                      Am.Phone{}
                    case 1n+e:
                      Am.PhoneLeft{}

def desks(ws: List<&2, String>) -> List<&2, Am.Desk>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      desk(tok.nat(w)) <> desks(rest)

def codes(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      tok.nat(w) <> codes(rest)

# Writing
# -------

def show.bool(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def show.shown(ks: List<&2, Nat>) -> String:
  match ks:
    case Nil{}:
      ""
    case +k <> rest:
      String.concat(["shown ", Nat.show(k), " named ", show.bool(Am.named(k)), "\n", show.shown(rest)])

def show.ruled(f: Am.Fate) -> String:
  match f:
    case Am.Runs{}:
      "end ruled run\n"
    case Am.Denied{}:
      "end ruled deny\n"
    case Am.Unheard{}:
      "end ruled unheard\n"
    case Am.GatewayRefused{}:
      "end ruled refuse\n"

def show.end(+es: List<&2, Nat>, e: Am.End) -> String:
  match e:
    case Am.Answered{k, y}:
      match y:
        case True{}:
          String.concat(["end approve ", Nat.show(k), "\n"])
        case False{}:
          String.concat(["end deny ", Nat.show(k), "\n"])
    case Am.Unanswered{}:
      "end unanswered\n"
    case Am.Ruled{k}:
      show.ruled(Am.fate(es, Am.Ruled{k}))

def show.out(+es: List<&2, Nat>, o: Am.Out) -> String:
  match o:
    case Am.Out{s, e}:
      String.append(show.shown(s), show.end(es, e))

# the effects word and the chain's words after it
def ask(ws: List<&2, String>) -> String:
  match ws:
    case Nil{}:
      ""
    case w <> rest:
      show.out(codes(String.split(w, ',')), Am.route(desks(rest)))

# one word h and the words after it: a `q` line asks with the chain of
# the words after it
def word(h: String, rest: List<&2, String>) -> String:
  match h:
    case SCon{'q', r}:
      ask(rest)
    case r:
      ""

def line(ws: List<&2, String>) -> String:
  match ws:
    case Nil{}:
      ""
    case h <> rest:
      word(h, rest)

def go(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      String.append(line(String.split(l, ' ')), go(rest))

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
      IO.die(String, 2, "usage: bridge_approvals <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_approvals <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text)))
