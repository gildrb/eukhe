import Base
import ./wire.bend as W
import ./launcher.bend as M

# ffi_launcher: the decisions of a daemon replacement (bend/launcher.bend
# `admits`, `quiesce`, `quiesce.answer`, `commits`, `adoption`) as an
# entry of the compiled Bend core. Request: a tag, then
#   0  a run start: the gate is closed (T|F)
#   1  a quiesce: the worker holds work (T|F), its gate is closed (T|F)
#   2  the commit: a count, then per worker whether it quiesced (T|F)
#   3  an adoption: the worker's build: 0 none | 1 and its number (0 the
#      supervisor's build, 1 another)
# Reply: a run start: T it starts; a quiesce: the gate is closed after it
# (T|F), then the worker quiesced (T|F); the commit: T it commits; an
# adoption: 0 adopt | 1 replace. Any other input: the error form.

# Decoding
# --------

def get_prompt(r: W.Dec<Bool>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{c, s}:
      W.Got{M.AskPrompt{c}, s}
    case W.Bad{}:
      W.Bad{}

def get_quiesce.closed(b: Bool, r: W.Dec<Bool>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{c, s}:
      W.Got{M.AskQuiesce{b, c}, s}
    case W.Bad{}:
      W.Bad{}

def get_quiesce(r: W.Dec<Bool>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{b, s}:
      get_quiesce.closed(b, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_answers.cons(a: Bool, r: W.Dec<List<&2, Bool>>) -> W.Dec<List<&2, Bool>>:
  match r:
    case W.Got{xs, s}:
      W.Got{a <> xs, s}
    case W.Bad{}:
      W.Bad{}

# n more answers after the one cur answers
def get_answers.go(n: Nat, cur: W.Dec<Bool>) -> W.Dec<List<&2, Bool>>:
  match n:
    case 0n:
      match cur:
        case W.Got{a, s}:
          W.Got{[a], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{a, s}:
          get_answers.cons(a, get_answers.go(m, W.get_bool(s)))
        case W.Bad{}:
          W.Bad{}

def get_commit.answers(r: W.Dec<List<&2, Bool>>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{xs, s}:
      W.Got{M.AskCommit{xs}, s}
    case W.Bad{}:
      W.Bad{}

def get_commit(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{M.AskCommit{Nil{}}, s}
        case 1n+m:
          get_commit.answers(get_answers.go(m, W.get_bool(s)))
    case W.Bad{}:
      W.Bad{}

def get_adopt.some(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{b, s}:
      W.Got{M.AskAdopt{Some{b}}, s}
    case W.Bad{}:
      W.Bad{}

def get_adopt.tag(t: Nat, s: String) -> W.Dec<M.Ask>:
  match t:
    case 0n:
      W.Got{M.AskAdopt{None{}}, s}
    case 1n:
      get_adopt.some(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_adopt(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{t, s}:
      get_adopt.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_ask.tag(t: Nat, s: String) -> W.Dec<M.Ask>:
  match t:
    case 0n:
      get_prompt(W.get_bool(s))
    case 1n:
      get_quiesce(W.get_bool(s))
    case 2n:
      get_commit(W.get_nat(s))
    case 3n:
      get_adopt(W.get_nat(s))
    case 4n+p:
      W.Bad{}

def get_ask.go(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{t, s}:
      get_ask.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_ask(s: String) -> W.Dec<M.Ask>:
  get_ask.go(W.get_nat(s))

# Encoding
# --------

def put_adoption(a: M.Adoption, rest: String) -> String:
  match a:
    case M.Adopt{}:
      W.put_nat(0n, rest)
    case M.Replace{}:
      W.put_nat(1n, rest)

# The entry
# ---------

# the answer to a request
def answer(a: M.Ask) -> String:
  match a:
    case M.AskPrompt{c}:
      W.put_bool(M.admits(c), "")
    case M.AskQuiesce{+b, c}:
      W.put_bool(M.Wk.closed(M.quiesce(M.Wk{b, c})), W.put_bool(M.quiesce.answer(b), ""))
    case M.AskCommit{xs}:
      W.put_bool(M.commits(xs), "")
    case M.AskAdopt{w}:
      put_adoption(M.adoption(0n, w), "")

def fail() -> String:
  W.err("launcher: malformed request")

def run.end(whole: Bool, a: M.Ask) -> String:
  match whole:
    case True{}:
      answer(a)
    case False{}:
      fail()

def run(r: W.Dec<M.Ask>) -> String:
  match r:
    case W.Got{a, s}:
      run.end(W.end(s), a)
    case W.Bad{}:
      fail()

def ffi(input: String) -> String:
  run(get_ask(input))
