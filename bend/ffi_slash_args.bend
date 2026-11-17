# ffi_slash_args: the entry of the compiled Bend core for the arguments of
# `/auto` (typed as `/auto`, `/autonomous` or `/goal`), a goal objective
# and the words of a command's argument text (bend/slash_args.bend; Rust:
# eukhe-bend rules/slash_args.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  a question, its tag then the text (String):
#            0 /goal | 1 /auto | 2 words | 3 objective | 4 /autonomous
#   reply    /auto, /autonomous, /goal: how it was typed (0 /auto or
#              /autonomous | 1 /goal), then the answer
#            answer: 0 status | 1 on, the options | 2 off
#                  | 3 error, its text (String)
#                  | 4 task, its text (String), the token budget's digits
#                    (Maybe<String>)
#              options: four limits (continuations, turns, tokens,
#                timeout), each Maybe of 0 unlimited | 1 digits (String);
#                the gates, Maybe of: the commands (Maybe<List<String>>),
#                the retries and the timeout digits (Maybe<String> each);
#                the keep-alive digits (Maybe<String>)
#            words: the words (List<String>)
#            objective: the answer: 4 task, the objective trimmed and no
#              budget (0), or 3 error
#
# Malformed input, or input left after the request, answers
# `E slash_args: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./slash_args.bend as Sa

# A request of the entry
type Req is Data:
  QGoal{args: String}
  QAuto{args: String}
  QWords{args: String}
  # a goal objective as a goal tool gives it
  QObjective{text: String}
  QAutonomous{args: String}

def get_goal(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QGoal{a}, s}
    case W.Bad{}:
      W.Bad{}

def get_auto(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QAuto{a}, s}
    case W.Bad{}:
      W.Bad{}

def get_words(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QWords{a}, s}
    case W.Bad{}:
      W.Bad{}

def get_objective(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QObjective{a}, s}
    case W.Bad{}:
      W.Bad{}

def get_autonomous(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QAutonomous{a}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_goal(W.get_str(s))
    case 1n:
      get_auto(W.get_str(s))
    case 2n:
      get_words(W.get_str(s))
    case 3n:
      get_objective(W.get_str(s))
    case 4n:
      get_autonomous(W.get_str(s))
    case 5n+u:
      W.Bad{}

def get_req.start(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.start(W.get_nat(s))

# Replies
# -------

def put_mstr(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, W.put_str(x, rest))

def put_mlim(m: Maybe<&2, Sa.Lim>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{l}:
      match l:
        case Sa.LUnl{}:
          W.put_nat(1n, W.put_nat(0n, rest))
        case Sa.LNum{d}:
          W.put_nat(1n, W.put_nat(1n, W.put_str(d, rest)))

def put_mcmds(m: Maybe<&2, List<&2, String>>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{cs}:
      W.put_nat(1n, W.put_list(~String, ~W.put_str, cs, rest))

def put_mgates(m: Maybe<&2, Sa.Gates>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{g}:
      match g:
        case Sa.Gates{cs, r, t}:
          W.put_nat(1n, put_mcmds(cs, put_mstr(r, put_mstr(t, rest))))

def put_conf(c: Sa.Conf) -> String:
  match c:
    case Sa.Conf{a, b, k, m, g, p}:
      put_mlim(a, put_mlim(b, put_mlim(k, put_mlim(m, put_mgates(g, put_mstr(p, ""))))))

def put_auto(a: Sa.Auto) -> String:
  match a:
    case Sa.AStatus{}:
      W.put_nat(0n, "")
    case Sa.AOn{c}:
      W.put_nat(1n, put_conf(c))
    case Sa.AOff{}:
      W.put_nat(2n, "")
    case Sa.AErr{e}:
      W.put_nat(3n, W.put_str(e, ""))
    case Sa.ATask{t, b}:
      W.put_nat(4n, W.put_str(t, put_mstr(b, "")))

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QGoal{a}:
      W.put_nat(1n, put_auto(Sa.goal(a)))
    case QAuto{a}:
      W.put_nat(0n, put_auto(Sa.auto(a)))
    case QWords{a}:
      W.put_list(~String, ~W.put_str, Sa.words(a), "")
    case QObjective{a}:
      put_auto(Sa.goal.objective(a, None{}))
    case QAutonomous{a}:
      W.put_nat(0n, put_auto(Sa.auto(a)))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("slash_args: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("slash_args: malformed request")

# the entry: decode the request, answer the model's answer
def ffi(input: String) -> String:
  ffi.got(get_req(input))
