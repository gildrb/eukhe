# ffi_goal_text: the entry of the compiled Bend core for the texts of a
# thread goal (bend/goal_text.bend; Rust: eukhe-bend rules/goal_text.rs).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   goal     the status (0 idle | 1 active | 2 paused | 3 budget_limited |
#            4 complete | 5 error), the objective (Maybe<String>), the
#            token budget's digits (Maybe<String>), the tokens used and the
#            seconds used (digits, String each)
#   request  a question, its tag then its fields:
#            0 prompt: the kind (0 continuation | 1 budget limit |
#              2 objective updated), the goal
#            1 usage: the goal
#            2 host: the goal, whether the completion report is asked (Bool)
#   reply    prompt: the text (String); usage: Maybe<String>;
#            host: 0 nothing | 1, the tokens left (Maybe<String>), the
#            report (Maybe<String>)
#
# Malformed input, or input left after the request, answers
# `E goal_text: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./goal_text.bend as Gt

# A request of the entry
type Req is Data:
  QPrompt{kind: Gt.Prompt, goal: Gt.Goal}
  QUsage{goal: Gt.Goal}
  QHost{goal: Gt.Goal, ask: Bool}

# Requests
# --------

def get_ms.some(r: W.Dec<String>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_ms.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, String>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_ms.some(W.get_str(s))
    case 2n+u:
      W.Bad{}

def get_ms.start(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{t, s}:
      get_ms.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a Maybe<String> at the start of s
def get_ms(s: String) -> W.Dec<Maybe<&2, String>>:
  get_ms.start(W.get_nat(s))

def get_goal.secs(st: Gt.Status, o: Maybe<&2, String>, b: Maybe<&2, String>, u: String, r: W.Dec<String>) -> W.Dec<Gt.Goal>:
  match r:
    case W.Got{t, s}:
      W.Got{Gt.Goal{st, o, b, u, t}, s}
    case W.Bad{}:
      W.Bad{}

def get_goal.used(st: Gt.Status, o: Maybe<&2, String>, b: Maybe<&2, String>, r: W.Dec<String>) -> W.Dec<Gt.Goal>:
  match r:
    case W.Got{u, s}:
      get_goal.secs(st, o, b, u, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_goal.budget(st: Gt.Status, o: Maybe<&2, String>, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Gt.Goal>:
  match r:
    case W.Got{b, s}:
      get_goal.used(st, o, b, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_goal.obj(st: Gt.Status, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Gt.Goal>:
  match r:
    case W.Got{o, s}:
      get_goal.budget(st, o, get_ms(s))
    case W.Bad{}:
      W.Bad{}

def get_goal.status(t: Nat, s: String) -> W.Dec<Gt.Goal>:
  match t:
    case 0n:
      get_goal.obj(Gt.SIdle{}, get_ms(s))
    case 1n:
      get_goal.obj(Gt.SActive{}, get_ms(s))
    case 2n:
      get_goal.obj(Gt.SPaused{}, get_ms(s))
    case 3n:
      get_goal.obj(Gt.SBudgetLimited{}, get_ms(s))
    case 4n:
      get_goal.obj(Gt.SComplete{}, get_ms(s))
    case 5n:
      get_goal.obj(Gt.SError{}, get_ms(s))
    case 6n+u:
      W.Bad{}

def get_goal.start(r: W.Dec<Nat>) -> W.Dec<Gt.Goal>:
  match r:
    case W.Got{t, s}:
      get_goal.status(t, s)
    case W.Bad{}:
      W.Bad{}

# a goal at the start of s
def get_goal(s: String) -> W.Dec<Gt.Goal>:
  get_goal.start(W.get_nat(s))

def get_prompt(k: Gt.Prompt, r: W.Dec<Gt.Goal>) -> W.Dec<Req>:
  match r:
    case W.Got{g, s}:
      W.Got{QPrompt{k, g}, s}
    case W.Bad{}:
      W.Bad{}

def get_kind.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_prompt(Gt.KContinuation{}, get_goal(s))
    case 1n:
      get_prompt(Gt.KBudgetLimit{}, get_goal(s))
    case 2n:
      get_prompt(Gt.KObjectiveUpdated{}, get_goal(s))
    case 3n+u:
      W.Bad{}

def get_kind(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_kind.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_usage(r: W.Dec<Gt.Goal>) -> W.Dec<Req>:
  match r:
    case W.Got{g, s}:
      W.Got{QUsage{g}, s}
    case W.Bad{}:
      W.Bad{}

def get_ask(g: Gt.Goal, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QHost{g, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_host(r: W.Dec<Gt.Goal>) -> W.Dec<Req>:
  match r:
    case W.Got{g, s}:
      get_ask(g, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_kind(W.get_nat(s))
    case 1n:
      get_usage(get_goal(s))
    case 2n:
      get_host(get_goal(s))
    case 3n+u:
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

def put_ms(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, W.put_str(x, rest))

def put_host(m: Maybe<&2, Gt.Host>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{h}:
      match h:
        case Gt.Host{r, p}:
          W.put_nat(1n, put_ms(r, put_ms(p, "")))

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QPrompt{k, g}:
      W.put_str(Gt.prompt(k, g), "")
    case QUsage{g}:
      put_ms(Gt.usage(g), "")
    case QHost{g, a}:
      put_host(Gt.host(g, a))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("goal_text: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("goal_text: malformed request")

# the entry: decode the request, answer the model's text
def ffi(input: String) -> String:
  ffi.got(get_req(input))
