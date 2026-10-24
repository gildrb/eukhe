import Base
import ./wire.bend as W
import ./skill_load.bend as M

# ffi_skill_load: the check of a skill file's frontmatter and the
# description of a prompt template (bend/skill_load.bend `check`,
# `summary`) as an entry of the compiled Bend core. Request: a tag, then
#   0  a skill file: its frontmatter's name (0 none | 1 and the string),
#      its dir's name, its frontmatter's description (0 none | 1 and the
#      string)
#   1  a template: its frontmatter's description (0 none | 1 and the
#      string), its body
# Reply: a skill: T|F it loads, its name, then the messages (a count, then
# each); a template: its description. Any other input: the error form.

# Decoding
# --------

def get_text.some(r: W.Dec<String>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_text.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, String>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_text.some(W.get_str(s))
    case 2n+p:
      W.Bad{}

def get_text.go(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{t, s}:
      get_text.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a string that may be missing
def get_text(s: String) -> W.Dec<Maybe<&2, String>>:
  get_text.go(W.get_nat(s))

def get_skill.desc(n: Maybe<&2, String>, p: String, r: W.Dec<Maybe<&2, String>>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{d, s}:
      W.Got{M.AskSkill{n, p, d}, s}
    case W.Bad{}:
      W.Bad{}

def get_skill.parent(n: Maybe<&2, String>, r: W.Dec<String>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{p, s}:
      get_skill.desc(n, p, get_text(s))
    case W.Bad{}:
      W.Bad{}

def get_skill(r: W.Dec<Maybe<&2, String>>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{n, s}:
      get_skill.parent(n, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_template.body(d: Maybe<&2, String>, r: W.Dec<String>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{b, s}:
      W.Got{M.AskTemplate{d, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_template(r: W.Dec<Maybe<&2, String>>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{d, s}:
      get_template.body(d, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_ask.tag(t: Nat, s: String) -> W.Dec<M.Ask>:
  match t:
    case 0n:
      get_skill(get_text(s))
    case 1n:
      get_template(get_text(s))
    case 2n+p:
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

def put_strs.items(xs: List<&2, String>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      W.put_str(x, put_strs.items(t, rest))

def put_strs(+xs: List<&2, String>, rest: String) -> String:
  W.put_nat(List.length(&2, String, xs), put_strs.items(xs, rest))

def put_checked(c: M.Checked) -> String:
  match c:
    case M.Checked{l, n, ms}:
      W.put_bool(l, W.put_str(n, put_strs(ms, "")))

# The entry
# ---------

# the answer to a request
def answer(a: M.Ask) -> String:
  match a:
    case M.AskSkill{n, p, d}:
      put_checked(M.check(n, p, d))
    case M.AskTemplate{d, b}:
      W.put_str(M.summary(d, b), "")

def fail() -> String:
  W.err("skill_load: malformed request")

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
