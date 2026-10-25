# ffi_codemode_describe: the entry of the compiled Bend core for the code
# mode tool's description and its `codemode` section
# (bend/codemode_describe.bend; Rust: crates/eukhe-durable/src/codemode/
# describe.rs and call.rs through `eukhe_bend::rules::codemode_describe`).
# The request is a question (crates/eukhe-bend/WIRE.md is the grammar):
#
#   Tool   String (its name), Nat (its section's UTF-16 length)
#   Space  String (its name), String (its name in lowercase), String (its
#          prefix), String (its description trimmed, "" when none)
#   Part   0 String (a text) | 1 Nat (the section of the tool at an index)
#
#   tag 0 spaces:      List<String> (tool names), List<String> (prefixes)
#                      -> List<Maybe<Nat>> (each name's namespace index)
#   tag 1 section:     List<Tool>, List<Space>, Nat (the budget, tokens)
#                      -> Maybe<List<Part>> (none without tools)
#   tag 2 description: Bool (models globals), Bool (a default classifier)
#                      -> String
#
# Malformed input, or input left after the request, answers
# `E codemode_describe: malformed request`, never a default. Pure: no IO,
# no @unsafe.

import Base
import ./wire.bend as W
import ./codemode_describe.bend as Dsc

# A request of the entry
type Req is Data:
  QSpaces{names: List<&2, String>, prefixes: List<&2, String>}
  QSection{tools: List<&2, Dsc.Tool>, spaces: List<&2, Dsc.Space>, budget: Nat}
  QDescribe{models: Bool, classify: Bool}

# Facts
# -----

def get_tool.size(n: String, r: W.Dec<Nat>) -> W.Dec<Dsc.Tool>:
  match r:
    case W.Got{z, s}:
      W.Got{Dsc.Tool{n, z}, s}
    case W.Bad{}:
      W.Bad{}

def get_tool.name(r: W.Dec<String>) -> W.Dec<Dsc.Tool>:
  match r:
    case W.Got{n, s}:
      get_tool.size(n, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# a tool: its name, then its section's UTF-16 length
def get_tool(s: String) -> W.Dec<Dsc.Tool>:
  get_tool.name(W.get_str(s))

def get_space.about(n: String, k: String, p: String, r: W.Dec<String>) -> W.Dec<Dsc.Space>:
  match r:
    case W.Got{a, s}:
      W.Got{Dsc.Space{n, k, p, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_space.prefix(n: String, k: String, r: W.Dec<String>) -> W.Dec<Dsc.Space>:
  match r:
    case W.Got{p, s}:
      get_space.about(n, k, p, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_space.key(n: String, r: W.Dec<String>) -> W.Dec<Dsc.Space>:
  match r:
    case W.Got{k, s}:
      get_space.prefix(n, k, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_space.name(r: W.Dec<String>) -> W.Dec<Dsc.Space>:
  match r:
    case W.Got{n, s}:
      get_space.key(n, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

# a namespace: its name, its lowercase name, its prefix, its description
def get_space(s: String) -> W.Dec<Dsc.Space>:
  get_space.name(W.get_str(s))

# Requests
# --------

def get_spaces.prefixes(ns: List<&2, String>, r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{ps, s}:
      W.Got{QSpaces{ns, ps}, s}
    case W.Bad{}:
      W.Bad{}

def get_spaces(r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{ns, s}:
      get_spaces.prefixes(ns, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

def get_section.budget(ts: List<&2, Dsc.Tool>, ss: List<&2, Dsc.Space>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{b, s}:
      W.Got{QSection{ts, ss, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_section.spaces(ts: List<&2, Dsc.Tool>, r: W.Dec<List<&2, Dsc.Space>>) -> W.Dec<Req>:
  match r:
    case W.Got{ss, s}:
      get_section.budget(ts, ss, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_section(r: W.Dec<List<&2, Dsc.Tool>>) -> W.Dec<Req>:
  match r:
    case W.Got{ts, s}:
      get_section.spaces(ts, W.get_list(~Dsc.Space, ~get_space, s))
    case W.Bad{}:
      W.Bad{}

def get_describe.classify(m: Bool, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      W.Got{QDescribe{m, c}, s}
    case W.Bad{}:
      W.Bad{}

def get_describe(r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{m, s}:
      get_describe.classify(m, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_spaces(W.get_list(~String, ~W.get_str, s))
        case 1n:
          get_section(W.get_list(~Dsc.Tool, ~get_tool, s))
        case 2n:
          get_describe(W.get_bool(s))
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a request: its tag, then its question
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# Replies
# -------

def put_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def put_mnats(xs: List<&2, Maybe<&2, Nat>>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, r}:
      put_mnat(x, put_mnats(r, rest))

def put_part(p: Dsc.Part, rest: String) -> String:
  match p:
    case Dsc.Lit{t}:
      W.put_nat(0n, W.put_str(t, rest))
    case Dsc.Sect{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def put_parts(ps: List<&2, Dsc.Part>, rest: String) -> String:
  match ps:
    case Nil{}:
      rest
    case Con{p, r}:
      put_part(p, put_parts(r, rest))

def put_section(m: Maybe<&2, List<&2, Dsc.Part>>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{+ps}:
      W.put_nat(1n, W.put_nat(List.length(&2, Dsc.Part, ps), put_parts(ps, "")))

def spaces_of(ns: List<&2, String>, +ps: List<&2, String>) -> List<&2, Maybe<&2, Nat>>:
  match ns:
    case Nil{}:
      []
    case Con{n, r}:
      Dsc.space_of(n, ps) <> spaces_of(r, ps)

# the answer to a request
def answer(q: Req) -> String:
  match q:
    case QSpaces{ns, ps}:
      +xs = spaces_of(ns, ps)
      W.put_nat(List.length(&2, Maybe<&2, Nat>, xs), put_mnats(xs, ""))
    case QSection{ts, ss, b}:
      put_section(Dsc.section(ts, ss, b))
    case QDescribe{m, c}:
      W.put_str(Dsc.description(m, c), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("codemode_describe: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("codemode_describe: malformed request")

# the entry: decode the request, answer it
def ffi(input: String) -> String:
  ffi.got(get_req(input))
