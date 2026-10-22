# ffi_child_env: the entry of the child environment (bend/child_env.bend)
# in the compiled Bend core. Rust (crates/eukhe-core/src/kernel/manager/
# startup.rs, `child_env`) sends the registry, the keep list, the base and
# the overlay, and reads the environment of the child.
#
# Request (crates/eukhe-bend/WIRE.md): a record
#   reg: List<String>, keep: List<String>, base: List<Var>, over: List<Var>
# with Var = a record (name: String, value: String).
# Reply: List<Var>, the environment of the child (Env.child).
#
# The model never reads a value (the laws: a variable reaches the child
# with its value, and no variable is invented), so the Rust code sends a
# short token for each value and maps the tokens of the reply back.

import Base
import ./wire.bend as W
import ./child_env.bend as Env

# Variables
# ---------

def put_var(v: Env.Var, rest: String) -> String:
  match v:
    case Env.Var{n, x}:
      W.put_str(n, W.put_str(x, rest))

def get_var.value(n: String, r: W.Dec<String>) -> W.Dec<Env.Var>:
  match r:
    case W.Got{x, s}:
      W.Got{Env.Var{n, x}, s}
    case W.Bad{}:
      W.Bad{}

def get_var.name(r: W.Dec<String>) -> W.Dec<Env.Var>:
  match r:
    case W.Got{n, s}:
      get_var.value(n, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_var(s: String) -> W.Dec<Env.Var>:
  get_var.name(W.get_str(s))

# The request
# -----------

type Req is Data:
  Req{reg: List<&2, String>, keep: List<&2, String>, base: List<&2, Env.Var>, over: List<&2, Env.Var>}

def put_req(q: Req, rest: String) -> String:
  match q:
    case Req{r, k, b, o}:
      W.put_list(~String, ~W.put_str, r, W.put_list(~String, ~W.put_str, k, W.put_list(~Env.Var, ~put_var, b, W.put_list(~Env.Var, ~put_var, o, rest))))

def get_req.over(r: List<&2, String>, k: List<&2, String>, b: List<&2, Env.Var>, d: W.Dec<List<&2, Env.Var>>) -> W.Dec<Req>:
  match d:
    case W.Got{o, s}:
      W.Got{Req{r, k, b, o}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.base(r: List<&2, String>, k: List<&2, String>, d: W.Dec<List<&2, Env.Var>>) -> W.Dec<Req>:
  match d:
    case W.Got{b, s}:
      get_req.over(r, k, b, W.get_list(~Env.Var, ~get_var, s))
    case W.Bad{}:
      W.Bad{}

def get_req.keep(r: List<&2, String>, d: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match d:
    case W.Got{k, s}:
      get_req.base(r, k, W.get_list(~Env.Var, ~get_var, s))
    case W.Bad{}:
      W.Bad{}

def get_req.reg(d: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match d:
    case W.Got{r, s}:
      get_req.keep(r, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.reg(W.get_list(~String, ~W.get_str, s))

# The entry
# ---------

def ffi.run(q: Req) -> String:
  match q:
    case Req{r, k, b, o}:
      W.put_list(~Env.Var, ~put_var, Env.child(r, k, b, o), "")

def ffi.whole(q: Req, done: Bool) -> String:
  match done:
    case True{}:
      ffi.run(q)
    case False{}:
      W.err("child_env: input left over")

def ffi.go(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      ffi.whole(q, W.end(s))
    case W.Bad{}:
      W.err("child_env: malformed request")

# the environment of a child: the request in, the variables out
def ffi(input: String) -> String:
  ffi.go(get_req(input))
