# ffi_dash_access: the entry of the compiled Bend core for who may reach
# the dashboard (bend/dash_access.bend; Rust: crates/eukhe-dashboard
# access.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   tag 0  host    the request's `Host` (String), the hosts the user
#                  allowed (List<String>)       -> the verdict (Bool)
#   tag 1  origin  the `Origin` (String), the `Host` (String)
#                                               -> the verdict (Bool)
#
# Malformed input, or input left after the request, answers
# `E dash_access: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./dash_access.bend as Ac

# A request of the entry
type Req is Data:
  QHost{host: String, allowed: List<&2, String>}
  QOrigin{origin: String, host: String}

# Requests
# --------

def get_strs(s: String) -> W.Dec<List<&2, String>>:
  W.get_list(~String, ~W.get_str, s)

def get_host.allowed(h: String, r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{al, s}:
      W.Got{QHost{h, al}, s}
    case W.Bad{}:
      W.Bad{}

def get_host(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{h, s}:
      get_host.allowed(h, get_strs(s))
    case W.Bad{}:
      W.Bad{}

def get_origin.host(o: String, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{h, s}:
      W.Got{QOrigin{o, h}, s}
    case W.Bad{}:
      W.Bad{}

def get_origin(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{o, s}:
      get_origin.host(o, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_host(W.get_str(s))
    case 1n:
      get_origin(W.get_str(s))
    case 2n+u:
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

# The entry
# ---------

# the reply of a request: the model's verdict, encoded
def answer(q: Req) -> String:
  match q:
    case QHost{h, al}:
      W.put_bool(Ac.host_allowed(h, al), "")
    case QOrigin{o, h}:
      W.put_bool(Ac.same_origin(o, h), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("dash_access: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("dash_access: malformed request")

# the entry: decode the request, answer the model's verdict
def ffi(input: String) -> String:
  ffi.got(get_req(input))
