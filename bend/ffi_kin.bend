# ffi_kin: the entry of the compiled Bend core for agent messaging in a
# tree (bend/kin.bend; Rust: eukhe-bend rules/kin.rs).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   tag 0  admit  the sender (String), the target (String), the edges'
#                 children (List<String>), their parents (List<String>;
#                 edge i is children[i] -> parents[i], paired up to the
#                 shorter list)
#                 -> 0, the relation (0 Parent | 1 Child) | 1, the
#                    refusal's text (String)
#   tag 1  land   the target's state (0 Busy | 1 Idle | 2 Parked)
#                 -> the landing (0 Queue | 1 Deliver | 2 WakeThenDeliver)
#
# Malformed input, or input left after the request, answers
# `E kin: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./kin.bend as K

# A request of the entry
type Req is Data:
  QAdmit{sender: String, target: String, children: List<&2, String>, parents: List<&2, String>}
  QLand{state: K.State}

# Requests
# --------

def get_strs(s: String) -> W.Dec<List<&2, String>>:
  W.get_list(~String, ~W.get_str, s)

def get_admit.parents(sn: String, tg: String, cs: List<&2, String>, r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{ps, s}:
      W.Got{QAdmit{sn, tg, cs, ps}, s}
    case W.Bad{}:
      W.Bad{}

def get_admit.children(sn: String, tg: String, r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{cs, s}:
      get_admit.parents(sn, tg, cs, get_strs(s))
    case W.Bad{}:
      W.Bad{}

def get_admit.target(sn: String, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{tg, s}:
      get_admit.children(sn, tg, get_strs(s))
    case W.Bad{}:
      W.Bad{}

def get_admit(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{sn, s}:
      get_admit.target(sn, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_land.of(n: Nat, s: String) -> W.Dec<Req>:
  match n:
    case 0n:
      W.Got{QLand{K.Busy{}}, s}
    case 1n:
      W.Got{QLand{K.Idle{}}, s}
    case 2n:
      W.Got{QLand{K.Parked{}}, s}
    case 3n+u:
      W.Bad{}

def get_land(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_land.of(n, s)
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_admit(W.get_str(s))
    case 1n:
      get_land(W.get_nat(s))
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

def put_relation(r: K.Relation) -> String:
  match r:
    case K.Parent{}:
      W.put_nat(0n, "")
    case K.Child{}:
      W.put_nat(1n, "")

def put_verdict(v: K.Verdict) -> String:
  match v:
    case K.Admit{r}:
      W.put_nat(0n, put_relation(r))
    case K.Refuse{f}:
      W.put_nat(1n, W.put_str(K.text(f), ""))

def put_landing(l: K.Landing) -> String:
  match l:
    case K.Queue{}:
      W.put_nat(0n, "")
    case K.Deliver{}:
      W.put_nat(1n, "")
    case K.WakeThenDeliver{}:
      W.put_nat(2n, "")

# the reply of a request: the model's decision or landing, encoded
def answer(q: Req) -> String:
  match q:
    case QAdmit{sn, tg, cs, ps}:
      put_verdict(K.decide(sn, tg, cs, ps))
    case QLand{st}:
      put_landing(K.land(st))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("kin: malformed request")

def ffi.got(x: W.Dec<Req>) -> String:
  match x:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("kin: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
