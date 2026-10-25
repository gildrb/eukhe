# ffi_compaction_cut: the entry of the compiled Bend core for where a
# compaction cuts the model context and what the summarizer's answer is
# (bend/compaction_cut.bend; Rust: crates/eukhe-durable/src/harness/
# compaction/range.rs and compaction.rs through
# `eukhe_bend::rules::compaction_cut`). The request is a question
# (crates/eukhe-bend/WIRE.md is the grammar; Stop and Msg are
# bend/ffi_context_order.bend's):
#
#   Limit    0 never | 1 Nat (below k)
#   Contrib  Nat (its tokens), List<Msg>
#
#   tag 0 cut:     Bool (a head marker leads), Limit, List<Contrib>
#                  -> Maybe<Nat> (the first contribution kept)
#   tag 1 summary: Stop, Bool (it called a tool), Bool (its trimmed text
#                  is not blank), Maybe<String> (its error message)
#                  -> 0 (a summary) | 1 String (the failure)
#
# Malformed input, or input left after the request, answers
# `E compaction_cut: malformed request`, never a default. Pure: no IO, no
# @unsafe.

import Base
import ./wire.bend as W
import ./context_order.bend as Co
import ./ffi_context_order.bend as FCo
import ./compaction_cut.bend as Cc

# A request of the entry
type Req is Data:
  QCut{head: Bool, lim: Cc.Limit, cs: List<&2, Cc.Contrib>}
  QSummary{stop: Co.Stop, calls: Bool, text: Bool, err: Maybe<&2, String>}

# Facts
# -----

def get_limit.k(r: W.Dec<Nat>) -> W.Dec<Cc.Limit>:
  match r:
    case W.Got{k, s}:
      W.Got{Cc.Below{k}, s}
    case W.Bad{}:
      W.Bad{}

def get_limit.tag(r: W.Dec<Nat>) -> W.Dec<Cc.Limit>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Cc.Never{}, s}
        case 1n:
          get_limit.k(W.get_nat(s))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a limit: its tag, then its k
def get_limit(s: String) -> W.Dec<Cc.Limit>:
  get_limit.tag(W.get_nat(s))

def get_contrib.ms(n: Nat, r: W.Dec<List<&2, Co.Msg>>) -> W.Dec<Cc.Contrib>:
  match r:
    case W.Got{ms, s}:
      W.Got{Cc.Contrib{n, ms}, s}
    case W.Bad{}:
      W.Bad{}

def get_contrib.tokens(r: W.Dec<Nat>) -> W.Dec<Cc.Contrib>:
  match r:
    case W.Got{n, s}:
      get_contrib.ms(n, FCo.get_msgs(s))
    case W.Bad{}:
      W.Bad{}

# a contribution: its tokens, then its messages
def get_contrib(s: String) -> W.Dec<Cc.Contrib>:
  get_contrib.tokens(W.get_nat(s))

def get_err.text(r: W.Dec<String>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{e, s}:
      W.Got{Some{e}, s}
    case W.Bad{}:
      W.Bad{}

def get_err.tag(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_err.text(W.get_str(s))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# an error message, if any
def get_err(s: String) -> W.Dec<Maybe<&2, String>>:
  get_err.tag(W.get_nat(s))

# Requests
# --------

def get_cut.cs(h: Bool, l: Cc.Limit, r: W.Dec<List<&2, Cc.Contrib>>) -> W.Dec<Req>:
  match r:
    case W.Got{cs, s}:
      W.Got{QCut{h, l, cs}, s}
    case W.Bad{}:
      W.Bad{}

def get_cut.lim(h: Bool, r: W.Dec<Cc.Limit>) -> W.Dec<Req>:
  match r:
    case W.Got{l, s}:
      get_cut.cs(h, l, W.get_list(~Cc.Contrib, ~get_contrib, s))
    case W.Bad{}:
      W.Bad{}

def get_cut(r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{h, s}:
      get_cut.lim(h, get_limit(s))
    case W.Bad{}:
      W.Bad{}

def get_summary.err(st: Co.Stop, c: Bool, x: Bool, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{e, s}:
      W.Got{QSummary{st, c, x, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_summary.text(st: Co.Stop, c: Bool, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      get_summary.err(st, c, x, get_err(s))
    case W.Bad{}:
      W.Bad{}

def get_summary.calls(st: Co.Stop, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_summary.text(st, c, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_summary(r: W.Dec<Co.Stop>) -> W.Dec<Req>:
  match r:
    case W.Got{st, s}:
      get_summary.calls(st, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_cut(W.get_bool(s))
        case 1n:
          get_summary(FCo.get_stop(s))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a request: its tag, then its question
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# Replies
# -------

def put_outcome(o: Cc.Outcome) -> String:
  match o:
    case Cc.Summary{}:
      W.put_nat(0n, "")
    case Cc.Failed{text}:
      W.put_nat(1n, W.put_str(text, ""))

# the answer to a request
def answer(q: Req) -> String:
  match q:
    case QCut{h, l, cs}:
      FCo.put_mnat(Cc.cut(h, l, cs), "")
    case QSummary{st, c, x, e}:
      put_outcome(Cc.summary(st, c, x, e))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("compaction_cut: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("compaction_cut: malformed request")

# the entry: decode the request, answer it
def ffi(input: String) -> String:
  ffi.got(get_req(input))
