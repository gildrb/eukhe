# ffi_ai_text: the entry of the compiled Bend core for texts the eukhe-ai
# providers read (bend/ai_text.bend; Rust: eukhe-bend rules/ai_text.rs).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  0, id (String)             reply Maybe<String>: the Gemini
#                                       major version's digits
#            1, text (String)           reply Bool: an API version part
#            2, chunks (List<String>)   reply Maybe<Nat>: the mime's length
#                                       in chars of the data URL the chunks
#                                       make
#            3, buffer (String)         reply Maybe<(Nat, Nat)>: `0,` or
#                                       `1,start,length,` of the first event
#                                       boundary, in chars
#            4, raw (String)            reply List<String>: the lines
#
# A request tag past 4, malformed input, or input left after the request
# answers `E ai_text: malformed request`, never a default. Pure: no IO, no
# @unsafe.

import Base
import ./wire.bend as W
import ./ai_text.bend as T

# A request of the entry
type Req is Data:
  QMajor{id: String}
  QApi{text: String}
  QData{chunks: List<&2, String>}
  QBound{buffer: String}
  QLines{raw: String}

def get_strs(s: String) -> W.Dec<List<&2, String>>:
  W.get_list(~String, ~W.get_str, s)

def get_req.major(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QMajor{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.api(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QApi{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.data(r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QData{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.bound(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QBound{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.lines(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QLines{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_req.major(W.get_str(s))
        case 1n:
          get_req.api(W.get_str(s))
        case 2n:
          get_req.data(get_strs(s))
        case 3n:
          get_req.bound(W.get_str(s))
        case 4n:
          get_req.lines(W.get_str(s))
        case 5n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# The entry
# ---------

def put_mstr(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{x}:
      W.put_nat(1n, W.put_str(x, ""))

def put_mnat(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{n}:
      W.put_nat(1n, W.put_nat(n, ""))

def put_span(m: Maybe<&2, T.Span>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{p}:
      match p:
        case T.Span{i, l}:
          W.put_nat(1n, W.put_nat(i, W.put_nat(l, "")))

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QMajor{x}:
      put_mstr(T.gemini_major(x))
    case QApi{x}:
      W.put_bool(T.api_version(x), "")
    case QData{cs}:
      put_mnat(T.data_url(cs))
    case QBound{x}:
      put_span(T.event_boundary(x))
    case QLines{x}:
      W.put_list(~String, ~W.put_str, T.lines(x), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("ai_text: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("ai_text: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
