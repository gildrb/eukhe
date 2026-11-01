# ffi_aws_text: the entry of the compiled Bend core for the names and texts
# the Bedrock client reads (bend/aws_text.bend; Rust: eukhe-bend
# rules/aws_text.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  0, region (String)        reply Maybe<Nat>: the partition index
#            1, names (List<String>)   reply Maybe<Nat>: the index of the
#                                      first request-id header name
#            2, chunks (List<String>)  reply Nat: 0 valid | 1 incorrect
#                                      padding | 2 invalid (the chunks read
#                                      as one text)
#            3, host (String)          reply Maybe<String>: the endpoint's
#                                      region
#            4, id (String)            reply Maybe<String>: the ARN's region
#            5, region (String)        reply String: without its FIPS part
#
# A request tag past 5, malformed input, or input left after the request
# answers `E aws_text: malformed request`, never a default. Pure: no IO, no
# @unsafe.

import Base
import ./wire.bend as W
import ./aws_text.bend as A

# A request of the entry
type Req is Data:
  QPart{region: String}
  QRid{names: List<&2, String>}
  QB64{chunks: List<&2, String>}
  QHost{host: String}
  QArn{id: String}
  QFips{region: String}

def get_strs(s: String) -> W.Dec<List<&2, String>>:
  W.get_list(~String, ~W.get_str, s)

def get_req.part(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QPart{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.rid(r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QRid{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.b64(r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QB64{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.host(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QHost{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.arn(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QArn{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.fips(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QFips{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_req.part(W.get_str(s))
        case 1n:
          get_req.rid(get_strs(s))
        case 2n:
          get_req.b64(get_strs(s))
        case 3n:
          get_req.host(W.get_str(s))
        case 4n:
          get_req.arn(W.get_str(s))
        case 5n:
          get_req.fips(W.get_str(s))
        case 6n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# The entry
# ---------

def put_mnat(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{n}:
      W.put_nat(1n, W.put_nat(n, ""))

def put_mstr(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{x}:
      W.put_nat(1n, W.put_str(x, ""))

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QPart{r}:
      put_mnat(A.partition(r))
    case QRid{ns}:
      put_mnat(A.request_id(ns))
    case QB64{cs}:
      W.put_nat(A.base64(cs), "")
    case QHost{h}:
      put_mstr(A.endpoint(h))
    case QArn{i}:
      put_mstr(A.arn(i))
    case QFips{r}:
      W.put_str(A.without_fips(r), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("aws_text: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("aws_text: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
