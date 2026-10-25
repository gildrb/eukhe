# ffi_stream_failure: the entry of the compiled Bend core for the cause of
# a failed provider stream and the message a user reads for it
# (bend/stream_failure.bend; Rust: eukhe-bend rules/stream_failure.rs).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   cause    0 refusal | 1 safety | 2 payment_required | 3 overloaded |
#            4 rate_limit | 5 server_error | 6 auth | 7 permission |
#            8 invalid_request | 9 malformed_response | 10 stream_drop |
#            11 stream_stalled | 12 stream_repeating | 13 unknown
#   block    0 thinking | 1 text | 2 tool call | 3 none
#   request  0, type (Maybe<String>), status (Maybe<Nat>)    -> cause
#            1, cause, type, status, detail, request id      -> message (String)
#               (type, detail, request id: Maybe<String>)
#            2, message (String), status, body type, body message, code,
#               SDK class name, request id                   -> cause, type
#               (Maybe<String>), message (Maybe<String>: none keeps the raw one)
#            3, stop reason, request id (Maybe<String>)      -> cause, message
#            4, block                                        -> message
#            5, deadline in ms as the host writes it (String) -> message
#            6, a repeated line (String)                     -> the line as shown
#            7, limit, period (Nats), the shown line quoted   -> message,
#               the period recorded (Nat)
#
# Malformed input, or input left after the request, answers
# `E stream_failure: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./stream_failure.bend as Sf

# A request of the entry
type Req is Data:
  QClassify{t: Maybe<&2, String>, st: Maybe<&2, Nat>}
  QMessage{k: Sf.Cause, t: Maybe<&2, String>, st: Maybe<&2, Nat>, d: Maybe<&2, String>, r: Maybe<&2, String>}
  QHttp{m: String, st: Maybe<&2, Nat>, bt: Maybe<&2, String>, d: Maybe<&2, String>, code: Maybe<&2, String>, sdk: Maybe<&2, String>, r: Maybe<&2, String>}
  QFromStop{raw: Maybe<&2, String>, r: Maybe<&2, String>}
  QDrop{b: Sf.Block}
  QStalled{ms: String}
  QShown{line: String}
  QRepeating{limit: Nat, period: Nat, q: String}

# Maybe values and tags
# ---------------------

def get_mstr.of(r: W.Dec<String>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_mstr.tag(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_mstr.of(W.get_str(s))
        case 2n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a Maybe<String> at the start of s
def get_mstr(s: String) -> W.Dec<Maybe<&2, String>>:
  get_mstr.tag(W.get_nat(s))

def get_mnat.of(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_mnat.tag(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_mnat.of(W.get_nat(s))
        case 2n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a Maybe<Nat> at the start of s
def get_mnat(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_mnat.tag(W.get_nat(s))

def get_cause.tag(r: W.Dec<Nat>) -> W.Dec<Sf.Cause>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Sf.KRefusal{}, s}
        case 1n:
          W.Got{Sf.KSafety{}, s}
        case 2n:
          W.Got{Sf.KPayment{}, s}
        case 3n:
          W.Got{Sf.KOverloaded{}, s}
        case 4n:
          W.Got{Sf.KRateLimit{}, s}
        case 5n:
          W.Got{Sf.KServer{}, s}
        case 6n:
          W.Got{Sf.KAuth{}, s}
        case 7n:
          W.Got{Sf.KPermission{}, s}
        case 8n:
          W.Got{Sf.KInvalid{}, s}
        case 9n:
          W.Got{Sf.KMalformed{}, s}
        case 10n:
          W.Got{Sf.KDrop{}, s}
        case 11n:
          W.Got{Sf.KStalled{}, s}
        case 12n:
          W.Got{Sf.KRepeating{}, s}
        case 13n:
          W.Got{Sf.KUnknown{}, s}
        case 14n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a cause at the start of s
def get_cause(s: String) -> W.Dec<Sf.Cause>:
  get_cause.tag(W.get_nat(s))

def get_block.tag(r: W.Dec<Nat>) -> W.Dec<Sf.Block>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Sf.BThinking{}, s}
        case 1n:
          W.Got{Sf.BText{}, s}
        case 2n:
          W.Got{Sf.BToolCall{}, s}
        case 3n:
          W.Got{Sf.BNone{}, s}
        case 4n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a block at the start of s
def get_block(s: String) -> W.Dec<Sf.Block>:
  get_block.tag(W.get_nat(s))

# Requests
# --------

def get_classify.st(t: Maybe<&2, String>, dec: W.Dec<Maybe<&2, Nat>>) -> W.Dec<Req>:
  match dec:
    case W.Got{st, s}:
      W.Got{QClassify{t, st}, s}
    case W.Bad{}:
      W.Bad{}

def get_classify.t(dec: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match dec:
    case W.Got{t, s}:
      get_classify.st(t, get_mnat(s))
    case W.Bad{}:
      W.Bad{}

def get_message.r(k: Sf.Cause, t: Maybe<&2, String>, st: Maybe<&2, Nat>, d: Maybe<&2, String>, dec: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match dec:
    case W.Got{r, s}:
      W.Got{QMessage{k, t, st, d, r}, s}
    case W.Bad{}:
      W.Bad{}

def get_message.d(k: Sf.Cause, t: Maybe<&2, String>, st: Maybe<&2, Nat>, dec: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match dec:
    case W.Got{d, s}:
      get_message.r(k, t, st, d, get_mstr(s))
    case W.Bad{}:
      W.Bad{}

def get_message.st(k: Sf.Cause, t: Maybe<&2, String>, dec: W.Dec<Maybe<&2, Nat>>) -> W.Dec<Req>:
  match dec:
    case W.Got{st, s}:
      get_message.d(k, t, st, get_mstr(s))
    case W.Bad{}:
      W.Bad{}

def get_message.t(k: Sf.Cause, dec: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match dec:
    case W.Got{t, s}:
      get_message.st(k, t, get_mnat(s))
    case W.Bad{}:
      W.Bad{}

def get_message.k(dec: W.Dec<Sf.Cause>) -> W.Dec<Req>:
  match dec:
    case W.Got{k, s}:
      get_message.t(k, get_mstr(s))
    case W.Bad{}:
      W.Bad{}

def get_http.r(m: String, st: Maybe<&2, Nat>, bt: Maybe<&2, String>, d: Maybe<&2, String>, code: Maybe<&2, String>, sdk: Maybe<&2, String>, dec: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match dec:
    case W.Got{r, s}:
      W.Got{QHttp{m, st, bt, d, code, sdk, r}, s}
    case W.Bad{}:
      W.Bad{}

def get_http.sdk(m: String, st: Maybe<&2, Nat>, bt: Maybe<&2, String>, d: Maybe<&2, String>, code: Maybe<&2, String>, dec: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match dec:
    case W.Got{sdk, s}:
      get_http.r(m, st, bt, d, code, sdk, get_mstr(s))
    case W.Bad{}:
      W.Bad{}

def get_http.code(m: String, st: Maybe<&2, Nat>, bt: Maybe<&2, String>, d: Maybe<&2, String>, dec: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match dec:
    case W.Got{code, s}:
      get_http.sdk(m, st, bt, d, code, get_mstr(s))
    case W.Bad{}:
      W.Bad{}

def get_http.d(m: String, st: Maybe<&2, Nat>, bt: Maybe<&2, String>, dec: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match dec:
    case W.Got{d, s}:
      get_http.code(m, st, bt, d, get_mstr(s))
    case W.Bad{}:
      W.Bad{}

def get_http.bt(m: String, st: Maybe<&2, Nat>, dec: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match dec:
    case W.Got{bt, s}:
      get_http.d(m, st, bt, get_mstr(s))
    case W.Bad{}:
      W.Bad{}

def get_http.st(m: String, dec: W.Dec<Maybe<&2, Nat>>) -> W.Dec<Req>:
  match dec:
    case W.Got{st, s}:
      get_http.bt(m, st, get_mstr(s))
    case W.Bad{}:
      W.Bad{}

def get_http.m(dec: W.Dec<String>) -> W.Dec<Req>:
  match dec:
    case W.Got{m, s}:
      get_http.st(m, get_mnat(s))
    case W.Bad{}:
      W.Bad{}

def get_fromstop.r(raw: Maybe<&2, String>, dec: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match dec:
    case W.Got{r, s}:
      W.Got{QFromStop{raw, r}, s}
    case W.Bad{}:
      W.Bad{}

def get_fromstop.raw(dec: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match dec:
    case W.Got{raw, s}:
      get_fromstop.r(raw, get_mstr(s))
    case W.Bad{}:
      W.Bad{}

def get_drop.b(dec: W.Dec<Sf.Block>) -> W.Dec<Req>:
  match dec:
    case W.Got{b, s}:
      W.Got{QDrop{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_stalled.ms(dec: W.Dec<String>) -> W.Dec<Req>:
  match dec:
    case W.Got{ms, s}:
      W.Got{QStalled{ms}, s}
    case W.Bad{}:
      W.Bad{}

def get_shown.line(dec: W.Dec<String>) -> W.Dec<Req>:
  match dec:
    case W.Got{line, s}:
      W.Got{QShown{line}, s}
    case W.Bad{}:
      W.Bad{}

def get_repeating.q(limit: Nat, period: Nat, dec: W.Dec<String>) -> W.Dec<Req>:
  match dec:
    case W.Got{q, s}:
      W.Got{QRepeating{limit, period, q}, s}
    case W.Bad{}:
      W.Bad{}

def get_repeating.period(limit: Nat, dec: W.Dec<Nat>) -> W.Dec<Req>:
  match dec:
    case W.Got{period, s}:
      get_repeating.q(limit, period, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_repeating.limit(dec: W.Dec<Nat>) -> W.Dec<Req>:
  match dec:
    case W.Got{limit, s}:
      get_repeating.period(limit, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_classify.t(get_mstr(s))
        case 1n:
          get_message.k(get_cause(s))
        case 2n:
          get_http.m(W.get_str(s))
        case 3n:
          get_fromstop.raw(get_mstr(s))
        case 4n:
          get_drop.b(get_block(s))
        case 5n:
          get_stalled.ms(W.get_str(s))
        case 6n:
          get_shown.line(W.get_str(s))
        case 7n:
          get_repeating.limit(W.get_nat(s))
        case 8n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# The entry
# ---------

def put_mstr(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, W.put_str(x, rest))

def put_cause(c: Sf.Cause, rest: String) -> String:
  match c:
    case Sf.KRefusal{}:
      W.put_nat(0n, rest)
    case Sf.KSafety{}:
      W.put_nat(1n, rest)
    case Sf.KPayment{}:
      W.put_nat(2n, rest)
    case Sf.KOverloaded{}:
      W.put_nat(3n, rest)
    case Sf.KRateLimit{}:
      W.put_nat(4n, rest)
    case Sf.KServer{}:
      W.put_nat(5n, rest)
    case Sf.KAuth{}:
      W.put_nat(6n, rest)
    case Sf.KPermission{}:
      W.put_nat(7n, rest)
    case Sf.KInvalid{}:
      W.put_nat(8n, rest)
    case Sf.KMalformed{}:
      W.put_nat(9n, rest)
    case Sf.KDrop{}:
      W.put_nat(10n, rest)
    case Sf.KStalled{}:
      W.put_nat(11n, rest)
    case Sf.KRepeating{}:
      W.put_nat(12n, rest)
    case Sf.KUnknown{}:
      W.put_nat(13n, rest)

def put_http(h: Sf.Http) -> String:
  match h:
    case Sf.Http{k, t, m}:
      put_cause(k, put_mstr(t, put_mstr(m, "")))

def put_named(n: Sf.Named) -> String:
  match n:
    case Sf.Named{k, m}:
      put_cause(k, W.put_str(m, ""))

def put_repeat(x: Sf.Repeat) -> String:
  match x:
    case Sf.Repeat{m, p}:
      W.put_str(m, W.put_nat(p, ""))

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QClassify{t, st}:
      put_cause(Sf.classify(t, st), "")
    case QMessage{k, t, st, d, r}:
      W.put_str(Sf.message(k, t, st, d, r), "")
    case QHttp{m, st, bt, d, code, sdk, r}:
      put_http(Sf.http(m, st, bt, d, code, sdk, r))
    case QFromStop{raw, r}:
      put_named(Sf.from_stop(raw, r))
    case QDrop{b}:
      W.put_str(Sf.drop(b), "")
    case QStalled{ms}:
      W.put_str(Sf.stalled(ms), "")
    case QShown{line}:
      W.put_str(Sf.shown(line), "")
    case QRepeating{limit, period, q}:
      put_repeat(Sf.repeating(limit, period, q))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("stream_failure: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("stream_failure: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
